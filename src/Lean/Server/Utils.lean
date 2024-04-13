/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
prelude
import Init.System.Uri
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.Diagnostics
import Lean.Data.Lsp.Extra
import Lean.Data.Lsp.TextSync
import Lean.Server.InfoUtils

namespace IO

/-- Throws an `IO.userError`. -/
def throwServerError (err : String) : IO α :=
  throw (userError err)

namespace FS.Stream

/--
Chains two streams by creating a new stream s.t. writing to it
just writes to `a` but reading from it also duplicates the read output
into `b`, c.f. `a | tee b` on Unix.
NB: if `a` is written to but this stream is never read from,
the output will *not* be duplicated. Use this if you only care
about the data that was actually read.
-/
def chainRight (a : Stream) (b : Stream) (flushEagerly : Bool := false) : Stream :=
  { a with
    flush := a.flush *> b.flush
    read := fun sz => do
      let bs ← a.read sz
      b.write bs
      if flushEagerly then b.flush
      pure bs
    getLine := do
      let ln ← a.getLine
      b.putStr ln
      if flushEagerly then b.flush
      pure ln }

/-- Like `tee a | b` on Unix. See `chainOut`. -/
def chainLeft (a : Stream) (b : Stream) (flushEagerly : Bool := false) : Stream :=
  { b with
    flush := a.flush *> b.flush
    write := fun bs => do
      a.write bs
      if flushEagerly then a.flush
      b.write bs
    putStr := fun s => do
      a.putStr s
      if flushEagerly then a.flush
      b.putStr s }

/-- Prefixes all written outputs with `pre`. -/
def withPrefix (a : Stream) (pre : String) : Stream :=
  { a with
    write := fun bs => do
      a.putStr pre
      a.write bs
    putStr := fun s =>
      a.putStr (pre ++ s) }

end FS.Stream
end IO

namespace Lean.Server

/-- Meta-Data of a document. -/
structure DocumentMeta where
  /-- URI where the document is located. -/
  uri                 : Lsp.DocumentUri
  /-- Version number of the document. Incremented whenever the document is edited. -/
  version             : Nat
  /-- Current text of the document. -/
  text                : FileMap
  /--
  Controls when dependencies of the document are built on `textDocument/didOpen` notifications.
  -/
  dependencyBuildMode : Lsp.DependencyBuildMode
  deriving Inhabited

/-- Extracts an `InputContext` from `doc`. -/
def DocumentMeta.mkInputContext (doc : DocumentMeta) : Parser.InputContext where
  input    := doc.text.source
  fileName := (System.Uri.fileUriToPath? doc.uri).getD doc.uri |>.toString
  fileMap  := doc.text

/--
Replaces the range `r` (using LSP UTF-16 positions) in `text` (using UTF-8 positions)
with `newText`.
-/
def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
  let start := text.lspPosToUtf8Pos r.start
  let «end» := text.lspPosToUtf8Pos r.«end»
  let pre := text.source.extract 0 start
  let post := text.source.extract «end» text.source.endPos
  (pre ++ newText.crlfToLf ++ post).toFileMap

open IO

/--
Duplicates an I/O stream to a log file `fName` in LEAN_SERVER_LOG_DIR
if that envvar is set.
-/
def maybeTee (fName : String) (isOut : Bool) (h : FS.Stream) : IO FS.Stream := do
  match (← IO.getEnv "LEAN_SERVER_LOG_DIR") with
  | none => pure h
  | some logDir =>
    IO.FS.createDirAll logDir
    let hTee ← FS.Handle.mk (System.mkFilePath [logDir, fName]) FS.Mode.write
    let hTee := FS.Stream.ofHandle hTee
    pure $ if isOut then
      hTee.chainLeft h true
    else
      h.chainRight hTee true

open Lsp

/-- Returns the document contents with the change applied. -/
def applyDocumentChange (oldText : FileMap) : (change : Lsp.TextDocumentContentChangeEvent) → FileMap
  | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) =>
    replaceLspRange oldText range newText
  | TextDocumentContentChangeEvent.fullChange (newText : String) =>
    newText.crlfToLf.toFileMap

/-- Returns the document contents with all changes applied. -/
def foldDocumentChanges (changes : Array Lsp.TextDocumentContentChangeEvent) (oldText : FileMap) : FileMap :=
  changes.foldl applyDocumentChange oldText

/-- Constructs a `textDocument/publishDiagnostics` notification. -/
def mkPublishDiagnosticsNotification (m : DocumentMeta) (diagnostics : Array Lsp.Diagnostic) :
    JsonRpc.Notification Lsp.PublishDiagnosticsParams where
  method := "textDocument/publishDiagnostics"
  param  := {
    uri         := m.uri
    version?    := some m.version
    diagnostics := diagnostics
  }

/-- Constructs a `$/lean/fileProgress` notification. -/
def mkFileProgressNotification (m : DocumentMeta) (processing : Array LeanFileProgressProcessingInfo) :
    JsonRpc.Notification Lsp.LeanFileProgressParams where
  method := "$/lean/fileProgress"
  param := {
    textDocument := { uri := m.uri, version? := m.version }
    processing
  }

/-- Constructs a `$/lean/fileProgress` notification from the given position onwards. -/
def mkFileProgressAtPosNotification (m : DocumentMeta) (pos : String.Pos)
  (kind : LeanFileProgressKind := LeanFileProgressKind.processing) :
    JsonRpc.Notification Lsp.LeanFileProgressParams :=
  mkFileProgressNotification m #[{ range := ⟨m.text.utf8PosToLspPos pos, m.text.utf8PosToLspPos m.text.source.endPos⟩, kind := kind }]

/-- Constructs a `$/lean/fileProgress` notification marking processing as done. -/
def mkFileProgressDoneNotification (m : DocumentMeta) : JsonRpc.Notification Lsp.LeanFileProgressParams :=
  mkFileProgressNotification m #[]

-- TODO: should return a request ID (or task?) when we add response handling
def mkApplyWorkspaceEditRequest (params : ApplyWorkspaceEditParams) :
    JsonRpc.Request ApplyWorkspaceEditParams :=
  ⟨"workspace/applyEdit", "workspace/applyEdit", params⟩

end Lean.Server

/--
Converts an UTF-8-based `String.range` in `text` to an equivalent LSP UTF-16-based `Lsp.Range`
in `text`.
-/
def String.Range.toLspRange (text : Lean.FileMap) (r : String.Range) : Lean.Lsp.Range :=
  ⟨text.utf8PosToLspPos r.start, text.utf8PosToLspPos r.stop⟩

open Lean in
/--
Attempts to find a module name in the roots denoted by `srcSearchPath` for `uri`.
Fails if `uri` is not a `file://` uri or if the given `uri` cannot be found in `srcSearchPath`.
-/
def System.SearchPath.searchModuleNameOfUri
    (srcSearchPath : SearchPath)
    (uri           : Lsp.DocumentUri)
    : IO (Option Name) := do
  let some path := Uri.fileUriToPath? uri
    | return none
  searchModuleNameOfFileName path srcSearchPath
