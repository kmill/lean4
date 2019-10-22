import Init.Lean.Trace
open Lean

structure MyState :=
(traceState : TraceState := {})
(s          : Nat := 0)

abbrev M := ReaderT Options (EState String MyState)

/- We can enable tracing for a monad M by adding an instance of `SimpleMonadTracerAdapter M` -/
instance : SimpleMonadTracerAdapter M :=
{ getOptions       := read,
  getTraceState    := MyState.traceState <$> get,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

def tst1 : M Unit :=
do trace `module (fun _ => ("hello" ++ MessageData.nest 9 (Format.line ++ "world" : MessageData)));
   trace `module (fun _ => ("another message" : MessageData));
   pure ()

def tst2 (b : Bool) : M Unit :=
traceCtx `module $ fun _ => do
  tst1;
  when b $ throw "error";
  tst1;
  pure ()

def tst3 (b : Bool) : M Unit :=
traceCtx `module $ fun _ => do
  tst2 b;
  tst1

def displayTrace (s : MyState) : IO Unit :=
s.traceState.traces.mfor $ fun m => IO.println (format m)

def runM (x : M Unit) : IO Unit :=
let opts := Options.empty;
let opts := opts.setBool `trace.module true;
match x.run opts {} with
| EState.Result.ok _ s    => displayTrace s
| EState.Result.error _ s => do IO.println "Error"; displayTrace s

def main : IO Unit :=
do IO.println "----";
   runM (tst3 true);
   IO.println "----";
   runM (tst3 false)

#eval main
