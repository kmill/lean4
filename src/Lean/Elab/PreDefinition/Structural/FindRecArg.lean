/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.Structural
open Meta

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat := Id.run do
  let mut minPos := xs.size
  for index in indices do
    match xs.indexOf? index with
    | some pos => if pos.val < minPos then minPos := pos.val
    | _        => pure ()
  return minPos

-- Indices can only depend on other indices
private def hasBadIndexDep? (ys : Array Expr) (indices : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for index in indices do
    let indexType ← inferType index
    for y in ys do
      if !indices.contains y && (← dependsOn indexType y.fvarId!) then
        return some (index, y)
  return none

-- Inductive datatype parameters cannot depend on ys
private def hasBadParamDep? (ys : Array Expr) (indParams : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for p in indParams do
    for y in ys do
      if ← dependsOn p y.fvarId! then
        return some (p, y)
  return none

/--
Assemble the `RecArgInfo` for the `i`th parameter in the parameter list `xs`. This performs
various sanity checks on the argument (is it even an inductive type etc).
-/
def getRecArgInfo (fnName : Name) (numFixed : Nat) (xs : Array Expr) (i : Nat) : MetaM RecArgInfo := do
  if h : i < xs.size then
    if i < numFixed then
      throwError "it is unchanged in the recursive calls"
    let x := xs[i]
    let localDecl ← getFVarLocalDecl x
    if localDecl.isLet then
      throwError "it is a let-binding"
    let xType ← whnfD localDecl.type
    matchConstInduct xType.getAppFn (fun _ => throwError "its type is not an inductive") fun indInfo us => do
    if !(← hasConst (mkBRecOnName indInfo.name)) then
      throwError "its type {indInfo.name} does not have a recursor"
    else if indInfo.isReflexive && !(← hasConst (mkBInductionOnName indInfo.name)) && !(← isInductivePredicate indInfo.name) then
      throwError "its type {indInfo.name} is a reflexive inductive, but {mkBInductionOnName indInfo.name} does not exist and it is not an inductive predicate"
    else
      let indArgs    : Array Expr := xType.getAppArgs
      let indParams  : Array Expr := indArgs[0:indInfo.numParams]
      let indIndices : Array Expr := indArgs[indInfo.numParams:]
      if !indIndices.all Expr.isFVar then
        throwError "its type {indInfo.name} is an inductive family and indices are not variables{indentExpr xType}"
      else if !indIndices.allDiff then
        throwError " its type {indInfo.name} is an inductive family and indices are not pairwise distinct{indentExpr xType}"
      else
        let indexMinPos := getIndexMinPos xs indIndices
        let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed
        let ys          := xs[numFixed:]
        match (← hasBadIndexDep? ys indIndices) with
        | some (index, y) =>
          throwError "its type {indInfo.name} is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}"
        | none =>
          match (← hasBadParamDep? ys indParams) with
          | some (indParam, y) =>
            throwError "its type is an inductive datatype{indentExpr xType}\nand the datatype parameter{indentExpr indParam}\ndepends on the function parameter{indentExpr y}\nwhich does not come before the varying parameters and before the indices of the recursion parameter."
          | none =>
            let indicesPos := indIndices.map fun index => match xs.indexOf? index with | some i => i.val | none => unreachable!
            return { fnName      := fnName
                     numFixed    := numFixed
                     recArgPos   := i
                     indicesPos  := indicesPos
                     indName     := indInfo.name
                     indLevels   := us
                     indParams   := indParams
                     indAll      := indInfo.all.toArray }
    else
      throwError "the index #{i+1} exceeds {xs.size}, the number of parameters"

/--
  Runs `k` on all argument indices, until it succeeds.
  We use this argument to justify termination using the auxiliary `brecOn` construction.

  We give preference for arguments that are *not* indices of inductive types of other arguments.
  See issue #837 for an example where we can show termination using the index of an inductive family, but
  we don't get the desired definitional equalities.

  `value` is the function value (including fixed parameters)
-/
partial def tryAllArgs (value : Expr) (k : Nat → M α) : M α := do
  -- It's improtant to keep the call to `k` outside the scope of `lambdaTelescope`:
  -- The tactics in the IndPred construction search the full local context, so we must not have
  -- extra FVars there
  let (indices, nonIndices) ← lambdaTelescope value fun xs _ => do
    let indicesRef : IO.Ref (Array Nat) ← IO.mkRef {}
    for x in xs do
      let xType ← inferType x
      /- Traverse all sub-expressions in the type of `x` -/
      forEachExpr xType fun e =>
        /- If `e` is an inductive family, we store in `indicesRef` all variables in `xs` that occur in "index positions". -/
        matchConstInduct e.getAppFn (fun _ => pure ()) fun info _ => do
          if info.numIndices > 0 && info.numParams + info.numIndices == e.getAppNumArgs then
            for arg in e.getAppArgs[info.numParams:] do
              forEachExpr arg fun e => do
                if let .some idx := xs.getIdx? e then
                  indicesRef.modify (·.push idx)
    let indices ← indicesRef.get
    let nonIndices := (Array.range xs.size).filter (fun i => !(indices.contains i))
    return (indices, nonIndices)

  let mut errors : Array MessageData := Array.mkArray (indices.size  + nonIndices.size) m!""
  let saveState ← get -- backtrack the state for each argument
  for i in id (nonIndices ++ indices) do
    trace[Elab.definition.structural] "findRecArg i: {i}"
    try
      set saveState
      return (← k i)
    catch e => errors := errors.set! i e.toMessageData
  throwError
    errors.foldl
      (init := m!"structural recursion cannot be used:")
      (f := (· ++ Format.line ++ Format.line ++ .))

end Lean.Elab.Structural
