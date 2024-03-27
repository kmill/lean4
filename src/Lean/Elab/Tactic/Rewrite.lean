/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic
open Meta

def rewriteTarget (tryCloseFinal : Bool) (stx : Syntax) (symm : Bool) (config : Rewrite.Config := {}) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).rewrite (← getMainTarget) e symm (config := config)
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    if tryCloseFinal then
      discard <| observing? <| Term.runTactic mvarId' (← `(tactic| with_reducible first | exact True.intro | rfl))
    replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDecl (tryCloseFinal : Bool) (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config := {}) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    (← getMainGoal).rewrite localDecl.type e symm (config := config)
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceResult.mvarId.withContext do
    if tryCloseFinal then
      let ty := (← replaceResult.fvarId.getType).consumeMData
      if ty.isFalse then
        replaceResult.mvarId.assign (← mkFalseElim (← replaceResult.mvarId.getType) (mkFVar fvarId))
        return
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

def withRWRulesSeq (tryClose : Bool) (token : Syntax) (rwRulesSeqStx : Syntax) (x : (tryClose : Bool) → (symm : Bool) → (term : Syntax) → TacticM Unit) : TacticM Unit := do
  let lbrak := rwRulesSeqStx[0]
  let rules := rwRulesSeqStx[1].getArgs
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
  let numRules := (rules.size + 1) / 2
  for i in [:numRules] do
    let rule := rules[i * 2]!
    let sep  := rules.getD (i * 2 + 1) Syntax.missing
    let tryCloseFinal := tryClose && i == numRules
    -- show rule state up to (incl.) next `,`
    withTacticInfoContext (mkNullNode #[rule, sep]) do
      -- show errors on rule
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        let processId (id : Syntax) : TacticM Unit := do
          -- See if we can interpret `id` as a hypothesis first.
          if (← optional <| getFVarId id).isSome then
            x tryCloseFinal symm term
          else
            -- Try to get equation theorems for `id`.
            let declName ← try realizeGlobalConstNoOverload id catch _ => return (← x tryCloseFinal symm term)
            let some eqThms ← getEqnsFor? declName (nonRec := true) | x tryCloseFinal symm term
            let rec go : List Name →  TacticM Unit
              | [] => throwError "failed to rewrite using equation theorems for '{declName}'"
              -- Remark: we prefix `eqThm` with `_root_` to ensure it is resolved correctly.
              -- See test: `rwPrioritizesLCtxOverEnv.lean`
              | eqThm::eqThms => (x tryCloseFinal symm (mkIdentFrom id (`_root_ ++ eqThm))) <|> go eqThms
            go eqThms.toList
            discard <| Term.addTermInfo id (← mkConstWithFreshMVarLevels declName) (lctx? := ← getLCtx)
        match term with
        | `($id:ident)  => processId id
        | `(@$id:ident) => processId id
        | _ => x tryCloseFinal symm term


declare_config_elab elabRewriteConfig Rewrite.Config

def evalRewrite (tryClose : Bool) : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq tryClose stx[0] stx[2] fun tryCloseFinal symm term => do
    withLocation loc
      (rewriteLocalDecl tryCloseFinal term symm · cfg)
      (rewriteTarget tryCloseFinal term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

@[builtin_tactic Lean.Parser.Tactic.rewriteSeq] def evalRewriteSeq : Tactic := evalRewrite (tryClose := false)

@[builtin_tactic Lean.Parser.Tactic.rwSeq] def evalRwSeq : Tactic := evalRewrite (tryClose := true)

end Lean.Elab.Tactic
