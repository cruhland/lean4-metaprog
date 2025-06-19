import Lean
import Lean.Elab.Tactic

namespace Lean4Metaprog.Ch9

/-! # Tactics -/

#print Lean.Elab.Tactic.TacticM
#check Lean.Elab.Tactic.Context
#check Lean.Elab.Tactic.State
#print Lean.Elab.Term.TermElabM

/-! ## Tactics by macro expansion -/

macro "custom_sorry_macro" : tactic => `(tactic| sorry)

-- example : 1 = 42 := by custom_sorry_macro

/-! ### Implementing `trivial`: extensible tactics by macro expansion -/

syntax "custom_tactic" : tactic

macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)

example : 42 = 42 := by custom_tactic

#check_failure (by custom_tactic : 43 = 43 ∧ 42 = 42)

macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

example : 43 = 43 ∧ 42 = 42 := by custom_tactic

/-! ### Implementing `<;>`: tactic combinators by macro expansion -/

syntax tactic " and_then " tactic : tactic

macro_rules
| `(tactic| $a:tactic and_then $b:tactic) => `(tactic| $a; all_goals $b:tactic)

theorem test_and_then : 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl

#print test_and_then

/-! ## Exploring `TacticM` -/

/-! ### The simplest tactic: `sorry` -/

elab "custom_sorry_0" : tactic => do
  return

#check Lean.Elab.Tactic.withMainContext
#check Lean.Elab.Tactic.getMainGoal

elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

/-
theorem test_custom_sorry : 1 = 2 := by
  custom_sorry_2

#print test_custom_sorry
-/

/-! ### The `custom_assump` tactic: accessing hypotheses -/

elab "custom_assump_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    dbg_trace f!"goal type: {goalType}"

elab "list_local_decls_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM λ decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declName := decl.userName
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

elab "list_local_decls_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM λ decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declName := decl.userName
      let declType ← Lean.Meta.inferType declExpr
      dbg_trace
        f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"

elab "list_local_decls_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM λ decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declName := decl.userName
      let declType ← Lean.Meta.inferType declExpr
      let eq? ← Lean.Meta.isExprDefEq declType goalType
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {declName}"

elab "custom_assump_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? λ decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if (← Lean.Meta.isExprDefEq declType goalType)
      then return some declExpr
      else return none
    dbg_trace f!"matching_expr: {option_matching_expr}"

elab "custom_assump_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let eqExprOpt ← ctx.findDeclM? λ decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if ← Lean.Meta.isExprDefEq declType goalType
      then return some declExpr
      else return none
    match eqExprOpt with
    | some e =>
      Lean.Elab.Tactic.closeMainGoal `custom_assump_2 e
    | none =>
      let msg := m!"unable to find matching hypothesis of type ({goalType})"
      Lean.Meta.throwTacticEx `custom_assump_2 goal msg

theorem assump_correct (_ : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_2

/-
theorem assump_wrong (H1 : 1 = 1) : 2 = 2 := by
  custom_assump_2 -- tactic 'custom_assump_2' failed,
                  -- unable to find matching hypothesis of type (2 = 2)
-/

/-! ### Tweaking the context -/

#check Lean.Elab.Tactic.liftMetaTactic
#check Lean.MVarId.define
#check Lean.MVarId.assert

open Lean.Elab.Tactic in
elab "custom_let" n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic λ mvarId => do
      let mvarId' ← mvarId.define n.getId t v
      let (_, mvarId') ← mvarId'.intro1P
      return [mvarId']

open Lean.Elab.Tactic in
elab "custom_have" n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic λ mvarId => do
      let mvarId' ← mvarId.assert n.getId t v
      let (_, mvarId') ← mvarId'.intro1P
      return [mvarId']

theorem test_let_have : True := by
  custom_let n : Nat := 5
  custom_have h : n = n := rfl
  exact True.intro

end Lean4Metaprog.Ch9
