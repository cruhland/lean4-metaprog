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

/-! ### "Getting" and "setting" the list of goals -/

elab "reverse_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals : List Lean.MVarId ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals goals.reverse

theorem test_reverse_goals : (1 = 1 ∧ 2 = 2) ∧ 3 = 3 := by
  constructor
  constructor
  -- goals: `1 = 1`, `2 = 2`, `3 = 3`
  reverse_goals
  -- goals: `3 = 3`, `2 = 2`, `1 = 1`
  all_goals trivial

/-! ## Exercises -/

open Lean (Expr mkAppN mkArrow)
open Lean.Elab.Tactic
open Lean.Meta (mkFreshExprMVar)

-- Exercise 1
elab "step_1" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let .app (.app (.const ``Iff _) a) b := goalType
    | throwError "Goal type is not of the form `a ↔ b`"

  let mvarId1 ← mkFreshExprMVar (← mkArrow a b) (userName := `red)
  let mvarId2 ← mkFreshExprMVar (← mkArrow b a) (userName := `blue)

  mvarId.assign (mkAppN (.const ``Iff.intro []) #[a, b, mvarId1, mvarId2])
  modify λ _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!]}

elab "step_2" : tactic => do
  -- Get goals and extract type information
  let [mvarFwd, mvarRev] ← getGoals | throwError "expected two goals"
  let fwdType := (← mvarFwd.getDecl).type
  let .forallE _ pq qp _ := fwdType
    | throwError "first goal must be of the form `a → b`"
  let .app (.app (.const ``And _) p) q := pq
    | throwError "hypothesis of first goal must be `p ∧ q`"

  -- Construct and assign expression for first goal, with new metavariable
  mvarFwd.withContext do
    let (_, mvarFwd') ← mvarFwd.intro `hFwd
    modify λ _ => { goals := [mvarFwd'] }

  -- Construct and assign expression for second goal
  let revHyp := .bvar 0
  let rightApp := mkAppN (.const ``And.right []) #[q, p, revHyp]
  let leftApp := mkAppN (.const ``And.left []) #[q, p, revHyp]
  let andApp := mkAppN (.const ``And.intro []) #[p, q, rightApp, leftApp]
  let revExpr := .lam `hRev qp andApp .default
  mvarRev.assign revExpr

elab "step_3" : tactic => do
  withMainContext do
    let mvarId ← getMainGoal
    let goalType ← getMainTarget
    let .app (.app (.const ``And _) q) p := goalType
      | throwError "goal must be of the form `q ∧ p`"

    let mvarIdL ← mkFreshExprMVar q
    let mvarIdR ← mkFreshExprMVar p
    let andExpr := mkAppN (.const ``And.intro []) #[q, p, mvarIdL, mvarIdR]
    mvarId.assign andExpr

    modify λ _ => { goals := [mvarIdL.mvarId!, mvarIdR.mvarId!] }

elab "step_4" : tactic => do
  let [mvarL, mvarR] ← getGoals | throwError "expected two goals"

  mvarL.withContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let some ldecl := lctx.findFromUserName? `hFwd | throwError "hyp not found"
    let .app (.app (.const ``And _) p) q := ldecl.type | throwError "wrong type"
    let hyp := ldecl.toExpr
    let exprL := mkAppN (.const ``And.right []) #[p, q, hyp]
    mvarL.assign exprL

  mvarR.withContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let some ldecl := lctx.findFromUserName? `hFwd | throwError "hyp not found"
    let .app (.app (.const ``And _) p) q := ldecl.type | throwError "wrong type"
    let hyp := ldecl.toExpr
    let exprR := mkAppN (.const ``And.left []) #[p, q, hyp]
    mvarR.assign exprR

theorem gradual (p q : Prop) : p ∧ q ↔ q ∧ p := by
  step_1
  step_2
  step_3
  step_4

end Lean4Metaprog.Ch9
