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

end Lean4Metaprog.Ch9
