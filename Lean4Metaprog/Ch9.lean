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

end Lean4Metaprog.Ch9
