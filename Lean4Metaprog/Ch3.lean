import Lean

namespace Lean4Metaprog.Ch3

/-! # Chapter 3: Expressions -/

/-! ## Universe levels -/

set_option pp.universes true in
#check @List.map

/-! ## Constructing expressions -/

open Lean

def z' := Expr.const `Nat.zero []
#eval z'

def z := Expr.const ``Nat.zero []
#eval z

section resolve

open Nat

def z₁ := Expr.const `zero []
#eval z₁

-- Without `open Nat`, gives error "unknown constant 'zero'"
def z₂ := Expr.const ``zero []
#eval z₂

-- Shorter way to create constants
def z₃ := mkConst ``zero
#eval z₃

end resolve

end Lean4Metaprog.Ch3
