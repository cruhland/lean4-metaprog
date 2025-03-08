import Lean4Metaprog.MyExpr

namespace Lean4Metaprog.MyCh3

open Lean

/-! # Chapter 3: Expressions - using My* definitions -/

/-! ## Universe levels -/

set_option pp.universes true in
#check @List.map

/-! ## Constructing expressions -/

/-! ### Constants -/

def z' : Expr := MyExpr.const `Nat.zero
#eval z'

def z : Expr := MyExpr.const ``Nat.zero
#eval z

section resolve

def z₁ : Expr := MyExpr.const `zero
#eval z₁

-- Comment this out and observe that ``zero has an error
open Nat

def z₂ : Expr := MyExpr.const ``zero
#eval z₂

end resolve

end Lean4Metaprog.MyCh3
