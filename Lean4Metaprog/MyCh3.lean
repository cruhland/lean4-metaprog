import Lean4Metaprog.MyExpr
import Lean4Metaprog.MyNat

namespace Lean4Metaprog.MyCh3

open Lean

/-! # Chapter 3: Expressions - using My* definitions -/

/-! ## Universe levels -/

set_option pp.universes true in
#check @List.map

/-! ## Constructing expressions -/

variable {L E : Type} [MyLevel L] [MyExpr L Name E]

/-! ### Constants -/

def z' : Expr := MyExpr.const `Nat.zero
#eval z'

def zE : E := MyExpr.const ``Nat.zero
def z : Expr := zE
#eval z

section resolve

def z₁ : Expr := MyExpr.const `zero
#eval z₁

-- Comment this out and observe that ``zero has an error
open Nat

def z₂ : Expr := MyExpr.const ``zero
#eval z₂

end resolve

/-! ### Function applications -/

open MyExpr (app const)

def oneE : E := MyExpr.app (const ``Nat.succ) zE
def one : Expr := oneE
#eval one

def natExpr {ℕ : Type} [MyNat ℕ] : ℕ → E :=
  let elimZero := zE
  let elimStep := λ nExpr => app (const ``Nat.succ) nExpr
  MyNat.elim elimZero elimStep

end Lean4Metaprog.MyCh3
