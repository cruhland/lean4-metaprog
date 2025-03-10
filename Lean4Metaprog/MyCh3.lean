import Lean4Metaprog.MyExpr

namespace Lean4Metaprog.MyCh3

open Lean
open MyExpr (app appN bvar const lam natLit sort)

/-! # Chapter 3: Expressions - using My* definitions -/

/-! ## Universe levels -/

set_option pp.universes true in
#check @List.map

/-! ## Constructing expressions -/

variable {L ℕ E : Type} [MyLevel L] [MyNat ℕ] [MyExpr L Name ℕ E]

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

def oneE : E := MyExpr.app (const ``Nat.succ) zE
def one : Expr := oneE
#eval one

def natExpr {ℕ : Type} [MyNat ℕ] : ℕ → E :=
  MyNat.elim (elimZero := zE) (elimStep := app (const ``Nat.succ))

def sumExpr {ℕ : Type} [MyNat ℕ] (n m : ℕ) : Expr :=
  appN (const ``Nat.add) #[natExpr n, natExpr m]

/-! ### Lambda abstractions -/

def constZeroE : E := lam `x (const ``Nat) (const ``Nat.zero)
def constZero : Expr := constZeroE
#eval constZero

def natE : E := const ``Nat
def lZeroE : E := sort MyLevel.zero

def addOneE : E := lam `x natE (appN (const ``Nat.add) #[bvar 0, natLit 1])

end Lean4Metaprog.MyCh3
