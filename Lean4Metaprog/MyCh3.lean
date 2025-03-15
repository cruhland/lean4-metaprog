import Lean4Metaprog.MyExpr

namespace Lean4Metaprog.MyCh3

open Lean
open MyExpr (app appN bvar const constL lam natLit sort)

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

def sumExpr {ℕ : Type} [MyNat ℕ] (n m : ℕ) : E :=
  appN (const ``Nat.add) #[natExpr n, natExpr m]

/-! ### Lambda abstractions -/

def constZeroE : E := lam `x (const ``Nat) (const ``Nat.zero)
def constZero : Expr := constZeroE
#eval constZero

def natE : E := const ``Nat
def ℓ₀ : L := MyLevel.zero

def addOneE : E := lam `x natE (appN (const ``Nat.add) #[bvar 0, natLit 1])

def mapAddOneNilE : E :=
  let listMapE := constL ``List.map [ℓ₀, ℓ₀]
  let nilE := constL ``List.nil [ℓ₀]
  appN listMapE #[natE, natE, addOneE, app nilE natE]

elab "mapAddOneNil" : term => return mapAddOneNilE

#check mapAddOneNil

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil

#reduce mapAddOneNil

/-! ## Exercises -/

def addE : E := const ``Nat.add

def ex_01 : E := app (app addE (natLit 1)) (natLit 2)
#eval (ex_01 : Expr)
elab "ex_01_term" : term => return ex_01
#check ex_01_term

def ex_02 : E := appN addE #[natLit 1, natLit 2]
#eval (ex_02 : Expr)
elab "ex_02_term" : term => return ex_02
#check ex_02_term

def ex_03 : E := lam `x natE (appN addE #[natLit 1, bvar 0])
#eval (ex_03 : Expr)
elab "ex_03_term" : term => return ex_03
#check ex_03_term

def ex_04 : E :=
  let a := bvar 2; let b := bvar 1; let c := bvar 0
  let body := appN addE #[appN (const ``Nat.mul) #[b, a], c]
  lam `a natE (lam `b natE (lam `c natE body))
#eval (ex_04 : Expr)
elab "ex_04_term" : term => return ex_04
#check ex_04_term

def ex_05 : E := lam `x natE (lam `y natE (appN addE #[bvar 1, bvar 0]))
#eval (ex_05 : Expr)
elab "ex_05_term" : term => return ex_05
#check ex_05_term

end Lean4Metaprog.MyCh3
