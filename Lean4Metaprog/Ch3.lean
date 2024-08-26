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

def one := Expr.app (mkConst ``Nat.succ) z
#eval one

def natExpr : Nat → Expr
| 0 => z
| n + 1 => .app (mkConst ``Nat.succ) (natExpr n)
#eval natExpr 3

def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]
#eval sumExpr 2 3

def constZero : Expr :=
  .lam `x (mkConst ``Nat) (mkConst ``Nat.zero) BinderInfo.default
#eval constZero

def nat : Expr := mkConst ``Nat

def addOne : Expr :=
  .lam `x nat
    (mkAppN (mkConst ``Nat.add) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelOne, levelOne])
    #[nat, nat, addOne, .app (.const ``List.nil [levelOne]) nat]

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil

#reduce mapAddOneNil

/-! ## Exercises -/

def addConst : Expr := mkConst ``Nat.add

def ex_01 : Expr := .app (.app addConst (mkNatLit 1)) (mkNatLit 2)
#eval ex_01

def mkAdd (e₁ e₂ : Expr) : Expr := mkAppN addConst #[e₁, e₂]

def ex_02 : Expr := mkAdd (mkNatLit 1) (mkNatLit 2)
#eval ex_02

def mkLam (binderName : Name) (binderType body : Expr) : Expr :=
  .lam binderName binderType body .default

def ex_03 : Expr := mkLam `x nat (mkAdd (mkNatLit 1) (.bvar 0))
#eval ex_03

def mulConst : Expr := mkConst ``Nat.mul
def mkMul (e₁ e₂ : Expr) : Expr := mkAppN mulConst #[e₁, e₂]

def ex_04 : Expr :=
  mkLam `a nat
    (mkLam `b nat
      (mkLam `c nat
        (mkAdd (mkMul (.bvar 1) (.bvar 2)) (.bvar 0))))
#eval ex_04

end Lean4Metaprog.Ch3
