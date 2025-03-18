import Lean4Metaprog.MyFinSeq
import Lean4Metaprog.MyLevel
import Lean4Metaprog.MyName
import Lean4Metaprog.MyNat
import Lean4Metaprog.MyString

namespace Lean4Metaprog

open Lean (BinderInfo Expr Level Name mkConst mkNatLit mkStrLit)

/--
A generic version of `Lean.Expr` that captures everything I've learned about
expressions so far.
-/
class MyExpr (E : Type) where
  /-- Call a function on a single argument. -/
  app (fn arg : E) : E

  /-- Refer to a bound variable using its deBruijn index. -/
  bvar {ℕ : Type} [MyNat ℕ] (index : ℕ) : E

  /--
  Refer to a previously-defined expression by name, at the provided universe
  levels.
  -/
  constL
    {L N : Type} {S : Type → Type} [MyLevel L] [MyName N] [MyFinSeq S]
    (name : N) (levels : S L) : E

  /-- The type of a dependent function: `(varName : varType) → bodyType`. -/
  forallE {N : Type} [MyName N] (varName : N) (varType bodyType : E) : E

  /--
  An anonymous function of a single, typed argument:
  `λ (varName : varType) => body`.
  -/
  lam {N : Type} [MyName N] (varName : N) (varType body : E) : E

  /-- A natural number literal, e.g. `42`. -/
  natLit {ℕ : Type} [MyNat ℕ] (n : ℕ) : E

  /-- A universe level. -/
  sort {L : Type} [MyLevel L] (level : L) : E

  /-- A string literal, e.g. `"hello"`. -/
  strLit {S : Type} [MyString S] (s : S) : E

  /-- Convert any expression type to a `Lean.Expr`. -/
  toExpr : E → Expr

instance myexpr_expr_inst : MyExpr Expr := {
  app := .app
  bvar := .bvar ∘ MyNat.toNat
  constL := λ name levels =>
    let lean_levels := (MyFinSeq.toList levels).map MyLevel.toLevel
    Expr.const (MyName.toName name) lean_levels
  forallE := λ name => (.forallE (MyName.toName name) · · BinderInfo.default)
  lam := λ name => (.lam (MyName.toName name) · · BinderInfo.default)
  natLit := mkNatLit ∘ MyNat.toNat
  sort := .sort ∘ MyLevel.toLevel
  strLit := mkStrLit ∘ MyString.toString
  toExpr := id
}

variable {E : Type} [MyExpr E]

namespace MyExpr

/-- Function application on many arguments. -/
def appN {S : Type → Type} [MyFinSeq S] (f : E) (args : S E) : E :=
  MyFinSeq.foldl app f args

/-- Refer to a previously-defined expression by name. -/
def const {N : Type} [MyName N] (name : N) : E := constL name ([] : List Level)

end Lean4Metaprog.MyExpr
