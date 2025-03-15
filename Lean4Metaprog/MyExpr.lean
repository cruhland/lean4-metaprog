import Lean4Metaprog.MyFinSeq
import Lean4Metaprog.MyLevel
import Lean4Metaprog.MyName
import Lean4Metaprog.MyNat
import Lean4Metaprog.MyString

open Lean (BinderInfo Expr Level Name mkConst mkNatLit mkStrLit)

namespace Lean4Metaprog

/--
A generic version of `Lean.Expr` that captures everything I've learned about
expressions so far.
-/
class MyExpr (L ℕ : outParam Type) [MyLevel L] [MyNat ℕ] (E : Type) where
  /-- Call a function on a single argument. -/
  app (fn arg : E) : E

  /-- Refer to a bound variable using its deBruijn index. -/
  bvar (index : ℕ) : E

  /--
  Refer to a previously-defined expression by name, at the provided universe
  levels.
  -/
  constL
    {N : Type} {S : Type → Type} [MyName N] [MyFinSeq S]
    (name : N) (levels : S L) : E

  /-- The type of a dependent function: `(varName : varType) → bodyType`. -/
  forallE {N : Type} [MyName N] (varName : N) (varType bodyType : E) : E

  /--
  An anonymous function of a single, typed argument:
  `λ (varName : varType) => body`.
  -/
  lam {N : Type} [MyName N] (varName : N) (varType body : E) : E

  /-- A natural number literal, e.g. `42`. -/
  natLit (n : ℕ) : E

  /-- A universe level. -/
  sort (level : L) : E

  /-- A string literal, e.g. `"hello"`. -/
  strLit {S : Type} [MyString S] (s : S) : E

instance myexpr_expr_inst : MyExpr Level Nat Expr := {
  app := .app
  bvar := .bvar
  constL :=
    λ name levels => Expr.const (MyName.toName name) (MyFinSeq.toList levels)
  forallE := λ name => (.forallE (MyName.toName name) · · BinderInfo.default)
  lam := λ name => (.lam (MyName.toName name) · · BinderInfo.default)
  natLit := mkNatLit
  sort := .sort
  strLit := λ str => mkStrLit (MyString.toString str)
}

variable {L ℕ E : Type} [MyLevel L] [MyNat ℕ] [MyExpr L ℕ E]

namespace MyExpr

/-- Function application on many arguments. -/
def appN {S : Type → Type} [MyFinSeq S] (f : E) (args : S E) : E :=
  MyFinSeq.foldl app f args

/-- Refer to a previously-defined expression by name. -/
def const {N : Type} [MyName N] (name : N) : E := constL name []

end MyExpr

end Lean4Metaprog
