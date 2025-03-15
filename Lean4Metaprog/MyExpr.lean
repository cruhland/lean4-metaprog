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
class MyExpr
    (L N ℕ : outParam Type) [MyLevel L] [MyName N] [MyNat ℕ] (E : Type)
    where
  /-- Call a function on a single argument. -/
  app (fn arg : E) : E

  /-- Refer to a bound variable using its deBruijn index. -/
  bvar (index : ℕ) : E

  /--
  Refer to a previously-defined expression by name, at the provided universe
  levels.
  -/
  constL {S : Type → Type} [MyFinSeq S] (name : N) (levels : S L) : E

  /-- An anonymous function of a single typed argument. -/
  lam (var_name : N) (var_type body : E) : E

  /-- A natural number literal, e.g. `42`. -/
  natLit (n : ℕ) : E

  /-- A universe level. -/
  sort (level : L) : E

  /-- A string literal, e.g. `"hello"`. -/
  strLit {S : Type} [MyString S] (s : S) : E

instance myexpr_expr_inst : MyExpr Level Name Nat Expr := {
  app := .app
  bvar := .bvar
  constL := λ name levels => .const name (MyFinSeq.toList levels)
  lam := (.lam · · · BinderInfo.default)
  natLit := mkNatLit
  sort := .sort
  strLit := λ str => mkStrLit (MyString.toString str)
}

variable {L N ℕ E : Type} [MyLevel L] [MyName N] [MyNat ℕ] [MyExpr L N ℕ E]

namespace MyExpr

/-- Function application on many arguments. -/
def appN {S : Type → Type} [MyFinSeq S] (f : E) (args : S E) : E :=
  MyFinSeq.foldl app f args

/-- Refer to a previously-defined expression by name. -/
def const (name : N) : E := constL name []

end MyExpr

end Lean4Metaprog
