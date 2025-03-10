import Lean4Metaprog.MyFinSeq
import Lean4Metaprog.MyLevel
import Lean4Metaprog.MyName
import Lean4Metaprog.MyNat

open Lean (BinderInfo Expr Level Name mkConst mkNatLit)

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

  /-- Refer to a previously-defined expression by name. -/
  const (name : N) : E

  /-- An anonymous function of a single typed argument. -/
  lam (var_name : N) (var_type body : E) : E

  /-- A natural number literal, e.g. `42`. -/
  natLit (n : ℕ) : E

  /-- A universe level. -/
  sort (level : L) : E

instance myexpr_expr_inst : MyExpr Level Name Nat Expr := {
  app := .app
  bvar := .bvar
  const := mkConst
  lam := (.lam · · · BinderInfo.default)
  natLit := mkNatLit
  sort := .sort
}

variable {L N ℕ E : Type} [MyLevel L] [MyName N] [MyNat ℕ] [MyExpr L N ℕ E]

namespace MyExpr

/-- Function application on many arguments. -/
def appN {S : Type → Type} [MyFinSeq S] (f : E) (args : S E) : E :=
  MyFinSeq.foldl app f args

end MyExpr

end Lean4Metaprog
