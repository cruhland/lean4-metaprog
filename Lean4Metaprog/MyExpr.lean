import Lean4Metaprog.MyFinSeq
import Lean4Metaprog.MyLevel
import Lean4Metaprog.MyName

open Lean (BinderInfo Expr Level Name mkConst)

namespace Lean4Metaprog

/--
A generic version of `Lean.Expr` that captures everything I've learned about
expressions so far.
-/
class MyExpr (L N : outParam Type) [MyLevel L] [MyName N] (E : Type) where
  /-- Call a function on a single argument. -/
  app (f : E) (arg : E) : E

  /-- Refer to a name defined elsewhere. -/
  const (name : N) : E

  /-- An anonymous function of a single typed argument. -/
  lam (var_name : N) (var_type : E) (body : E) : E

  /-- A universe level. -/
  sort (level : L) : E

instance myexpr_expr_inst : MyExpr Level Name Expr := {
  app := .app
  const := mkConst
  lam := (.lam · · · BinderInfo.default)
  sort := .sort
}

variable {L N E : Type} [MyLevel L] [MyName N] [MyExpr L N E]

namespace MyExpr

/-- Function application on many arguments. -/
def appN {S : Type → Type} [MyFinSeq S] (f : E) (args : S E) : E :=
  MyFinSeq.foldl app f args

end MyExpr

end Lean4Metaprog
