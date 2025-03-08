import Lean4Metaprog.MyLevel
import Lean4Metaprog.MyName

open Lean (Expr Level Name mkConst)

namespace Lean4Metaprog

/--
A generic version of `Lean.Expr` that captures everything I've learned about
expressions so far.
-/
class MyExpr (L N : outParam Type) [MyLevel L] [MyName N] (E : Type) where
  /-- Call a function on a single argument. -/
  _app : E → E → E

  /-- Refer to a name defined elsewhere. -/
  _const : N → E

  /-- A universe level. -/
  _sort : L → E

instance myexpr_expr_inst : MyExpr Level Name Expr := {
  _app := .app
  _const := mkConst
  _sort := .sort
}

variable {L N E : Type} [MyLevel L] [MyName N] [MyExpr L N E]

namespace MyExpr

/-- Convenience function for creating function applications. -/
def app : E → E → E := MyExpr._app

/-- Convenience function for creating named constant expressions. -/
def const : N → E := MyExpr._const

end MyExpr

end Lean4Metaprog
