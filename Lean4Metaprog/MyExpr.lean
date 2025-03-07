import Lean4Metaprog.MyLevel

open Lean (Expr Level)

namespace Lean4Metaprog

/--
A generic version of `Lean.Expr` that captures everything I've learned about
expressions so far.
-/
class MyExpr (L : outParam Type) [MyLevel L] (E : Type) where
  sort : L → E

instance myexpr_expr_inst : MyExpr Level Expr := {
  sort := .sort
}

end Lean4Metaprog
