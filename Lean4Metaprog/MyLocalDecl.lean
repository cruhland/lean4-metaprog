import Lean4Metaprog.MyExpr

namespace Lean4Metaprog

/--
A generic version of `Lean.LocalDecl` that captures everything I've learned
about local variable declarations so far.
-/
class MyLocalDecl (D : Type) where
  /-- The type of expressions returned from operations. -/
  ExprOut : Type

  /-- The expression type has all properties required of expressions. -/
  myExprOut : MyExpr ExprOut

  /-- Whether this local declaration should be hidden from users. -/
  isImplDetail (ldecl : D) : Bool

  /-- The local variable's type. -/
  type (ldecl : D) : ExprOut

  /-- The expression that references the given local variable. -/
  asExpr (ldecl : D) : ExprOut

instance mylocaldecl_localdecl_inst : MyLocalDecl Lean.LocalDecl := {
  ExprOut := Lean.Expr
  myExprOut := inferInstance
  isImplDetail := Lean.LocalDecl.isImplementationDetail
  type := Lean.LocalDecl.type
  asExpr := Lean.LocalDecl.toExpr
}

namespace MyLocalDecl

variable {D : Type} [MyLocalDecl D]

instance mylocaldecl_myexprout_inst : MyExpr (ExprOut D) := myExprOut

end Lean4Metaprog.MyLocalDecl
