import Lean4Metaprog.MyExpr

namespace Lean4Metaprog

/--
A generic version of `Lean.LocalDecl` that captures everything I've learned
about local variable declarations so far.
-/
class MyLocalDecl (L : Type) where
  /-- The type of expressions returned from operations. -/
  ExprOut : Type

  /-- The expression type has all properties required of expressions. -/
  myExprOut : MyExpr ExprOut

  /-- Whether this local declaration should be hidden from users. -/
  isImplDetail (ldecl : L) : Bool

  /-- The local variable's type. -/
  type (ldecl : L) : ExprOut

  /-- The expression that references the given local variable. -/
  asExpr (ldecl : L) : ExprOut

instance mylocaldecl_localdecl_inst : MyLocalDecl Lean.LocalDecl := {
  ExprOut := Lean.Expr
  myExprOut := inferInstance
  isImplDetail := Lean.LocalDecl.isImplementationDetail
  type := Lean.LocalDecl.type
  asExpr := Lean.LocalDecl.toExpr
}

namespace MyLocalDecl

variable {L : Type} [MyLocalDecl L]

instance mylocaldecl_myexprout_inst : MyExpr (ExprOut L) := myExprOut

end Lean4Metaprog.MyLocalDecl
