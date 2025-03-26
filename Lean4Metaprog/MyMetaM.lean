import Lean4Metaprog.MyExpr
import Lean4Metaprog.MyMVarId

namespace Lean4Metaprog

/-- The parts of the `Lean.MetaM` interface that I've used so far. -/
class MyMetaM (M : Type → Type) extends Monad M where
  /-- The type of unique identifiers for metavariables. -/
  MVarId : Type

  /-- `MVarId` satisfies the properties of a metavariable ID. -/
  myMVarId : MyMVarId MVarId

  /-- The type of expressions returned from operations. -/
  ExprOut : Type

  /-- `ExprOut` satisfies the properties of an expression type. -/
  myExprOut : MyExpr ExprOut

  /-- Create a new, unique metavariable with the given type. -/
  mkFreshMVar {E : Type} [MyExpr E] (type : E) : M MVarId

  /--
  Return the given expression with all metavariables assigned in the current
  context replaced with their values.
  -/
  instantiateMVars {E : Type} [MyExpr E] (expr : E) : M ExprOut

  /-- Unsafely fill in the value of a metavariable (no validity checks). -/
  assign {E : Type} [MyExpr E] (mvar : MVarId) (val : E) : M Unit

instance mymetam_metam_inst : MyMetaM Lean.MetaM := {
  MVarId := Lean.MVarId
  myMVarId := inferInstance
  ExprOut := Lean.Expr
  myExprOut := inferInstance
  mkFreshMVar := λ type => do
    let exprMVar ← Lean.Meta.mkFreshExprMVar (MyExpr.toExpr type)
    return exprMVar.mvarId!
  instantiateMVars := Lean.instantiateMVars ∘ MyExpr.toExpr
  assign := λ mvarId => mvarId.assign ∘ MyExpr.toExpr
}

namespace MyMetaM

variable {M : Type → Type} [MyMetaM M]

instance mymvarid_mymetam_mvarid_inst : MyMVarId (MyMetaM.MVarId M) :=
  MyMetaM.myMVarId

instance myexpr_mymetam_exprout_inst : MyExpr (MyMetaM.ExprOut M) :=
  MyMetaM.myExprOut

end Lean4Metaprog.MyMetaM
