import Lean4Metaprog.MyExpr
import Lean4Metaprog.MyMVarId

namespace Lean4Metaprog

/-- The parts of the `Lean.MetaM` interface that I've used so far. -/
class MyMetaM (M : Type → Type) where
  /-- The type of unique identifiers for metavariables. -/
  MVarId : Type

  /-- `MVarId` satisfies the properties of a metavariable ID. -/
  myMVarId : MyMVarId MVarId

  /-- Create a new, unique metavariable with the given type. -/
  mkFreshMVar {E : Type} [MyExpr E] (type : E) : M MVarId

instance mymetam_metam_inst : MyMetaM Lean.MetaM := {
  MVarId := Lean.MVarId
  myMVarId := inferInstance
  mkFreshMVar := λ type => do
    let exprMVar ← Lean.Meta.mkFreshExprMVar (MyExpr.toExpr type)
    return exprMVar.mvarId!
}

instance mymvarid_mymetam_mvarid_inst
    {M : Type → Type} [MyMetaM M] : MyMVarId (MyMetaM.MVarId M)
    :=
  MyMetaM.myMVarId

end Lean4Metaprog
