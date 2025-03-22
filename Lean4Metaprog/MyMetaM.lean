import Lean4Metaprog.MyExpr
import Lean4Metaprog.MyMVarId

namespace Lean4Metaprog

/-- The parts of the `Lean.MetaM` interface that I've used so far. -/
class MyMetaM (M : Type → Type) extends Monad M where
  /-- The type of unique identifiers for metavariables. -/
  MVarId : Type

  /-- `MVarId` satisfies the properties of a metavariable ID. -/
  myMVarId : MyMVarId MVarId

  /-- Create a new, unique metavariable with the given type. -/
  mkFreshMVar {E : Type} [MyExpr E] (type : E) : M MVarId

  /-- Create a new, unique name based on the given user-friendly name. -/
  mkFreshUserName {N : Type} [MyName N] (name : N) : M Lean.Name

instance mymetam_metam_inst : MyMetaM Lean.MetaM := {
  MVarId := Lean.MVarId
  myMVarId := inferInstance
  mkFreshMVar := λ type => do
    let exprMVar ← Lean.Meta.mkFreshExprMVar (MyExpr.toExpr type)
    return exprMVar.mvarId!
  mkFreshUserName := λ name => Lean.Core.mkFreshUserName (MyName.toName name)
}

namespace MyMetaM

variable {M : Type → Type} [MyMetaM M]

instance mymvarid_mymetam_mvarid_inst : MyMVarId (MyMetaM.MVarId M) :=
  MyMetaM.myMVarId

/--
Creates an expression for a non-dependent function type, i.e.
`argType → bodyType`.
-/
def mkArrow {E : Type} [MyExpr E] (argType bodyType : E) : M E :=
  return MyExpr.forallE (← mkFreshUserName `x) argType bodyType

end Lean4Metaprog.MyMetaM
