import Lean4Metaprog.MyExpr

namespace Lean4Metaprog

open Lean (MetaM MVarId)
open Lean.Meta (mkFreshExprMVar)

/-- The parts of the `Lean.MetaM` interface that I've used so far. -/
class MyMetaM (M : Type → Type) where
  /-- The type of unique identifiers for metavariables. -/
  MVarId : Type

  /-- Create a new, unique metavariable with the given type. -/
  mkFreshMVar {E : Type} [MyExpr E] (type : E) : M MVarId

instance mymetam_metam_inst : MyMetaM MetaM := {
  MVarId := MVarId
  mkFreshMVar := λ type => do
    let exprMVar ← mkFreshExprMVar (.some (MyExpr.toExpr type))
    return exprMVar.mvarId!
}

end Lean4Metaprog
