import Lean

namespace Lean4Metaprog

/-- The parts of the `Lean.MVarId` interface that I've used so far. -/
class MyMVarId (M : Type) where
  /-- Convert any metavariable identifier to a `Lean.MVarId`. -/
  toMVarId : M → Lean.MVarId

instance mymvarid_mvarid_inst : MyMVarId Lean.MVarId := {
  toMVarId := id
}

end Lean4Metaprog
