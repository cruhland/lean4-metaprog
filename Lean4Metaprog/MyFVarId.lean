import Lean

namespace Lean4Metaprog

/--
A generic version of `Lean.FVarId` that captures everything I've learned about
free variable identifiers so far.
-/
class MyFVarId (F : Type) where
  /-- Convert any free variable identifier to a `Lean.FVarId`. -/
  toFVarId : F → Lean.FVarId

instance myfvarid_fvarid_inst : MyFVarId Lean.FVarId := {
  toFVarId := id
}

end Lean4Metaprog
