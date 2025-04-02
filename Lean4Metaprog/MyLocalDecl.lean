import Lean

namespace Lean4Metaprog

/--
A generic version of `Lean.LocalDecl` that captures everything I've learned
about local variable declarations so far.
-/
class MyLocalDecl (L : Type) where
  /-- Whether this local declaration should be hidden from users. -/
  isImplDetail (ldecl : L) : Bool

instance mylocaldecl_localdecl_inst : MyLocalDecl Lean.LocalDecl := {
  isImplDetail := Lean.LocalDecl.isImplementationDetail
}

end Lean4Metaprog
