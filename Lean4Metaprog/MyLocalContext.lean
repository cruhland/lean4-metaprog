import Lean4Metaprog.MyLocalDecl

namespace Lean4Metaprog

/--
A generic version of `Lean.LocalContext` that captures everything I've learned
about local variable contexts so far.
-/
class MyLocalContext (C : Type) where
  /-- The type of declarations in this local context. -/
  LocalDeclOut : Type

  /-- Local declarations satisfy all properties expected of them. -/
  myLocalDeclOut : MyLocalDecl LocalDeclOut

  /-- Effectful iteration over the declarations in this local context. -/
  declIter {M : Type → Type} [Monad M] : ForIn M C LocalDeclOut

instance mylocalcontext_localcontext_inst
    : MyLocalContext Lean.LocalContext
    := {
  LocalDeclOut := Lean.LocalDecl
  myLocalDeclOut := inferInstance
  declIter := inferInstance
}

namespace MyLocalContext

variable {C : Type} [MyLocalContext C]

instance mylocaldecl_localdeclout_inst : MyLocalDecl (LocalDeclOut C) :=
  myLocalDeclOut

instance mylocalcontext_forIn_inst
    {M : Type → Type} [Monad M] : ForIn M C (LocalDeclOut C)
    :=
  declIter

end Lean4Metaprog.MyLocalContext
