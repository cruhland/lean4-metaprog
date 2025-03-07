import Lean

open Lean (Level)

namespace Lean4Metaprog

/--
A generic version of `Lean.Level` that captures everything I've learned about
levels so far.
-/
class MyLevel (L : Type) where
  zero : L
  succ : L → L

instance mylevel_level_inst : MyLevel Level := {
  zero := .zero
  succ := .succ
}

end Lean4Metaprog
