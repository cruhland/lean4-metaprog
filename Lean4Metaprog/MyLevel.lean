import Lean

open Lean (Level)

namespace Lean4Metaprog

/--
A generic version of `Lean.Level` that captures everything I've learned about
levels so far.
-/
class MyLevel (L : Type) where
  /-- The lowest level. -/
  zero : L

  /-- The next level above the given one. -/
  succ : L → L

  /-- Convert any level type into a `Lean.Level`. -/
  toLevel : L → Level

instance mylevel_level_inst : MyLevel Level := {
  zero := .zero
  succ := .succ
  toLevel := id
}

variable {L : Type} [MyLevel L]

/-- Support natural number literals for all `MyLevel` types, for convenience. -/
instance ofnat_mylevel_inst {n : Nat} : OfNat L n := {
  ofNat := Nat.rec (zero := MyLevel.zero) (succ := λ _ => MyLevel.succ) n
}

end Lean4Metaprog
