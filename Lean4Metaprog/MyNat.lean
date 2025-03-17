namespace Lean4Metaprog

/--
A generic version of `Lean.Nat` that captures everything I've learned about
natural numbers so far.
-/
class MyNat (ℕ : Type) where
  /-- The smallest natural number. -/
  zero : ℕ

  /-- Produces the next largest natural number after the given value. -/
  step : ℕ → ℕ

  /--
  Convert a natural number to a value of another type, via recursion on the
  `zero` and `step` constructors.

  The name is an abbreviation of "eliminator", which is a common term in type
  theory for this kind of function.
  -/
  elim {X : Type} (elimZero : X) (elimStep : X → X) : ℕ → X

  /-- Convert any natural number type into a `Lean.Nat`. -/
  toNat : ℕ → Nat := elim Nat.zero Nat.succ

instance mynat_nat_inst : MyNat Nat := {
  zero := Nat.zero
  step := Nat.succ
  elim := λ elimZero elimStep => Nat.rec elimZero (λ _ => elimStep)
  toNat := id
}

variable {ℕ : Type} [MyNat ℕ]

/-- Support natural number literals for all `MyNat` types, for convenience. -/
instance ofnat_mynat_inst {n : Nat} : OfNat ℕ n := {
  ofNat := Nat.rec (zero := MyNat.zero) (succ := λ _ => MyNat.step) n
}

end Lean4Metaprog
