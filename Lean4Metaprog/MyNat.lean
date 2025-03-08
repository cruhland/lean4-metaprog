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

end Lean4Metaprog
