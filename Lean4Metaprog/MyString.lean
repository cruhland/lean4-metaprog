namespace Lean4Metaprog

/--
A generic version of `Lean.String` that captures everything I've learned about
strings so far.
-/
class MyString (S : Type) where
  /-- Convert any string type into a `Lean.String`. -/
  toString : S → String

instance mystring_string_inst : MyString String := {
  toString := id
}

end Lean4Metaprog
