namespace Lean4Metaprog

open Lean (Name)

/--
A generic version of `Lean.Name` that captures everything I've learned about
names so far.
-/
class MyName (N : Type) where
  /-- Convert any name type into a `Lean.Name`. -/
  toName : N → Name

instance myname_name_inst : MyName Name := {
  toName := id
}

end Lean4Metaprog
