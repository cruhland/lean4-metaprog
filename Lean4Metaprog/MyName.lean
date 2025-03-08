namespace Lean4Metaprog

open Lean (Name)

/--
A generic version of `Lean.Name` that captures everything I've learned about
names so far.
-/
class MyName (N : Type) where
  -- No properties yet

instance myname_name_inst : MyName Name := {}

end Lean4Metaprog
