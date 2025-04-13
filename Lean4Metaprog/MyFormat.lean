namespace Lean4Metaprog

/--
A generic version of `Std.Format` that captures everything I've learned about
formatting data so far.
-/
class MyFormat (F : Type) where
  -- No properties yet

instance myformat_format_inst : MyFormat Std.Format := {}

end Lean4Metaprog
