namespace Lean4Metaprog

/-- Characterizes types that behave like finite sequences. -/
class MyFinSeq (S : Type → Type) where
  /-- The sequence containing no elements. -/
  empty {A : Type} : S A

  /-- Consume sequence elements from smaller indices to larger. -/
  foldl {A X : Type} (next : X → A → X) (init : X) : S A → X

  /-- Consume sequence elements from larger indices to smaller. -/
  foldr {A X : Type} (next : A → X → X) (init : X) : S A → X

  /-- Convert a finite sequence into a `List`. -/
  toList {A : Type} : S A → List A := foldr List.cons List.nil

namespace MyFinSeq

instance myfinseq_array_inst : MyFinSeq Array := {
  empty := Array.empty
  foldl := Array.foldl
  foldr := Array.foldr
  toList := Array.toList
}

instance myfinseq_list_inst : MyFinSeq List := {
  empty := List.nil
  foldl := List.foldl
  foldr := List.foldr
  toList := id
}

end Lean4Metaprog.MyFinSeq
