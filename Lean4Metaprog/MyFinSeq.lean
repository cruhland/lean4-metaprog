namespace Lean4Metaprog

/-- Characterizes types that behave like finite sequences. -/
class MyFinSeq (S : Type → Type) where
  /-- Consume the sequence elements from smaller indices to larger. -/
  foldl {A X : Type} (next : X → A → X) (init : X) : S A → X

instance myfinseq_array_inst : MyFinSeq Array := {
  foldl := Array.foldl
}

end Lean4Metaprog
