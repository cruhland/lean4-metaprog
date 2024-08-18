import Lake
open Lake DSL

package "lean4-metaprog" where
  -- add package configuration options here

lean_lib «Lean4Metaprog» where
  -- add library configuration options here

@[default_target]
lean_exe "lean4-metaprog" where
  root := `Main
