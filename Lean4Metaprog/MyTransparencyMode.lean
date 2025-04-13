
namespace Lean4Metaprog

/--
A generic version of `Lean.Meta.TransparencyMode` that captures everything I've
learned about the transparency mode so far.
-/
class MyTransparencyMode (T : Type) where
  /-- All definitions reduce. -/
  all : T

  /-- All definitions lacking the `irreducible` attribute reduce. -/
  default : T

  /-- Only definitions with the `reducible` or `instance` attributes reduce. -/
  instances : T

  /-- Only definitions with the `reducible` attribute reduce. -/
  reducible : T

  /-- Convert any transparency mode type to Lean's standard version. -/
  toTransparencyMode : T → Lean.Meta.TransparencyMode

instance mytransmode_transmode_inst
    : MyTransparencyMode Lean.Meta.TransparencyMode
    := {
  all := .all
  default := .default
  instances := .instances
  reducible := .reducible
  toTransparencyMode := id
}

end Lean4Metaprog
