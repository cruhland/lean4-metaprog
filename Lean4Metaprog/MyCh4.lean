import Lean
import Lean4Metaprog.MyMetaM

/-! # Metavariables -/

namespace Lean4Metaprog.Ch4

-- Create a new metavariable
#check Lean.Meta.mkFreshExprMVar
#check MyMetaM.mkFreshMVar

-- Create a new metavariable in a specified local context
#check Lean.Meta.mkFreshExprMVarAt
-- MyMetaM equivalent not needed yet

-- Assign an expression to a metavariable (unsafely)
#check Lean.MVarId.assign
-- MyMetaM equivalents not needed yet

-- Retrieve information about a metavariable
#check Lean.MVarId.getDecl -- throws exception (in the monad) if not found
#check Lean.MVarId.findDecl? -- returns Option
#check Lean.MVarId.getType -- only get the type (throws exception)
-- MyMetaM equivalents not needed yet

-- Retrieve or check metavariable assignment; rarely used
#check Lean.getExprMVarAssignment?
#check Lean.MVarId.isAssigned
-- MyMetaM equivalents not needed yet

-- Replaces all assigned metavariables in expression with their assignments
#check Lean.instantiateMVars
-- MyMetaM equivalents not needed yet

#eval show Lean.MetaM Unit from do
  let natTy := Lean.Expr.const ``Nat []
  -- Create two fresh metavariables of type `Nat`.
  let mvar1 ← Lean.Meta.mkFreshExprMVar natTy (userName := `mvar1)
  let mvar2 ← Lean.Meta.mkFreshExprMVar natTy (userName := `mvar2)

  /-
  Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  creates a function type.
  -/
  let natFn ← Lean.mkArrow natTy natTy
  let mvar3 ← Lean.Meta.mkFreshExprMVar natFn (userName := `mvar3)

  -- Define a helper function that prints each metavariable.
  let printMVars : Lean.MetaM Unit := do
    IO.println s!"  meta1: {← Lean.instantiateMVars mvar1}"
    IO.println s!"  meta2: {← Lean.instantiateMVars mvar2}"
    IO.println s!"  meta3: {← Lean.instantiateMVars mvar3}"

  IO.println "Metavariable assignment example"
  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  mvar3.mvarId!.assign (.const ``Nat.succ [])
  IO.println "After assigning mvar3:"
  printMVars

end Lean4Metaprog.Ch4
