import Lean
import Lean4Metaprog.MyExpr
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

def metavariableExample {E : Type} [E : MyExpr E] : Lean.MetaM Unit := do
  let natTy := E.const ``Nat
  -- Create two fresh metavariables of type `Nat`.
  let mvid1 ← MyMetaM.mkFreshMVar natTy
  let mvid2 ← MyMetaM.mkFreshMVar natTy

  /-
  Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  creates a function type.
  -/
  let mvid3 ← MyMetaM.mkFreshMVar (E.mkArrow natTy natTy)

  let mvar1 := E.mvar mvid1
  let mvar2 := E.mvar mvid2
  let mvar3 := E.mvar mvid3

  -- Define a helper function that prints each metavariable.
  let printMVars : Lean.MetaM Unit := do
    IO.println s!"  meta1: {← MyMetaM.instantiateMVars mvar1}"
    IO.println s!"  meta2: {← MyMetaM.instantiateMVars mvar2}"
    IO.println s!"  meta3: {← MyMetaM.instantiateMVars mvar3}"

  IO.println "Metavariable assignment example"
  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  MyMetaM.assign mvid1 (E.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  MyMetaM.assign mvid2 (E.const ``Nat.zero)
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  MyMetaM.assign mvid3 (E.const ``Nat.succ)
  IO.println "After assigning mvar3:"
  printMVars

#eval metavariableExample (E := Lean.Expr)

end Lean4Metaprog.Ch4
