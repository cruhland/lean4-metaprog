import Lean

open Lean hiding mkConst
open Lean.Expr
open Lean.Meta

/-! # Metavariables -/

def mkConst (name : Name) (levels : List Level := []) : Expr :=
  .const name levels
def constNat : Expr := mkConst ``Nat

#eval show MetaM Unit from do
  -- Create two fresh metavariables of type `Nat`.
  let mvar₁ ← mkFreshExprMVar constNat (userName := `mvar1)
  let mvar₂ ← mkFreshExprMVar constNat (userName := `mvar2)
  -- Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  -- creates a function type.
  let mvar₃ ←
    mkFreshExprMVar (← mkArrow constNat constNat) (userName := `mvar3)

  -- Define a helper function that prints each metavariable.
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar₁}"
    IO.println s!"  meta2: {← instantiateMVars mvar₂}"
    IO.println s!"  meta3: {← instantiateMVars mvar₃}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar₁.mvarId!.assign (.app mvar₃ mvar₂)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  mvar₂.mvarId!.assign (mkConst ``Nat.zero)
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  mvar₃.mvarId!.assign (mkConst ``Nat.succ)
  IO.println "After assigning mvar3:"
  printMVars

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  -- Pass the current tactic name as argument for a better error message
  mvarId.checkNotAssigned `myAssumption
  mvarId.withContext do
    let goalType ← mvarId.getType
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      if ← isDefEq ldecl.type goalType then
        -- Prove the goal
        mvarId.assign ldecl.toExpr
        return true
    return false
