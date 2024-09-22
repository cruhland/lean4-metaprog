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

def someNumber : Nat := (· + 2) $ 3
#eval mkConst ``someNumber
#eval reduce (mkConst ``someNumber)
#reduce someNumber

def traceWithTransparency
    (e : Expr) (md : TransparencyMode) : MetaM Format
    := do
  ppExpr (← withTransparency md $ reduce e)

@[irreducible] def irreducibleDef : Nat := 1
def defaultDef : Nat := irreducibleDef + 1
abbrev reducibleDef : Nat := defaultDef + 1
abbrev reduceWithTransparency := traceWithTransparency (mkConst ``reducibleDef)

#eval reduceWithTransparency .reducible

set_option pp.explicit true in
#eval reduceWithTransparency .reducible

#eval reduceWithTransparency .instances

#eval reduceWithTransparency .default

#eval reduceWithTransparency .all

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

#eval whnf' `(List.cons 1 [])
#eval whnf' `(List.cons (1 + 1) [])
#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
#eval whnf' `(λ x : Nat => x)
#eval whnf' `(∀ x, x > 0)
#eval whnf' `(Type 3)
#eval whnf' `((15 : Nat))

#eval whnf' `(List.append [1])
#eval whnf' `((λ x y : Nat => x + y) 1)
#eval whnf' `(let x : Nat := 1; x)

def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | .app (.app (.const ``And _) P) Q => return some (P, Q)
  | _ => return none

def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ← whnf e with
  | .app (.app (.const ``And _) P) e' =>
    match ← whnf e' with
    | .app (.app (.const ``And _) Q) R => return some (P, Q, R)
    | _ => return none
  | _ =>
    return none

def appendAppend (xs ys : List α) := (xs.append ys).append xs

set_option pp.all true in
set_option pp.explicit true in
#print appendAppend

def appendAppendRhsExpr₁ (u : Level) (α xs ys : Expr) : Expr :=
  mkAppN
    (.const ``List.append [u])
    #[α, mkAppN (.const ``List.append [u]) #[α, xs, ys], xs]

def appendAppendRhsExpr₂ (xs ys : Expr) : MetaM Expr := do
  mkAppM ``List.append #[← mkAppM ``List.append #[xs, ys], xs]

def revOrd : Ord Nat where
  compare x y := compare y x

def ordExpr : MetaM Expr := do
  mkAppOptM ``compare #[none, Expr.const ``revOrd [], mkNatLit 0, mkNatLit 1]

#eval format <$> ordExpr

def doubleExpr₁ : Expr :=
  .lam `x constNat (mkAppN (mkConst ``Nat.add) #[.bvar 0, .bvar 0]) .default

#eval ppExpr doubleExpr₁

def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x .default constNat λ x => do
    let body ← mkAppM ``Nat.add #[x, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)

def somePropExpr : MetaM Expr := do
  let funcType ← mkArrow constNat constNat
  withLocalDecl `f .default funcType λ f => do
    let feqn ← withLocalDecl `n .default constNat λ n => do
      let lhs := .app f n
      let rhs := .app f (← mkAppM ``Nat.succ #[n])
      let eqn ← mkEq lhs rhs
      mkForallFVars #[n] eqn
    mkLambdaFVars #[f] feqn

elab "someProp" : term => somePropExpr

#check someProp
#reduce (types := true) someProp Nat.succ

/-! ### Deconstructing expressions -/

/--
Attempt to apply `e` to `goal`, and generate a list of new goals on success.
-/
def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  goal.checkNotAssigned `myApply
  goal.withContext do
    let goalType ← goal.getType
    let exprType ← inferType e
    -- When `exprType` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce
    -- new metavariables for the `xᵢ` in `exprArgs` and instantiate them in the
    -- conclusion `U`, given by `exprBodyType`. When `exprType` does not have
    -- that form, `exprArgs` is empty and `exprType = exprBodyType`.
    let (exprArgs, _, exprBodyType) ← forallMetaTelescopeReducing exprType
    if ! (← isDefEq goalType exprBodyType) then
      let msg := m!"{e} is not applicable to goal with target {goalType}"
      throwTacticEx `myApply goal msg
    goal.assign (mkAppN e exprArgs)
    -- `isDefEq` may have assigned some of `exprArgs`.
    -- Report the rest as new goals.
    let newGoals ← exprArgs.filterMapM λ mvar => do
      let mvarId := mvar.mvarId!
      let isAssigned := (← mvarId.isAssigned) || (← mvarId.isDelayedAssigned)
      return if isAssigned then none else some mvarId
    return newGoals.toList

elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a

/-! ## Backtracking -/

def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s

/-! ## Exercises -/

/-! ### Ex 1 -/
#eval show MetaM Unit from do
  let mvarNat ← mkFreshExprMVar constNat (userName := `mvarNat)
  mvarNat.mvarId!.assign (mkNatLit 3)
  IO.println s!"{← instantiateMVars mvarNat}"
  let mvarNatType ← mvarNat.mvarId!.getType
  IO.println s!"{mvarNatType}"

  let mvarString ← mkFreshExprMVar (mkConst ``String) (userName := `mvarString)
  mvarString.mvarId!.assign (mkNatLit 3)
  IO.println s!"{← instantiateMVars mvarString}"
  let mvarStringType ← mvarString.mvarId!.getType
  IO.println s!"{mvarStringType}"

/-! ### Ex 2 -/
-- My answer: either `1 + 2` or
-- `.app (.app (.const ``Nat.add) (.lit (.natVal 1))) (.lit (.natVal 2))`

#eval show MetaM Expr from
  instantiateMVars
    (Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2])

-- Ah, looks like I forgot all the typeclass stuff for `OfNat`
-- Other than that it's pretty close
