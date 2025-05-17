import Lean
import Lean4Metaprog.MyExpr
import Lean4Metaprog.MyLocalDecl
import Lean4Metaprog.MyMetaM

namespace Lean4Metaprog.Ch4

open MyExpr (const)

/-! ## Metavariables -/

/-! ### Basic operations -/

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

def metavariableExample
    {E : Type} {M : Type → Type} [E : MyExpr E] [MyMetaM M] [MonadLiftT IO M]
    : M Unit
    := do
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
  let printMVars : M Unit := do
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

#eval metavariableExample (E := Lean.Expr) (M := Lean.MetaM)

/-! ### Local contexts -/

-- Get the "ambient" local context.
#check Lean.getLCtx

-- Run a `MetaM` program with a given metavariable's context
#check Lean.MVarId.withContext

-- Get all information about a local hypothesis declaration
#check Lean.FVarId.getDecl -- fails the monad if not found

-- Get the most recent local declaration with the given human-readable name
#check Lean.Meta.getLocalDeclFromUserName  -- fails the monad if not found

-- Iteration over all declarations in the local context
#check
  (inferInstanceAs (ForIn Lean.MetaM Lean.LocalContext Lean.LocalDecl)).forIn

-- Declarations that can be ignored
#check Lean.LocalDecl.isImplementationDetail

-- Fails the `MetaM` monad if the metavariable argument is already assigned
#check Lean.MVarId.checkNotAssigned

-- Are two expressions definitionally equal (reduce to the same normal form)?
#check Lean.Meta.isDefEq

-- Creates the `Lean.Expr` for a local hypothesis
#check Lean.LocalDecl.toExpr

def myAssumption
    {mvid : Type} {M : Type → Type} [MyMVarId mvid] [MyMetaM M]
    (mvarId : mvid) : M Bool
    := do
  MyMetaM.failIfAssigned mvarId `myAssumption
  MyMetaM.withLocalCtxOf mvarId do
    let target ← MyMetaM.mvarType mvarId

    for ldecl in ← MyMetaM.localCtx do
      if MyLocalDecl.isImplDetail ldecl then continue

      if ← MyMetaM.isDefEq (MyLocalDecl.type ldecl) target then
        -- Prove the goal
        MyMetaM.assign mvarId (MyLocalDecl.asExpr ldecl)
        return true
    return false

/-! ### Delayed assignments -/

/-! ### Metavariable depth -/

#check Lean.Meta.withNewMCtxDepth

/-! ## Computation -/

/-! ### Full normalization -/

#check Lean.Meta.reduce

def someNumber : Nat := (· + 2) $ 3

def someNumberE {E : Type} [MyExpr E] : E := const ``someNumber
#eval (someNumberE : Lean.Expr)

def reduceNumberE
    {E : Type} {M : Type → Type} [MyExpr E] [MyMetaM M]
    : M (MyMetaM.ExprOut M)
    :=
  MyMetaM.reduce (someNumberE : E)

#eval reduceNumberE (M := Lean.MetaM) (E := Lean.Expr)
#reduce someNumber

/-! ### Transparency -/

#check Lean.Meta.TransparencyMode
#check Lean.Meta.TransparencyMode.reducible
#check Lean.Meta.TransparencyMode.instances
#check Lean.Meta.TransparencyMode.default
#check Lean.Meta.TransparencyMode.all

#check Lean.Meta.getTransparency
#check Lean.Meta.withTransparency
#check Lean.Meta.withReducible
#check Lean.Meta.withReducibleAndInstances
#check Lean.Meta.withDefault

#check Lean.Meta.ppExpr

def traceConstWithT
    {N T : Type} {M : Type → Type} [MyName N] [MyTransparencyMode T] [MyMetaM M]
    (md : T) (c : N) : M (MyMetaM.FormatOut M)
    :=
  let reduceAction := MyMetaM.reduce (MyExpr.const c : Lean.Expr)
  do
    let reducedExpr ← MyMetaM.withTransparency md reduceAction
    MyMetaM.prettyPrint reducedExpr

@[irreducible]
def irreducibleDef : Nat := 1

def defaultDef : Nat := irreducibleDef + 1
abbrev reducibleDef : Nat := defaultDef + 1

abbrev traceConstWithTM {N : Type} [MyName N] :=
  traceConstWithT (N := N) (T := Lean.Meta.TransparencyMode) (M := Lean.MetaM)

#eval traceConstWithTM MyTransparencyMode.reducible ``reducibleDef

set_option pp.explicit true in
#eval traceConstWithTM MyTransparencyMode.reducible ``reducibleDef

#eval traceConstWithTM MyTransparencyMode.instances ``reducibleDef
#eval traceConstWithTM MyTransparencyMode.all ``reducibleDef

/-! ### Weak head normalization -/

#check Lean.Meta.whnf

open Lean.Elab.Term in
def whnf' (e: TermElabM Lean.Syntax) : TermElabM Std.Format := do
  let e ← elabTermAndSynthesize (← e) none
  Lean.Meta.ppExpr (← Lean.Meta.whnf e)

#eval whnf' `(List.cons 1 [])
#eval whnf' `(List.cons (1 + 1) [])
#eval Lean.Meta.withTransparency .reducible $ whnf' `(List.append [1] [2])
#eval whnf' `(λ x : Nat => x)
#eval whnf' `(∀ x, x > 0)
#eval whnf' `(Type 3)
#eval whnf' `((15 : Nat))

#eval whnf' `(List.append [1])
#eval whnf' `((λ x y => x + y) 1)
#eval whnf' `(let x : Nat := 1; x)

def matchAndReducing
    (e : Lean.Expr) : Lean.MetaM (Option (Lean.Expr × Lean.Expr))
    := do
  return match ← Lean.Meta.whnf e with
  /- The equivalent of pattern matching on `MyExpr` would be very tedious,
     so don't bother. -/
  | (.app (.app (.const ``And _) P) Q) => some (P, Q)
  | _ => none

open Lean (Expr) in
def matchAndReducing₂
    (e : Expr) : Lean.MetaM (Option (Expr × Expr × Expr))
    := do
  match ← Lean.Meta.whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← Lean.Meta.whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
    | _ => return none
  | _ => return none

/-! ### Definitional equality -/

#check Lean.Meta.isDefEq
#check MyMetaM.isDefEq

#check Lean.MetavarKind
#check Lean.MetavarKind.natural
#check Lean.MetavarKind.synthetic
#check Lean.MetavarKind.syntheticOpaque

/-! ## Constructing expressions -/

/-! ### Applications -/

def appendAppend (xs ys : List α) := (xs.append ys).append xs

set_option pp.all true in
set_option pp.explicit true in
#print appendAppend

def appendAppendRhsExpr₁
    {E L : Type} [MyExpr E] [MyLevel L] (u : L) (α xs ys : E) : E
    :=
  MyExpr.appN (MyExpr.constL ``List.append [u])
    #[α, MyExpr.appN (MyExpr.constL ``List.append [u]) #[α, xs, ys], xs]

#check Lean.Meta.mkAppM

def appendAppendRhsExpr₂
    {M : Type → Type} {E : Type} [MyMetaM M] [MyExpr E] (xs ys : E) : M E
    := do
  let subApp ← MyMetaM.mkAppM ``List.append #[xs, ys]
  MyMetaM.mkAppM ``List.append #[subApp, xs]

#check Lean.Meta.mkAppM'

-- #eval Lean.Meta.mkAppM ``List.append #[]
-- Produces error: AppBuilder for 'mkAppM', result contains metavariables

#check Lean.Meta.mkAppOptM

def revOrd : Ord Nat where
  compare x y := compare y x

open MyExpr (const natLit) in
def ordExpr {M : Type → Type} {E : Type} [MyMetaM M] [MyExpr E] : M E := do
  let args := #[none, some (const ``revOrd), some (natLit 0), some (natLit 1)]
  MyMetaM.mkAppOptM ``compare args

#eval Lean.format <$> (ordExpr (M := Lean.MetaM) (E := Lean.Expr))

#check Lean.Meta.mkAppOptM'

/-! ### Lambdas and foralls -/

def doubleExpr₁ {E : Type} [MyExpr E] : E :=
  let bvar0 := MyExpr.bvar 0
  let body := MyExpr.appN (MyExpr.const ``Nat.add) #[bvar0, bvar0]
  MyExpr.lam `x (MyExpr.const ``Nat) body

#eval MyMetaM.prettyPrint (M := Lean.MetaM) (E := Lean.Expr) doubleExpr₁

def doubleExpr₂ {M : Type → Type} {E : Type} [MyMetaM M] [MyExpr E] : M E :=
  MyMetaM.withLocalDecl `x (MyExpr.const ``Nat : E) λ xId => do
    let x := MyExpr.fvar xId
    let body ← MyMetaM.mkAppM ``Nat.add #[x, x]
    MyMetaM.mkLambdaFVars #[x] body

#eval show Lean.MetaM _ from do
  Lean.Meta.ppExpr (← doubleExpr₂)

#check Lean.Meta.withLocalDecl
#check Lean.Meta.mkLambdaFVars
#check Lean.Meta.withLocalDecls
#check Lean.Meta.mkForallFVars
#check Lean.Meta.mkLetFVars
#check Lean.mkArrow
#check Lean.Meta.mkEq

def somePropExpr
    {M : Type → Type} {E : Type} [MyMetaM M] [MyExpr E] : Lean.MetaM Lean.Expr
    :=
  let natType : E := MyExpr.const ``Nat
  let funcType := MyExpr.mkArrow natType natType
  MyMetaM.withLocalDecl `f funcType λ fId => do
    let f := MyExpr.fvar fId
    let feqn ← MyMetaM.withLocalDecl `n natType λ nId => do
      let n := MyExpr.fvar nId
      let lhs := MyExpr.app f n
      let rhs := MyExpr.app f (← MyMetaM.mkAppM ``Nat.succ #[n])
      let eqn ← MyMetaM.mkEq lhs rhs
      MyMetaM.mkForallFVars #[n] eqn
    MyMetaM.mkLambdaFVars #[f] feqn

elab "someProp" : term => somePropExpr (M := Lean.MetaM) (E := Lean.Expr)

#check someProp
#reduce (types := true) someProp Nat.succ

/-! ### Deconstructing expressions -/

#check Lean.Meta.forallTelescope
#check Lean.Meta.forallTelescopeReducing
#check Lean.Meta.forallBoundedTelescope
#check Lean.Meta.forallMetaTelescope
#check Lean.Meta.forallMetaTelescopeReducing
#check Lean.Meta.forallMetaBoundedTelescope
#check Lean.Meta.lambdaTelescope
#check Lean.Meta.lambdaBoundedTelescope
#check Lean.Meta.lambdaMetaTelescope

def myApply
    {mvId E : Type} {M : Type → Type} [MyMVarId mvId] [MyExpr E] [MyMetaM M]
    (goal : mvId) (e : E) : M (List (MyMetaM.MVarIdOut M))
    := do
  MyMetaM.failIfAssigned goal `myApply
  MyMetaM.withLocalCtxOf goal do
    let goalType ← MyMetaM.mvarType goal
    let exprType ← MyMetaM.inferType e
    /-
    If `exprType` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    metavariables for the `xᵢ` and obtain the conclusion `U`. (If `exprType`
    does not have this form, `args` is empty and `conclusion = exprType`).
    -/
    let (args, bodyType) ← MyMetaM.forallMetaTelescopeReducing exprType
    if !(← MyMetaM.isDefEq goalType bodyType) then
      let msg := m!"{e} is not applicable to goal with type {goalType}"
      MyMetaM.throwTacticEx `myApply goal msg
    /-
    At this point we know the goal can be satisfied by applying the expression
    `e` to the metavariable arguments from the telescope.
    -/
    MyMetaM.assign goal (MyExpr.appN e <| args.map MyExpr.mvar)
    /-
    Some of the args may already be assigned via unification. Return the
    unassigned ones as new goals.
    -/
    let newGoals ← args.filterMapM λ mvarId =>
      return if (← MyMetaM.isAnyAssigned mvarId) then none else some mvarId
    return newGoals.toList

elab "myApply" e:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm e none
  Lean.Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a

/-! ## Backtracking -/

#check Lean.MonadBacktrack
#check Lean.saveState
#check Lean.restoreState

def tryM (x : Lean.MetaM Unit) : Lean.MetaM Unit := do
  let s ← Lean.saveState
  try
    x
  catch _ =>
    Lean.restoreState s

#check Lean.withoutModifyingState
#check Lean.observing?
#check Lean.commitIfNoEx
#check Lean.Meta.SavedState.restore
#check Lean.Core.SavedState.restore

/-! ## Exercises -/

def ex01
    {N : Type} {M : Type → Type} [MyName N] [MyMetaM M] (typeName : N) : M Unit
    := do
  let mvId ← MyMetaM.mkFreshMVar (MyExpr.const typeName : Lean.Expr)
  MyMetaM.assign mvId (MyExpr.natLit 3 : Lean.Expr)

#eval (ex01 ``Nat : Lean.MetaM Unit)
#eval (ex01 ``String : Lean.MetaM Unit) -- No runtime error

-- Exercise 02
-- Answer: it should output the expression unchanged, because it contains no
-- metavariables
-- Confirmation:

def ex02Expr : Lean.Expr :=
  Lean.mkAppN (.const ``Nat.add []) #[Lean.mkNatLit 1, Lean.mkNatLit 2]
#eval (Lean.instantiateMVars ex02Expr : Lean.MetaM Lean.Expr)
-- I was basically correct, but the full expression has a lot more details than
-- I mentioned. There were no metavariables though!

-- Exercise 03
#eval show Lean.MetaM Lean.Expr from do
  let oneExpr := Lean.Expr.app (.const ``Nat.succ []) (.const ``Nat.zero [])
  let twoExpr := Lean.Expr.app (.const ``Nat.succ []) oneExpr

  let mvar1 ← Lean.Meta.mkFreshExprMVar (Lean.Expr.const ``Nat [])
  let mvar2 ← Lean.Meta.mkFreshExprMVar (Lean.Expr.const ``Nat [])
  let mvar3 ← Lean.Meta.mkFreshExprMVar (Lean.Expr.const ``Nat [])

  let natAdd := Lean.Expr.const ``Nat.add []
  let innerSum := Lean.mkAppN natAdd #[twoExpr, mvar2]
  let outerSum := Lean.mkAppN natAdd #[innerSum, mvar3]
  mvar1.mvarId!.assign outerSum
  mvar3.mvarId!.assign oneExpr

  Lean.instantiateExprMVars mvar1

-- Exercise 04
elab "explore" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl ← mvarId.getDecl

  let showDecl (type : Lean.Expr) (userName : Lean.Name) : IO Unit := do
    IO.println s!"  Type: ${type}"
    IO.println s!"  User name: ${userName}"

  IO.println "Exercise 04"
  IO.println "Our metavariable"
  showDecl metavarDecl.type metavarDecl.userName

  IO.println "All of its local declarations"
  mvarId.withContext do
    for ldecl in ← Lean.getLCtx do
      if ldecl.isImplementationDetail then continue
      showDecl ldecl.type ldecl.userName

-- Exercise 05
-- Write a tactic `solve` that proves the theorem `red`.
elab "solve" : tactic => do
  let goalId ← Lean.Elab.Tactic.getMainGoal
  let goalType ← goalId.getType
  goalId.withContext do
    for ldecl in ← Lean.getLCtx do
      if ldecl.isImplementationDetail then continue
      if !(← Lean.Meta.isDefEq goalType ldecl.type) then continue
      goalId.assign ldecl.toExpr
      break

set_option linter.unusedVariables false in
theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  solve

-- Exercise 06
-- What is the normal form of the following expressions?

-- a) `fun x => x` of type `Bool → Bool`
-- My answer: `fun x => x`
#reduce (fun x => x : Bool → Bool)

-- b) `(fun x => x) ((true && false) || true)` of type `Bool`
-- My answer: `true`
#reduce (fun x => x) ((true && false) || true)

-- c) `800 + 2` of type `Nat`
-- My answer: `802`
#reduce 800 + 2

-- Exercise 07
#eval show Lean.MetaM Bool from do
  let litOne := Lean.Expr.lit (Lean.Literal.natVal 1)
  let conOne := Lean.Expr.app (.const ``Nat.succ []) (.const ``Nat.zero [])
  Lean.Meta.isDefEq litOne conOne

-- Exercise 08
def printMCtxInfo : Lean.MetaM Unit := do
  let mctx ← Lean.getMCtx
  IO.println s!"Metavar counter: ${mctx.mvarCounter}"
  IO.println s!"Metavar types: ${(mctx.decls.map (·.type)).toList.map (·.2)}"
  IO.println s!"Metavar assignments: ${mctx.eAssignment.toList.map (·.2)}"

-- (a) `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
-- Yes, because the argument to `(fun x => 5)` is ignored
#eval show Lean.MetaM Bool from do
  let natType := Lean.Expr.const ``Nat []
  let lhs := Lean.Expr.lit (Lean.Literal.natVal 5)
  let fnX ← do
    let xTypeExpr ← Lean.Meta.mkFreshExprMVar none
    Lean.Meta.withLocalDecl `x .default xTypeExpr λ x =>
      Lean.Meta.mkLambdaFVars #[x] (.lit (.natVal 5))
  let fnY ← do
    let yTypeExpr ← Lean.mkArrow natType natType
    Lean.Meta.withLocalDecl `y .default yTypeExpr λ y =>
      Lean.Meta.mkLambdaFVars #[y] y
  let fnZ ← do
    Lean.Meta.withLocalDecl `z .default natType λ z =>
      Lean.Meta.mkLambdaFVars #[z] z
  let rhs := Lean.Expr.app fnX (.app fnY fnZ)
  let isEq ← Lean.Meta.isDefEq lhs rhs
  -- It appears no metavariables were assigned
  printMCtxInfo
  return isEq

-- (b) `2 + 1 =?= 1 + 2`
-- Yes, because both sides can be fully reduced to 3
#eval show Lean.MetaM Bool from do
  let natAdd := .const ``Nat.add []
  let litOne := .lit (.natVal 1)
  let litTwo := .lit (.natVal 2)
  let lhs := Lean.mkAppN natAdd #[litTwo, litOne]
  let rhs := Lean.mkAppN natAdd #[litOne, litTwo]
  let isEq ← Lean.Meta.isDefEq lhs rhs
  -- No metavars were created or assigned
  printMCtxInfo
  return isEq

-- (c) `?a =?= 2`, where `?a` has type `String`
-- No, the types are not compatible
#eval show Lean.MetaM Bool from do
  let stringType := Lean.Expr.const ``String []
  let lhs ← Lean.Meta.mkFreshExprMVar stringType (userName := `a)
  let rhs := .lit (.natVal 2)
  let isEq ← Lean.Meta.isDefEq lhs rhs
  printMCtxInfo
  return isEq

-- (d) `?a + Int =?= "hi" + ?b`, where `?a` and `?b` don't have a type
-- No, there's no `+` operator that works with `String` and `Type`, so the
-- metavariables won't be assigned, even though that could be done consistently
-- My guess was correct, using `#eval` here gives the following error:
-- `incorrect number of universe levels HAdd.hAdd`
#check show Lean.MetaM Bool from do
  let addOp := .const ``HAdd.hAdd []
  let lhs := do
    let mvarA ← Lean.Meta.mkFreshExprMVar none (userName := `a)
    let intType := .const ``Int []
    return Lean.mkAppN addOp #[mvarA, intType]
  let rhs := do
    let mvarB ← Lean.Meta.mkFreshExprMVar none (userName := `b)
    let strLit := .lit (.strVal "hi")
    return Lean.mkAppN addOp #[strLit, mvarB]
  let isEq ← Lean.Meta.isDefEq (← lhs) (← rhs)
  printMCtxInfo
  return isEq

-- (e) `2 + ?a =?= 3`
-- No, because Lean can't unify expressions that don't have the same structure?
#eval show Lean.MetaM Bool from do
  let mvarA ← Lean.Meta.mkFreshExprMVar none (userName := `a)
  let lhs := Lean.mkAppN (.const ``Nat.add []) #[.lit (.natVal 2), mvarA]
  let rhs := .lit (.natVal 3)
  let isEq ← Lean.Meta.isDefEq lhs rhs
  printMCtxInfo
  return isEq

-- (f) `2 + ?a =?= 2 + 1`
-- Yes, because the expressions have the same structure and the right types
#eval show Lean.MetaM Bool from do
  let natAdd := .const ``Nat.add []
  let mvarA ← Lean.Meta.mkFreshExprMVar none (userName := `a)
  let lhs := Lean.mkAppN natAdd #[.lit (.natVal 2), mvarA]
  let rhs := Lean.mkAppN natAdd #[.lit (.natVal 2), .lit (.natVal 1)]
  let isEq ← Lean.Meta.isDefEq lhs rhs
  printMCtxInfo
  return isEq

-- Exercise 09
-- Write down what you expect the following code to output
-- reducible: [1, instanceDef, defaultDef, irreducibleDef]
-- instances: [1, 2, defaultDef, irreducibleDef]
-- default: [1, 2, 3, irreducibleDef]
-- all: [1, 2, 3, 4]
-- normal: [1, 2, 3, irreducibleDef]
namespace ex_09
open Lean
open Lean.Meta

@[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
@[instance] def instanceDef       : Nat := 2 -- same as `instance`
def defaultDef                    : Nat := 3
@[irreducible] def irreducibleDef : Nat := 4

@[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

#eval show MetaM Unit from do
  let constantExpr := Expr.const ``sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr)
end ex_09

-- Exercise 10
def ex10a : Lean.Expr :=
  let body := Lean.mkAppN (.const ``Nat.add []) #[.lit (.natVal 1), .bvar 0]
  .lam `x (.const ``Nat []) body .default

#eval ex10a
elab "ex10a_term" : term => return ex10a
#check ex10a_term

def ex10b : Lean.MetaM Lean.Expr :=
  Lean.Meta.withLocalDecl `x .default (.const ``Nat []) λ x => do
    let body ← Lean.Meta.mkAppM ``Nat.add #[.lit (.natVal 1), x]
    Lean.Meta.mkLambdaFVars #[x] body

#eval ex10b
elab "ex10b_term" : term => ex10b
#check ex10b_term

end Lean4Metaprog.Ch4
