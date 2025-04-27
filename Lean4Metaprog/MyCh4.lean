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

def somePropExpr : Lean.MetaM Lean.Expr := do
  let natType := .const ``Nat []
  let funcType ← Lean.mkArrow natType natType
  Lean.Meta.withLocalDecl `f .default funcType λ f => do
    let feqn ← Lean.Meta.withLocalDecl `n .default natType λ n => do
      let lhs := .app f n
      let rhs := .app f (← Lean.Meta.mkAppM ``Nat.succ #[n])
      let eqn ← Lean.Meta.mkEq lhs rhs
      Lean.Meta.mkForallFVars #[n] eqn
    Lean.Meta.mkLambdaFVars #[f] feqn

elab "someProp" : term => somePropExpr

#check someProp
#reduce (types := true) someProp Nat.succ

end Lean4Metaprog.Ch4
