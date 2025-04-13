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
    {T : Type} [MyTransparencyMode T] (md : T) (c : Lean.Name)
    : Lean.MetaM Std.Format
    :=
  let reduceAction := MyMetaM.reduce (MyExpr.const c : Lean.Expr)
  do
    let reducedExpr ← MyMetaM.withTransparency md reduceAction
    Lean.Meta.ppExpr reducedExpr

@[irreducible]
def irreducibleDef : Nat := 1

def defaultDef : Nat := irreducibleDef + 1
abbrev reducibleDef : Nat := defaultDef + 1

abbrev traceConstWithTM := traceConstWithT (T := Lean.Meta.TransparencyMode)

#eval traceConstWithTM MyTransparencyMode.reducible ``reducibleDef

set_option pp.explicit true in
#eval traceConstWithTM MyTransparencyMode.reducible ``reducibleDef

#eval traceConstWithTM MyTransparencyMode.instances ``reducibleDef
#eval traceConstWithTM MyTransparencyMode.all ``reducibleDef

end Lean4Metaprog.Ch4
