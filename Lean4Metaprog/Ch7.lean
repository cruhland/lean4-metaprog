import Lean

namespace Lean4Metaprog.Ch7

/-! # Elaboration -/

/-! ## Command elaboration -/

/-! ### Giving meaning to commands -/

#print Lean.Elab.Command.CommandElab
#print Lean.Elab.Command.CommandElabM

#check Lean.MonadLog
#check Lean.AddMessageContext
#check Lean.logInfo
#check Lean.logWarning
#check Lean.logError

#check Lean.MonadEnv
#check Lean.Environment
#check Lean.MonadOptions
#check Lean.MonadTrace

#check Lean.throwError

/-! ### Making our own -/

open Lean.Elab.Command (CommandElab)

syntax (name := mycommand1) "#mycommand1" : command

@[command_elab mycommand1]
def myCommand1Impl : CommandElab := λ _ => Lean.logInfo "Hello world"

#mycommand1 -- Hello world

elab "#mycommand2" : command => Lean.logInfo "Hello world"

#mycommand2 -- Hello world

@[command_elab mycommand1]
def myNewImpl : CommandElab := λ _ => Lean.logInfo "new!"

#mycommand1 -- new!

elab "#check" "mycheck" : command => Lean.logInfo "got ya!"

#check mycheck -- got ya!
#check "Hello" -- "Hello" : String
#check Nat.add -- Nat.add : Nat → Nat → Nat

@[command_elab Lean.Parser.Command.check] def mySpecialCheck : CommandElab :=
  λ stx => do
    if let some str := stx[1].isStrLit? then
      Lean.logInfo s!"Special elab of string literal: {str} : String"
    else
      Lean.Elab.throwUnsupportedSyntax

#check mycheck -- got ya!
#check "Hello" -- Special elab of string literal: Hello : String
#check Nat.add -- Nat.add : Nat → Nat → Nat

/-! ### Mini project -/

#check Lean.getEnv
#check Lean.Elab.expandMacroImpl?
#check Lean.Elab.liftMacroM
#check Lean.Elab.Command.commandElabAttribute
#check Lean.KeyedDeclsAttribute.getEntries

elab "#findCElab" c:command : command => do
  let env ← Lean.getEnv
  let macroOpt ← Lean.Elab.liftMacroM <| Lean.Elab.expandMacroImpl? env c
  match macroOpt with
  | some (name, _) =>
    Lean.logInfo s!"Refusing to expand next macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    -- Get all declarations annotated with the `command_elab {kind}` attr
    let elabs := Lean.Elab.Command.commandElabAttribute.getEntries env kind
    match elabs with
    | [] =>
      Lean.logInfo s!"No elaborators for syntax kind {kind}"
    | _ =>
      let declNames := elabs.map (·.declName.toString)
      Lean.logInfo s!"Elaborators for syntax {kind}: {declNames}"

#findCElab def lala := 12
#findCElab abbrev lolo := 12
#check Lean.Parser.Command.declaration
#check Lean.Elab.Command.elabDeclaration

#findCElab #check foo
#check Lean.Parser.Command.check
#check Lean4Metaprog.Ch7.mySpecialCheck
#check Lean.Elab.Command.elabCheck

#findCElab open Hi
#check Lean.Parser.Command.open
#check Lean.Elab.Command.elabOpen

#findCElab namespace Foo
#check Lean.Parser.Command.namespace
#check Lean.Elab.Command.elabNamespace

#findCElab #findCElab #eval 123 -- even works on itself!

/-! ## Term elaboration -/

/-! ### Giving meaning to terms -/

#print Lean.Elab.Term.TermElab
#check Lean.Elab.Term.TermElabM
#check Lean.Elab.Term.Context
#check Lean.Elab.Term.State

/-! ### Term elaboration -/

#check Lean.Elab.Term.SyntheticMVarKind
#check Lean.Elab.Term.SyntheticMVarKind.typeClass
#check Lean.Elab.Term.SyntheticMVarKind.coe
#check Lean.Elab.Term.SyntheticMVarKind.tactic
#check Lean.Elab.Term.SyntheticMVarKind.postponed

#check set_option trace.Elab.postpone true in List.foldr .add 0 [1,2,3]
#check_failure set_option trace.Elab.postpone true in List.foldr .add

/-! ### Making our own -/

syntax (name := myterm1) "myterm_1" : term

def mytermValues := [1, 2]

@[term_elab myterm1]
def myTerm1Impl : Lean.Elab.Term.TermElab := λ _ _ => do
  Lean.Meta.mkAppM ``List.get! #[.const ``mytermValues [], Lean.mkNatLit 0]

#eval myterm_1 -- => List.get! mytermValues 0 => 1

-- Also works with `elab`
elab "myterm_2" : term => do
  Lean.Meta.mkAppM ``List.get! #[.const ``mytermValues [], Lean.mkNatLit 1]

#eval myterm_2 -- => List.get! mytermValues 1 => 2

/-! ### Mini project -/

-- slightly different notation to prevent ambiguity
syntax (name := myanon) "⟪" term,* "⟫" : term

def getCtors (typ : Lean.Name) : Lean.Meta.MetaM (List Lean.Name) := do
  let env ← Lean.MonadEnv.getEnv
  return match env.find? typ with
  | some (Lean.ConstantInfo.inductInfo val) => val.ctors
  | _ => []

@[term_elab myanon]
def myanonImpl : Lean.Elab.Term.TermElab := λ stx typ? => do
  -- If this has already postponed once, do nothing
  Lean.Elab.Term.tryPostponeIfNoneOrMVar typ?
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then throwError "expected type must be known"
  let .const base .. :=
    typ.getAppFn | throwError s!"expected constant or fn app, found {typ}"
  let [ctor] ← getCtors base | throwError "type must have exactly one ctor"
  let args := Lean.TSyntaxArray.mk stx[1].getSepArgs
  let stx ← `($(Lean.mkIdent ctor) $args*)
  Lean.Elab.Term.elabTerm stx typ -- elaborate recursively

#check (⟪1, sorry⟫ : Fin 12)
#check_failure ⟪1, sorry⟫ -- expected type must be known
#check_failure (⟪0⟫ : Nat) -- type must have exactly one ctor
#check_failure (⟪⟫ : Nat → Nat) -- expected constant or fn app, found Nat → Nat

-- The `<= t` syntax replaces the first two lines of `myanonImpl`
-- elab "⟨⟨" args:term,* "⟩⟩" : term <= t => do sorry

end Lean4Metaprog.Ch7
