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

end Lean4Metaprog.Ch7
