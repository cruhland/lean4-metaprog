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

end Lean4Metaprog.Ch7
