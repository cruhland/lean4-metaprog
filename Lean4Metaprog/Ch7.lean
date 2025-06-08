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

end Lean4Metaprog.Ch7
