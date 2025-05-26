import Lean

namespace Lean4Metaprog.Ch6

/-! # Macros -/

/-! ## What is a macro -/

open Lean

#print Macro
#print MacroM
#check Macro.Context
#check Macro.State

syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
| `($l:term LXOR $r:term) => `(!$l && $r) -- in macros, backtick creates syntax
| _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

@[macro lxor] def lxorImpl2 : Macro
 -- special case, changes behavior for specific pieces of syntax
| `(true LXOR true) => `(true)
| _ => Macro.throwUnsupported

#eval true LXOR true -- true, handled by new macro
#eval true LXOR false -- false, handled by old after new throws

def foo := true
 -- false, handled by old macro: `foo` and `true` are not the same syntax
#eval foo LXOR foo

end Lean4Metaprog.Ch6
