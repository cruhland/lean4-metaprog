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

/-! ## Simplifying macro declaration -/

syntax:10 term:10 " RXOR " term:11 : term

macro_rules
| `($l:term RXOR $r:term) => `($l && !$r)

macro:10 l:term:10 " ⊕ " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

/-! ## Syntax quotations -/

/-! ### The basics -/

/-
instance : Coe (TSyntax `a) (TSyntax `b) where
  coe s := ⟨s.raw⟩
-/

#check TSyntax.getNat

/-! ### Advanced anti-quotations -/

-- The syntax «`($(mkIdent `c))» is the same as «let x := mkIdent `c; `($x)»

-- syntactically cut away the first element of a tuple if possible
syntax "cut_tuple" "(" term ", " term,+ ")" : term

macro_rules
-- This base clause is needed because the anti-quotation `$xs,*` can only be
-- used in a parsing context where a "repeat" parser is expected. Thus the
-- tuples that we make on the RHS must always have an explicit first element.
| `(cut_tuple ($x, $y)) => `(($x, $y))
| `(cut_tuple ($_, $y, $xs,*)) => `(($y, $xs,*))

#check cut_tuple (1, 2)
#check cut_tuple (1, 2, 3)

syntax "mylet " ident (" : " term)? " := " term " in " term : term

macro_rules
| `(mylet $x $[: $ty]? := $val in $body) => `(let $x $[: $ty]? := $val; $body)

#eval mylet x := 5 in x - 10 -- 0, because of subtraction on Nat
#eval mylet x : Int := 5 in x - 10 -- -5, because of subtraction on Int

syntax "foreach " "[" term,* "] " term : term

macro_rules
| `(foreach [ $[$x:term],* ] $func:term) => `(let f := $func; [ $[f $x],* ])

#eval foreach [1,2,3,4] (Nat.add 2) -- [3, 4, 5, 6]

/-! ## Hygiene issues and how to solve them -/

-- Applying this macro produces a function that binds a new identifier x
macro "const " e:term : term => `(fun x => $e)

-- But `x` can also be defined by a user
def x : Nat := 42

-- Which `x` should be used by the compiler in place of `$e`?
#eval (const x) 10 -- 42

/-! ## `MonadQuotation` and `MonadRef` -/

namespace Playground

class MonadRef (m : Type → Type) where
  getRef : m Syntax
  withRef {α} : Syntax → m α → m α

class MonadQuotation (m : Type → Type) extends MonadRef m where
  getCurrMacroScope : m MacroScope
  getMainModule : m Name
  withFreshMacroScope {α : Type} : m α → m α

end Playground

syntax "error_position " ident : term

macro_rules
| `(error_position all) => Macro.throwError "Ahhh"
-- The `syn%$x` pattern binds the syntax `syn` to the name `x`
| `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")

#check_failure error_position all -- blue underline on the whole term
#check_failure error_position first -- blue underline just on `error_position`

end Lean4Metaprog.Ch6
