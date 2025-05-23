import Lean

namespace Lean4Metaprog.Ch5

/-! # Syntax -/

/-! ## Declaring syntax -/

/-! ### Declaration helpers -/

-- XOR, denoted \oplus or \o+
infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- with `notation`, "left XOR"
notation:10 l:10 " LXOR " r:11 => (!l && r)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

#eval true ⊕ false LXOR false -- false
#eval (true ⊕ false) LXOR false -- false
#eval true ⊕ (false LXOR false) -- true

-- Make a right associative RXOR using `notation`
notation:10 l:11 " RXOR " r:10 => (l && !r)

#eval true RXOR false RXOR true -- true
#eval (true RXOR false) RXOR true -- false
#eval true RXOR (false RXOR true) -- true

notation:65 lhs:65 " ~ " rhs:65 => (lhs - rhs)
#eval 5 ~ 3 ~ 3 -- 5 because this is parsed as 5 - (3 - 3)

notation:65 a:65 " ~ " b:65 " mod " rel:65 => rel a b
#check 0 ~ 0 mod Eq -- 0 = 0 : Prop

/-! ### Free form syntax declarations -/

syntax "MyTerm" : term
#check_failure MyTerm

namespace BoolExpr

-- Use `scoped` to keep these inside this namespace
scoped syntax "⊥" : term
scoped syntax "⊤" : term
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
#check_failure ⊥ OR (⊤ AND ⊥) -- parsing passes, but no elab fn

end BoolExpr

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr
syntax "⊤" : boolean_expr
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

-- gives "expected term" error
-- #check ⊥ AND ⊤

syntax "[Bool|" boolean_expr "]" : term
#check_failure [Bool| ⊥ AND ⊤ ]

/-! ### Syntax combinators -/

syntax binOne := "O"
syntax binZero := "Z"
syntax binDigit := binZero <|> binOne

-- The `+` denotes "one or more"; use `*` for "zero or more"
-- The `,` is the separator between items; if omitted, space is the separator
syntax binNumber := binDigit,+

syntax "bin(" binNumber ")" : term
#check_failure bin(Z, O, Z, Z, O) -- no elab, but parsing succeeds
-- #check_failure bin() -- fails to parse, need at least one O or Z

syntax binNumber' := binDigit,*
syntax "emptyBin(" binNumber' ")" : term
#check_failure emptyBin() -- no elab, but parsing succeeds

syntax "binCompact(" ("Z" <|> "O"),+ ")" : term
#check_failure binCompact(Z, O, Z, Z, O) -- no elab, but parsing succeeds

-- Write `(...)?` to denote an optional portion
syntax "binDoc(" (str ";")? binNumber ")" : term
#check_failure binDoc(Z, O, Z, Z, O) -- no elab, valid parse
#check_failure binDoc("mycomment"; Z, O, Z, Z, O) -- no elab, valid parse

/-! ## Operating on syntax -/

/-! ### Constructing new syntax -/

open Lean
#check Syntax
#check Syntax.mkApp
#check Lean.Parser.Term.app
#check mkNode
#check mkIdent
#check Syntax.mkNumLit
#check mkAtom

def oneLit := Syntax.mkNumLit "1"
#eval Syntax.mkApp (mkIdent `Nat.add) #[oneLit, oneLit]
#eval mkNode `«term_+_» #[oneLit, mkAtom "+", oneLit]

/-! ### Matching on syntax -/

def isAdd11 : Syntax → Bool
| `(Nat.add 1 1) => true
| _ => false

#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[oneLit, oneLit]) -- true
#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, oneLit]) -- false

def isAdd : Syntax → Option (Syntax × Syntax)
| `(Nat.add $x $y) => some (x, y)
| _ => none

#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[oneLit, oneLit]) -- some
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, oneLit]) -- some
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo]) -- none

/-! ### Typed syntax -/

def isLitAdd : TSyntax `term → Option Nat
| `(Nat.add $x:num $y:num) => some (x.getNat + y.getNat)
| _ => none

#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[oneLit, oneLit]) -- some 2
#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, oneLit]) -- none

def isBoolExpr : Syntax → Bool
| `(boolean_expr|⊥ AND ⊤) => true
| _ => false

-- It works!
def boolExprParts : Array Syntax :=
  #[mkNode ``«boolean_expr⊥» #[mkAtom "⊥"],
    mkAtom "AND",
    mkNode ``«boolean_expr⊤» #[mkAtom "⊤"]]
def boolExpr := mkNode ``boolean_expr_AND_ boolExprParts
#eval boolExpr
#eval isBoolExpr boolExpr -- true
#eval `(boolean_expr|⊥ AND ⊤)

/-! ### Mini project -/

declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

-- The `partial` appears to be needed because Lean can't prove termination
partial def denoteArith : TSyntax `arith → Nat
| `(arith| $x:num ) => x.getNat
| `(arith| $x:arith + $y:arith ) => denoteArith x + denoteArith y
| `(arith| $x:arith - $y:arith ) => denoteArith x - denoteArith y
| `(arith| ($x:arith) ) => denoteArith x
| _ => 0

-- Use `TermElabM` to allow construction of `Syntax` with ``(...)` notation
def test : Elab.TermElabM Nat := do
  let stx ← `(arith| (12 + 3) - 4)
  return denoteArith stx

#eval test -- 11

/-! ## More elaborate examples -/

/-! ### Using type classes for notations -/

class Subset (α : Type u) where
  subset : α → α → Prop

infix:50 " ⊆ " => Subset.subset

def Set (α : Type u) := α → Prop

def Set.mem (X : Set α) (x : α) : Prop := X x

instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

instance : Subset (Set α) where
  subset X Y := (x : α) → x ∈ X → x ∈ Y

example (X : Set α) : Set.empty ⊆ X := by
  show (x : α) → x ∈ Set.empty → x ∈ X
  intro (x : α) (h : x ∈ Set.empty)
  show x ∈ X
  have : Set.empty x := h
  have : False := this
  exact False.elim this

/-! ### Binders -/

-- Using this ensures the syntax is interpreted as `Set α` and not `α → Prop`
def setOf {α : Type} (p : α → Prop) : Set α := p

notation "{ " x " | " p " }" => setOf (λ x => p)

#check { x | x ≤ 1 } -- { x | x ≤ 1 } : Set Nat

example : 1 ∈ { y | y ≤ 1 } := by simp [Membership.mem, Set.mem, setOf]
example : 2 ∈ { y | 1 ≤ y ∧ y ≤ 3 } := by simp [Membership.mem, Set.mem, setOf]

/-! ## Exercises -/

-- Exercise 1
namespace ex_1a
scoped notation:80 lhs:81 " ∸ " rhs:80 => lhs - rhs
#eval 5 * 8 ∸ 4
#eval 8 ∸ 6 ∸ 1
end ex_1a

namespace ex_1b
scoped infixr:80 " ∸ " => (· - ·)
#eval 5 * 8 ∸ 4
#eval 8 ∸ 6 ∸ 1
end ex_1b

namespace ex_1c
scoped syntax:80 term:81 " ∸ " term:80 : term
-- Need `macro_rules` to map the syntax to a term, which hasn't been covered yet
end ex_1c

-- Exercise 2
syntax "good" "morning" : term
syntax "hello" : command
syntax "yellow" : tactic

#check_failure good morning -- parses, but no elab
/-
hello -- parses, but no elab
example : Nat := by yellow -- parses, but no elab
-/

-- Exercise 3
syntax (name := colors) ("red"+ <|> "blue"+) num : command
@[command_elab colors] def elabColors : Lean.Elab.Command.CommandElab :=
  λ _ => Lean.logInfo "success!"

red red red 4
blue 7
blue blue blue blue blue 18
-- red blue blue 5 -- confirmed this doesn't work

end Lean4Metaprog.Ch5
