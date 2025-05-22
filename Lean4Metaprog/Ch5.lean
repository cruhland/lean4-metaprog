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

end Lean4Metaprog.Ch5
