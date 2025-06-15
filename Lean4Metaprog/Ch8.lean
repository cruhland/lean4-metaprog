import Lean

namespace Lean4Metaprog.Ch8

/-! # Embedding DSLs by elaboration -/

open Lean (Expr Syntax mkNatLit mkStrLit)
open Lean.Meta (MetaM mkAppM)

/-! ## Defining our AST -/

inductive ImpLit
| nat (n : Nat)
| bool (b : Bool)

inductive ImpUnOp
| not

inductive ImpBinOp
| add | and | less

inductive ImpExpr
| lit (l : ImpLit)
| var (v : String)
| un (op : ImpUnOp) (arg : ImpExpr)
| bin (op : ImpBinOp) (l r : ImpExpr)

inductive ImpProgram
| Skip
| Assign (v : String) (e: ImpExpr)
| Seq (p q : ImpProgram)
| If (c : ImpExpr) (t e : ImpProgram)
| While (c : ImpExpr) (b : ImpProgram)

/-! ## Elaborating literals -/

declare_syntax_cat imp_lit
syntax num : imp_lit
syntax "true" : imp_lit
syntax "false" : imp_lit

def elabImpLit : Syntax → MetaM Expr
| `(imp_lit| $n:num) => mkAppM ``ImpLit.nat #[mkNatLit n.getNat]
| `(imp_lit| true) => mkAppM ``ImpLit.bool #[.const ``Bool.true []]
| `(imp_lit| false) => mkAppM ``ImpLit.bool #[.const ``Bool.false []]
| _ => Lean.Elab.throwUnsupportedSyntax

elab "test_elabImpLit " l:imp_lit : term => elabImpLit l

#reduce test_elabImpLit 4 -- ImpLit.nat 4
#reduce test_elabImpLit true -- ImpLit.bool «true»
#reduce test_elabImpLit false -- ImpLit.bool «false»

/-! ## Elaborating expressions -/

declare_syntax_cat imp_unop
syntax "not" : imp_unop

def elabImpUnOp : Syntax → MetaM Expr
| `(imp_unop| not) => return .const ``ImpUnOp.not []
| _ => Lean.Elab.throwUnsupportedSyntax

declare_syntax_cat imp_binop
syntax " + " : imp_binop
syntax " and " : imp_binop
syntax " < " : imp_binop

def elabImpBinOp : Syntax → MetaM Expr
| `(imp_binop| +) => return .const ``ImpBinOp.add []
| `(imp_binop| and) => return .const ``ImpBinOp.and []
| `(imp_binop| <) => return .const ``ImpBinOp.less []
| _ => Lean.Elab.throwUnsupportedSyntax

declare_syntax_cat imp_expr
syntax imp_lit : imp_expr
syntax ident : imp_expr
syntax imp_unop imp_expr : imp_expr
syntax imp_expr imp_binop imp_expr : imp_expr

syntax "(" imp_expr ")" : imp_expr

partial def elabImpExpr : Syntax → MetaM Expr
| `(imp_expr| $l:imp_lit) => do
  let l ← elabImpLit l
  mkAppM ``ImpExpr.lit #[l]
| `(imp_expr| $i:ident) =>
  mkAppM ``ImpExpr.var #[mkStrLit i.getId.toString]
| `(imp_expr| $b:imp_unop $e:imp_expr) => do
  let b ← elabImpUnOp b
  let e ← elabImpExpr e
  mkAppM ``ImpExpr.un #[b, e]
| `(imp_expr| $l:imp_expr $b:imp_binop $r:imp_expr) => do
  let b ← elabImpBinOp b
  let l ← elabImpExpr l
  let r ← elabImpExpr r
  mkAppM ``ImpExpr.bin #[b, l, r]
| `(imp_expr | ($e:imp_expr)) =>
  elabImpExpr e
| _ =>
  Lean.Elab.throwUnsupportedSyntax

elab "test_elabImpExpr " e:imp_expr : term => elabImpExpr e

#reduce test_elabImpExpr a
-- .var "a"

#reduce test_elabImpExpr a + 5
-- .bin .add (.var "a") (.lit (.nat 5))

#reduce test_elabImpExpr 1 + true
-- .bin .add (.lit (.nat 1)) (.lit (.bool «true»))

end Lean4Metaprog.Ch8
