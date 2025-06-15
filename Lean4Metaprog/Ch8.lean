import Lean

namespace Lean4Metaprog.Ch8

/-! # Embedding DSLs by elaboration -/

open Lean (Expr Syntax mkNatLit)
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

end Lean4Metaprog.Ch8
