
namespace Lean4Metaprog.Ch8

/-! # Embedding DSLs by elaboration -/

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

end Lean4Metaprog.Ch8
