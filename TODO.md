On `generic` branch:
1. Make a `ToString` instance for `MyExpr` (convert to `Lean.Expr`)
1. Use your own `assign`
1. Update mvar assignment example with your own definitions.
1. Have `MyMetaM` just use `Lean.MVarId` for return values, not its own field
1. Make `MyMetaM MetaM` instance more efficient by replacing operations with
   more low-level ones.
1. Finish Chapter 4
1. Merge branch into `main`
