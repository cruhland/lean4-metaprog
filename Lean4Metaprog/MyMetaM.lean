import Lean4Metaprog.MyExpr
import Lean4Metaprog.MyLocalContext
import Lean4Metaprog.MyMVarId

namespace Lean4Metaprog

/-- The parts of the `Lean.MetaM` interface that I've used so far. -/
class MyMetaM (M : Type → Type) extends Monad M where
  /--
  The type of unique identifiers for metavariables that is returned from
  operations.
  -/
  MVarIdOut : Type

  /-- `MVarIdOut` satisfies the properties of a metavariable ID. -/
  myMVarIdOut : MyMVarId MVarIdOut

  /-- The type of expressions returned from operations. -/
  ExprOut : Type

  /-- `ExprOut` satisfies the properties of an expression type. -/
  myExprOut : MyExpr ExprOut

  /-- The type of local contexts returned from operations. -/
  LocalCtxOut : Type

  /-- Returned local contexts satisfy all of the expected properties. -/
  myLocalCtxOut : MyLocalContext LocalCtxOut

  /-- The current local context. -/
  localCtx : M LocalCtxOut

  /--
  Interpret a metavariable action with the local context of a metavariable.
  -/
  withLocalCtxOf {α mvId : Type} [MyMVarId mvId] : mvId → M α → M α

  /--
  Determine whether two expressions evaluate to the same normal form (i.e., are
  definitionally equal).
  -/
  isDefEq {E : Type} [MyExpr E] (e₁ e₂ : E) : M Bool

  /-- Create a new, unique metavariable with the given type. -/
  mkFreshMVar {E : Type} [MyExpr E] (type : E) : M MVarIdOut

  /--
  Return the given expression with all metavariables assigned in the current
  context replaced with their values.
  -/
  instantiateMVars {E : Type} [MyExpr E] (expr : E) : M ExprOut

  /-- Unsafely fill in the value of a metavariable (no validity checks). -/
  assign
    {E mvId : Type} [MyExpr E] [MyMVarId mvId] (mvar : mvId) (val : E) : M Unit

  /-- Fail the monad if the given metavariable already has a value. -/
  failIfAssigned
    {mvId N : Type} [MyMVarId mvId] [MyName N]
    (mvar : mvId) (tacticName : N) : M Unit

  /-- Retrieve the given metavariable's type, as an expression. -/
  mvarType {mvId : Type} [MyMVarId mvId] (mvar : mvId) : M ExprOut

instance mymetam_metam_inst : MyMetaM Lean.MetaM := {
  MVarIdOut := Lean.MVarId
  myMVarIdOut := inferInstance
  ExprOut := Lean.Expr
  myExprOut := inferInstance
  LocalCtxOut := Lean.LocalContext
  myLocalCtxOut := inferInstance
  localCtx := Lean.getLCtx
  withLocalCtxOf := Lean.MVarId.withContext ∘ MyMVarId.toMVarId
  isDefEq := λ e₁ e₂ => Lean.Meta.isDefEq (MyExpr.toExpr e₁) (MyExpr.toExpr e₂)
  mkFreshMVar := λ type => do
    let lctx ← Lean.getLCtx
    let localInsts ← Lean.Meta.getLocalInstances
    let mvarId ← Lean.mkFreshMVarId

    Lean.MonadMCtx.modifyMCtx λ mctx =>
      let typeExpr := MyExpr.toExpr type
      let userName := Lean.Name.anonymous
      let kind := Lean.MetavarKind.natural
      let numScopeArgs := 0

      mctx.addExprMVarDecl
        mvarId userName lctx localInsts typeExpr kind numScopeArgs

    return mvarId
  instantiateMVars := Lean.instantiateMVars ∘ MyExpr.toExpr
  assign := λ mvarId => (MyMVarId.toMVarId mvarId).assign ∘ MyExpr.toExpr
  failIfAssigned := λ mvid tacticName =>
    (MyMVarId.toMVarId mvid).checkNotAssigned (MyName.toName tacticName)
  mvarType := Lean.MVarId.getType ∘ MyMVarId.toMVarId
}

namespace MyMetaM

variable {M : Type → Type} [MyMetaM M]

instance mymvarid_mvaridout_inst : MyMVarId (MVarIdOut M) := myMVarIdOut

instance myexpr_exprout_inst : MyExpr (ExprOut M) := myExprOut

instance mylocalcontext_localctxout_inst : MyLocalContext (LocalCtxOut M) :=
  myLocalCtxOut

end Lean4Metaprog.MyMetaM
