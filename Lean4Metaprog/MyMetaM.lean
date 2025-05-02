import Lean4Metaprog.MyExpr
import Lean4Metaprog.MyFormat
import Lean4Metaprog.MyLocalContext
import Lean4Metaprog.MyMVarId
import Lean4Metaprog.MyTransparencyMode

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

  /--
  The type of unique identifiers for free variables returned from operations.
  -/
  FVarIdOut : Type

  /-- `FVarIdOut` satisfies the properties of a free variable identifier. -/
  myFVarIdOut : MyFVarId FVarIdOut

  /-- The type of expressions returned from operations. -/
  ExprOut : Type

  /-- `ExprOut` satisfies the properties of an expression type. -/
  myExprOut : MyExpr ExprOut

  /-- The type of local contexts returned from operations. -/
  LocalCtxOut : Type

  /-- Returned local contexts satisfy all of the expected properties. -/
  myLocalCtxOut : MyLocalContext LocalCtxOut

  /-- The type of formatting data returned from operations. -/
  FormatOut : Type

  /-- Returned formatting datums satisfy all of the expected properties. -/
  myFormat : MyFormat FormatOut

  /-- Fail the monad in the context of a given tactic. -/
  throwTacticEx
    {α N mvId : Type} [MyName N] [MyMVarId mvId]
    (tacticName : N) (goal : mvId) (msg : Lean.MessageData) : M α

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
  isDefEq {E₁ E₂ : Type} [MyExpr E₁] [MyExpr E₂] : E₁ → E₂ → M Bool

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

  /-- Attempt to deduce the type of an expression. -/
  inferType {E : Type} [MyExpr E] : E → M ExprOut

  /-- Evalute an expression to its normal form. -/
  reduce {E : Type} [MyExpr E] : E → M ExprOut

  /--
  Render an expression into a formatting directive, for human-readable display.
  -/
  prettyPrint {E : Type} [MyExpr E] : E → M FormatOut

  /-- Interpret a metavariable action with the given transparency mode. -/
  withTransparency {T α : Type} [MyTransparencyMode T] : T → M α → M α

  /--
  Construct an application expression, inferring implicit and instance
  arguments.
  -/
  mkAppM
    {N E : Type} {S : Type → Type} [MyName N] [MyExpr E] [MyFinSeq S]
    (f : N) (explicitArgs : S E) : M E

  /--
  Construct an application expression, inferring the arguments that are given
  as `none` values.
  -/
  mkAppOptM
    {N E : Type} {S : Type → Type} [MyName N] [MyExpr E] [MyFinSeq S]
    (f : N) (args : S (Option E)) : M E

  /--
  Interpret a metavariable action with the given temporary local variable.
  -/
  withLocalDecl
    {α N E : Type} [MyName N] [MyExpr E]
    (name : N) (type : E) (k : FVarIdOut → M α) : M α

  /--
  Abstract the given free variable and metavariable expressions from the given
  body expression, producing a lambda expression.
  -/
  mkLambdaFVars
    {E : Type} {S : Type → Type} [MyExpr E] [MyFinSeq S]
    (args : S E) (body : E) : M E

  /--
  Abstract the given free variable and metavariable expressions from the given
  body expression, producing a forall expression.
  -/
  mkForallFVars
    {E : Type} {S : Type → Type} [MyExpr E] [MyFinSeq S]
    (args : S E) (body : E) : M E

  /-- Construct the propositional equality between the given expressions. -/
  mkEq {E : Type} [MyExpr E] (e₁ e₂ : E) : M E

  /--
  Creates metavariables for the arguments of a forall expression, and populates
  the body with them. Returns the argument metavariables and the body.
  -/
  forallMetaTelescopeReducing
    {E : Type} [MyExpr E] (e : E) : M (Array ExprOut × ExprOut)

instance mymetam_metam_inst : MyMetaM Lean.MetaM := {
  MVarIdOut := Lean.MVarId
  myMVarIdOut := inferInstance
  FVarIdOut := Lean.FVarId
  myFVarIdOut := inferInstance
  ExprOut := Lean.Expr
  myExprOut := inferInstance
  LocalCtxOut := Lean.LocalContext
  myLocalCtxOut := inferInstance
  FormatOut := Std.Format
  myFormat := inferInstance
  throwTacticEx := λ name goalId msg =>
    Lean.Meta.throwTacticEx (MyName.toName name) (MyMVarId.toMVarId goalId) msg
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
  inferType := Lean.Meta.inferType ∘ MyExpr.toExpr
  reduce := Lean.Meta.reduce ∘ MyExpr.toExpr
  prettyPrint := Lean.Meta.ppExpr ∘ MyExpr.toExpr
  withTransparency :=
    Lean.Meta.withTransparency ∘ MyTransparencyMode.toTransparencyMode
  mkAppM := λ n es =>
    let n' := MyName.toName n
    let es' := ((MyFinSeq.toList es).map MyExpr.toExpr).toArray
    return MyExpr.fromExpr (← Lean.Meta.mkAppM n' es')
  mkAppOptM := λ n eos =>
    let n' := MyName.toName n
    let eos' := ((MyFinSeq.toList eos).map (Option.map MyExpr.toExpr)).toArray
    return MyExpr.fromExpr (← Lean.Meta.mkAppOptM n' eos')
  withLocalDecl := λ n t k =>
    -- Can't avoid `fvarId!` here, `fvExpr` is baked into Lean's data structures
    let k' := λ fvExpr => k fvExpr.fvarId!
    Lean.Meta.withLocalDecl (MyName.toName n) .default (MyExpr.toExpr t) k'
  mkLambdaFVars := λ args body =>
    let args' := ((MyFinSeq.toList args).map MyExpr.toExpr).toArray
    let body' := MyExpr.toExpr body
    return MyExpr.fromExpr (← Lean.Meta.mkLambdaFVars args' body')
  mkForallFVars := λ args body =>
    let args' := ((MyFinSeq.toList args).map MyExpr.toExpr).toArray
    let body' := MyExpr.toExpr body
    return MyExpr.fromExpr (← Lean.Meta.mkForallFVars args' body')
  mkEq := λ e₁ e₂ =>
    let e₁' := MyExpr.toExpr e₁
    let e₂' := MyExpr.toExpr e₂
    return MyExpr.fromExpr (← Lean.Meta.mkEq e₁' e₂')
  forallMetaTelescopeReducing := λ e => do
    let expr := MyExpr.toExpr e
    let (args, _, body) ← Lean.Meta.forallMetaTelescopeReducing expr
    return (args, body)
}

namespace MyMetaM

variable {M : Type → Type} [MyMetaM M]

instance mymvarid_mvaridout_inst : MyMVarId (MVarIdOut M) := myMVarIdOut

instance myfvarid_mfvaridout_inst : MyFVarId (FVarIdOut M) := myFVarIdOut

instance myexpr_exprout_inst : MyExpr (ExprOut M) := myExprOut

instance mylocalcontext_localctxout_inst : MyLocalContext (LocalCtxOut M) :=
  myLocalCtxOut

end Lean4Metaprog.MyMetaM
