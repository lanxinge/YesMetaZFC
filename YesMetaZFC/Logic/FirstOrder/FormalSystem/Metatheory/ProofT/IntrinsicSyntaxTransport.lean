import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-!
# 内在语法替换运输

本层只处理语法核本身的上下文运输。无 bound 变量项嵌入任意 bound 上下文后，
再执行类型化替换，结果等于直接对原项执行 free 替换；该事实是所有闭式对象
载体进入模板和量词闭包时的共同快路径。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

set_option autoImplicit false

universe u v w

@[simp] theorem Term.embedBoundClosed_substituteMapped
    {σ : Signature.{u, v, w}}
    {sourceBound targetBound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (term : Term σ [] sourceFree sort)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    (term.embedBoundClosed sourceBound).substituteMapped
        boundSubstitution freeSubstitution =
      term.substituteMapped VariableSubstitution.empty freeSubstitution := by
  exact Term.rec
    (motive_1 := fun sort term =>
      ∀ (sourceBound targetBound targetFree : SortContext σ)
        (boundSubstitution :
          VariableSubstitution σ sourceBound targetBound targetFree)
        (freeSubstitution :
          VariableSubstitution σ sourceFree targetBound targetFree),
        (term.embedBoundClosed sourceBound).substituteMapped
            boundSubstitution freeSubstitution =
          term.substituteMapped VariableSubstitution.empty freeSubstitution)
    (motive_2 := fun sorts arguments =>
      ∀ (sourceBound targetBound targetFree : SortContext σ)
        (boundSubstitution :
          VariableSubstitution σ sourceBound targetBound targetFree)
        (freeSubstitution :
          VariableSubstitution σ sourceFree targetBound targetFree),
        (arguments.embedBoundClosed sourceBound).substituteMapped
            boundSubstitution freeSubstitution =
          arguments.substituteMapped VariableSubstitution.empty freeSubstitution)
    (fun entry => nomatch entry)
    (fun entry => by
      intro sourceBound targetBound targetFree boundSubstitution freeSubstitution
      rw [Term.embedBoundClosed_fvar]
      rfl)
    (fun function arguments ih => by
      intro sourceBound targetBound targetFree boundSubstitution freeSubstitution
      simp only [Term.embedBoundClosed_app, Term.substituteMapped]
      rw [ih sourceBound targetBound targetFree boundSubstitution freeSubstitution])
    (by
      intro sourceBound targetBound targetFree boundSubstitution freeSubstitution
      rw [Arguments.embedBoundClosed_nil]
      rfl)
    (fun head tail ihHead ihTail => by
      intro sourceBound targetBound targetFree boundSubstitution freeSubstitution
      simp only [Arguments.embedBoundClosed_cons, Arguments.substituteMapped]
      rw [ihHead sourceBound targetBound targetFree boundSubstitution freeSubstitution,
        ihTail sourceBound targetBound targetFree boundSubstitution freeSubstitution])
    term sourceBound targetBound targetFree boundSubstitution freeSubstitution

/-- 空 bound 源在恒等 free 替换下直接形成目标 bound 闭嵌入。 -/
@[simp] theorem Term.substituteMapped_empty_freeId
    {σ : Signature.{u, v, w}}
    {targetBound free : SortContext σ}
    {sort : σ.SortSymbol}
    (term : Term σ [] free sort) :
    term.substituteMapped
        (VariableSubstitution.empty :
          VariableSubstitution σ [] targetBound free)
        VariableSubstitution.freeId =
      term.embedBoundClosed targetBound := by
  have h := Term.embedBoundClosed_substituteMapped
    (sourceBound := targetBound) (targetBound := targetBound)
    term VariableSubstitution.boundId VariableSubstitution.freeId
  calc
    term.substituteMapped
        (VariableSubstitution.empty :
          VariableSubstitution σ [] targetBound free)
        VariableSubstitution.freeId =
        (term.embedBoundClosed targetBound).substituteMapped
          VariableSubstitution.boundId VariableSubstitution.freeId := h.symm
    _ = term.embedBoundClosed targetBound :=
      Term.substituteMapped_id (term.embedBoundClosed targetBound)

/-- 空 bound 上下文到自身的替换直接命中恒等快路径。 -/
@[simp] theorem Term.substituteMapped_empty_freeId_eq_self
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    {sort : σ.SortSymbol}
    (term : Term σ [] free sort) :
    term.substituteMapped
        (VariableSubstitution.empty :
          VariableSubstitution σ [] [] free)
        VariableSubstitution.freeId = term := by
  exact Term.substituteMapped_empty_freeId term

/-- 无 bound 公式上的空替换同样直接保持原公式。 -/
@[simp] theorem Formula.substituteMapped_empty_freeId_eq_self
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (formula : Formula σ [] free) :
    formula.substituteMapped
        (VariableSubstitution.empty :
          VariableSubstitution σ [] [] free)
        VariableSubstitution.freeId = formula := by
  calc
    _ = formula.substituteMapped
        VariableSubstitution.boundId VariableSubstitution.freeId := by
      apply Formula.substituteMapped_congr
      · intro sort entry
        exact nomatch entry
      · intro sort entry
        rfl
    _ = formula := Formula.substituteMapped_id formula

/-- 恒等 free 替换保持闭 bound 嵌入，连续 witness 实例化因此不展开原 AST。 -/
@[simp] theorem Term.embedBoundClosed_substituteMapped_freeId
    {σ : Signature.{u, v, w}}
    {sourceBound targetBound free : SortContext σ}
    {sort : σ.SortSymbol}
    (term : Term σ [] free sort)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound free) :
    (term.embedBoundClosed sourceBound).substituteMapped
        boundSubstitution VariableSubstitution.freeId =
      term.embedBoundClosed targetBound := by
  rw [Term.embedBoundClosed_substituteMapped]
  exact Term.substituteMapped_empty_freeId term

/-- 提升替换后立即实例化顶部 binder，等价于一次扩展后的直接替换。 -/
@[simp] theorem Formula.substituteMapped_liftBound_instantiateTop
    {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree)
    (witness : Term σ targetBound targetFree introduced)
    (body : Formula σ (introduced :: sourceBound) sourceFree) :
    (body.substituteMapped
        (VariableSubstitution.liftBound introduced boundSubstitution)
        (VariableSubstitution.weakenBound introduced freeSubstitution)).instantiateTop
          witness =
      body.substituteMapped
        (VariableSubstitution.cons witness boundSubstitution)
        freeSubstitution := by
  change
    (body.substituteMapped
        (VariableSubstitution.liftBound introduced boundSubstitution)
        (VariableSubstitution.weakenBound introduced freeSubstitution)).substituteMapped
          (VariableSubstitution.instantiateTop witness)
          VariableSubstitution.freeId =
      body.substituteMapped
        (VariableSubstitution.cons witness boundSubstitution)
        freeSubstitution
  rw [Formula.substituteMapped_comp]
  apply Formula.substituteMapped_congr
  · intro resultSort entry
    cases entry with
    | here =>
        rfl
    | there previous =>
        exact Term.instantiateTop_weakenBound
          witness (boundSubstitution previous)
  · intro resultSort entry
    exact Term.instantiateTop_weakenBound
      witness (freeSubstitution entry)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
