import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # 普通 Hilbert 推导中的真不可定义性

逻辑核心只消费一个否定固定点，不要求可导性条件或真值反射。
句法合同要求全部真值等价式可证；语义合同分别覆盖闭句真值和固定参数赋值下的开放公式真值。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.Tarski
set_option autoImplicit false
universe u v w x
variable {σ : Signature.{u, v, w}} {T : Theory σ}

/-- 同一候选算子的全部真值等价式在理论中可证。 -/
def TruthSchema_m {free : SortContext σ} (T : Theory σ)
    (F : OpenFormula σ free → OpenFormula σ free) : Prop :=
  ∀ φ, Derives T [] (.iff (F φ) φ)

/-- 候选算子在指定模型中与全部闭句同真。 -/
def DefinesTruth_m (ℳ : Structure.{u, v, w, x} σ) (F : Sentence σ → Sentence σ) : Prop :=
  ∀ φ, (F φ).TrueIn ℳ ↔ φ.TrueIn ℳ

/-- 在同一任意参数赋值下，候选算子与全部开放公式同真。 -/
def DefinesSatisfaction_m {ℳ : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (env : Env ℳ [] free) (F : OpenFormula σ free → OpenFormula σ free) : Prop :=
  ∀ φ, (F φ).satisfies env ↔ φ.satisfies env

/-- 否定固定点使相应真值等价式可被理论反驳，无一致性前提。 -/
theorem liar_refutes_m {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} (h : Derives T Γ (.iff φ (.neg ψ))) :
    Derives T Γ (.neg (.iff ψ φ)) := by
  apply Derives.neg_intro
  have h₁ : Derives T (.iff ψ φ :: Γ) (.neg ψ) := by
    apply Derives.neg_intro
    have h₂ : Derives T (ψ :: .iff ψ φ :: Γ) ψ :=
      Derives.assumption List.mem_cons_self
    have h₃ := Derives.iff_elim_left
      (Derives.assumption (List.mem_cons_of_mem _ List.mem_cons_self)) h₂
    exact Derives.neg_elim h₂
      (Derives.iff_elim_left h.context_weaken_cons.context_weaken_cons h₃)
  exact Derives.neg_elim
    (Derives.iff_elim_right (Derives.assumption List.mem_cons_self)
      (Derives.iff_elim_right h.context_weaken_cons h₁)) h₁

theorem biconditional_unprovable_m {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} (h : Derives T Γ (.iff φ (.neg ψ)))
    (hT : Derives.Consistent T Γ) : ¬ Derives T Γ (.iff ψ φ) :=
  fun h₁ => hT (Derives.neg_elim h₁ (liar_refutes_m h))

theorem not_truth_schema_m {free : SortContext σ}
    {F : OpenFormula σ free → OpenFormula σ free} {φ : OpenFormula σ free}
    (h : Derives T [] (.iff φ (.neg (F φ))))
    (hT : Derives.Consistent T ([] : Context σ free)) : ¬ TruthSchema_m T F :=
  fun h₁ => biconditional_unprovable_m h hT (h₁ φ)

/-- 模型可靠性直接排除真值对应，不另外假定理论一致或模型标准。 -/
theorem not_defines_truth_m {ℳ : Structure.{u, v, w, x} σ}
    (hℳ : Theory.Models ℳ T) {F : Sentence σ → Sentence σ} {φ : Sentence σ}
    (h : Derives T [] (.iff φ (.neg (F φ)))) : ¬ DefinesTruth_m ℳ F :=
  fun h₁ => (liar_refutes_m h).semantically_entails ℳ hℳ (h₁ φ)

theorem not_defines_satisfaction_m {ℳ : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (hℳ : Theory.Models ℳ T) (env : Env ℳ [] free)
    {F : OpenFormula σ free → OpenFormula σ free} {φ : OpenFormula σ free}
    (h : Derives T [] (.iff φ (.neg (F φ)))) : ¬ DefinesSatisfaction_m env F :=
  fun h₁ => (liar_refutes_m h).sound hℳ env (by intro ψ hψ; cases hψ) (h₁ φ)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.Tarski
