import YesMetaZFC.Model.Henkin.StrongCompleteness

/-! # 通过模型扩张和约化传输一致性与独立性

扩张负责一致性，约化负责把目标推导反射回源理论。句子真值对应只要求在指定句子上
成立，不把带条件定义的任意非法输入偷偷强化成全语言定义扩张。
-/
namespace YesMetaZFC.Automation.SemanticTransfer
open Logic Logic.FirstOrder
set_option autoImplicit false
variable {σ τ : Signature.{0, 0, 0}} {S : Theory σ} {T : Theory τ}

/-- 每个目标理论模型都允许一个源理论模型；只用于一致性传输。 -/
def Expands (S : Theory σ) (T : Theory τ) : Prop :=
  ∀ ℳ : Structure.{0, 0, 0, 0} τ, Theory.Models ℳ T →
    ∃ 𝒩 : Structure.{0, 0, 0, 0} σ, Theory.Models 𝒩 S

/-- 源模型的具体目标约化以及公理保持。 -/
structure Reduction (S : Theory σ) (T : Theory τ) where
  model : Structure.{0, 0, 0, 0} σ → Structure.{0, 0, 0, 0} τ
  models : ∀ ℳ, Theory.Models ℳ S → Theory.Models (model ℳ) T

/-- 指定闭句在约化前后真值一致。 -/
def Reduction.Agrees (reduction : Reduction S T) (source : Sentence σ) (target : Sentence τ) : Prop :=
  ∀ ℳ, Theory.Models ℳ S → (target.TrueIn (reduction.model ℳ) ↔ source.TrueIn ℳ)

theorem consistent_of_expands [DecidableEq τ.SortSymbol]
    (schedule : Completeness.Henkin.Schedule τ) (hExpansion : Expands S T)
    (hConsistent : Derives.Consistent T ([] : Context τ [])) :
    Derives.Consistent S ([] : Context σ []) := by
  obtain ⟨ℳ, hℳ⟩ := (Completeness.consistent_iff_exists_model schedule).mp hConsistent
  obtain ⟨𝒩, h𝒩⟩ := hExpansion ℳ hℳ
  intro hFalse
  exact hFalse.semantically_entails 𝒩 h𝒩

/-- 句子级真值对应经通用强完备性给出所需方向的推导反射。 -/
theorem Reduction.reflect [DecidableEq σ.SortSymbol]
    (reduction : Reduction S T) (schedule : Completeness.Henkin.Schedule σ)
    {source : Sentence σ} {target : Sentence τ} (hAgrees : reduction.Agrees source target)
    (hDerives : Derives T [] target) : Derives S [] source := by
  apply Completeness.strong_completeness schedule
  intro ℳ hℳ
  exact (hAgrees ℳ hℳ).mp (hDerives.semantically_entails (reduction.model ℳ) (reduction.models ℳ hℳ))

theorem Reduction.agrees_neg (reduction : Reduction S T)
    {source : Sentence σ} {target : Sentence τ} (hAgrees : reduction.Agrees source target) :
    reduction.Agrees (.neg source) (.neg target) :=
  fun ℳ hℳ => not_congr (hAgrees ℳ hℳ)

/-- 只要求源独立性定理和两种模型合同，最终前提是目标理论的一致性。 -/
theorem independent [DecidableEq σ.SortSymbol] [DecidableEq τ.SortSymbol]
    (sourceSchedule : Completeness.Henkin.Schedule σ) (targetSchedule : Completeness.Henkin.Schedule τ)
    (hExpansion : Expands S T) (reduction : Reduction S T)
    {source : Sentence σ} {target : Sentence τ} (hAgrees : reduction.Agrees source target)
    (hIndependent : Derives.Consistent S ([] : Context σ []) →
      (¬ Derives S [] source) ∧ (¬ Derives S [] (.neg source)))
    (hConsistent : Derives.Consistent T ([] : Context τ [])) :
    (¬ Derives T [] target) ∧ (¬ Derives T [] (.neg target)) := by
  obtain ⟨hPositive, hNegative⟩ := hIndependent (consistent_of_expands targetSchedule hExpansion hConsistent)
  exact ⟨fun h => hPositive (reduction.reflect sourceSchedule hAgrees h),
    fun h => hNegative (reduction.reflect sourceSchedule (reduction.agrees_neg hAgrees) h)⟩

end YesMetaZFC.Automation.SemanticTransfer
