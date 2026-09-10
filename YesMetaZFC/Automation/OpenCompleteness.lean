import YesMetaZFC.Automation.SemanticTransfer
import YesMetaZFC.Automation.ModelClosure

/-! # 任意有限自由上下文的模型完备性接口

统一使用全称闭包连接闭句完备性；不要求语言含有闭项。
-/
namespace YesMetaZFC.Automation.SemanticTransfer
open Logic Logic.FirstOrder
set_option autoImplicit false
variable {σ : Signature.{0,0,0}} [DecidableEq σ.SortSymbol]

theorem derives_open_m {T : Theory σ} (schedule : Completeness.Henkin.Schedule σ)
    {free : SortContext σ} {φ : OpenFormula σ free}
    (h : ∀ (ℳ : Structure.{0,0,0,0} σ), Theory.Models ℳ T →
      ∀ env : Env ℳ [] free, φ.satisfies env) : Derives T [] φ := by
  have hClosed : Derives T [] (Metatheory.Formula.forall_close φ) := by
    apply Completeness.strong_completeness schedule
    intro ℳ hℳ
    exact (ModelClosure.forall_close_iff φ).mpr (h ℳ hℳ)
  apply Metatheory.Derives.forall_close_open φ
  simpa [Formula.fromSentence, Renaming.emptyFree] using hClosed

/-- 通过模型非空性保留开放上下文一致性，纯关系语言也适用。 -/
theorem consistent_open_m {T : Theory σ} (schedule : Completeness.Henkin.Schedule σ)
    (hT : Derives.Consistent T ([] : Context σ [])) (free : SortContext σ) :
    Derives.Consistent T ([] : Context σ free) := by
  obtain ⟨ℳ, hℳ⟩ := (Completeness.consistent_iff_exists_model schedule).mp hT
  let env : Env ℳ [] free :=
    ⟨Assignment.empty, fun {s} _ => Classical.choice (ℳ.nonempty s)⟩
  intro h
  exact h.sound hℳ env (by intro ψ hψ; cases hψ)

end YesMetaZFC.Automation.SemanticTransfer
