import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceInduction
import YesMetaZFC.Automation.ObjectBoundedReflection

/-! # 实际源公式的内部强归纳

对“所有较小输入满足正文”的有界全称公式使用普通内部归纳。
最终阶段对应只要求正文在自然数上成立，不假定外部良基性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInduction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem strong_induction (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {parameters : SetContext} (body : SetOpenFormula (.set :: parameters))
    (args : Values 𝒩.Carrier parameters)
    (hAgreement : ∀ input, mem 𝒩 input (w 𝒩) →
      (body.satisfies (templateEnv (.cons input args) : Env 𝒩 [] (.set :: parameters)) ↔
        body.satisfies (templateEnv (.cons input args) : Env (canonical h𝒩) [] (.set :: parameters))))
    (hStep : ∀ input, mem 𝒩 input (w 𝒩) →
      (∀ previous, mem 𝒩 previous input → body.satisfies (templateEnv (.cons previous args))) →
        body.satisfies (templateEnv (.cons input args))) :
    ∀ input, mem 𝒩 input (w 𝒩) → body.satisfies (templateEnv (.cons input args)) := by
  have hSem (ℳ : Structure.{0,0,0,x} signature) (values : Values ℳ.Carrier parameters) (limit : ℳ.Carrier .set) :
      (ObjectBoundedReflection.allBody body).satisfies (templateEnv (.cons limit values) : Env ℳ [] (.set :: parameters)) ↔
        ∀ input, mem ℳ input limit → body.satisfies (templateEnv (.cons input values)) := by
    have he (input : ℳ.Carrier .set) : (templateEnv values : Env ℳ [] parameters).pushFree input = templateEnv (.cons input values) := by
      apply Env.ext
      · intro sort entry; cases entry
      · intro sort entry; cases entry <;> rfl
    rw [← he limit]
    unfold ObjectBoundedReflection.allBody ObjectBoundedReflection.allAt
    simp only [Formula.satisfies, Arguments.eval, Term.eval_weakenBound]
    apply forall_congr'; intro input
    apply imp_congr_right; intro _
    change (body.abstractFreeTop.weakenFree SetSort.set).satisfies
      (((templateEnv values : Env ℳ [] parameters).pushBound input).pushFree limit) ↔ _
    rw [Formula.satisfies_weakenFree, Formula.satisfies_abstractFreeTop, he]
  have hAll : ∀ limit, mem 𝒩 limit (w 𝒩) →
      (ObjectBoundedReflection.allBody body).satisfies (templateEnv (.cons limit args) : Env 𝒩 [] (.set :: parameters)) := by
    apply induction h𝒩 (ObjectBoundedReflection.allBody body) args
    · intro limit hl
      rw [hSem, hSem]
      apply forall_congr'; intro input
      apply imp_congr_right; intro hi
      exact hAgreement input (member_natural h𝒩 hl hi)
    · apply (hSem _ _ _).mpr
      intro input hi; exact False.elim (empty_spec h𝒩 input hi)
    · intro limit hl hPrevious
      have hp := (hSem _ _ _).mp hPrevious
      apply (hSem _ _ _).mpr
      intro input hi
      rcases (successor_spec h𝒩 limit input).mp hi with hi | rfl
      · exact hp input hi
      · exact hStep _ hl hp
  intro input hi
  exact hStep input hi ((hSem _ _ _).mp (hAll input hi))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInduction
