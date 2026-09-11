import YesMetaZFC.Model.Henkin.TruthLemma
import YesMetaZFC.Model.Henkin.Schedule
import YesMetaZFC.Model.Henkin.Conservativity

/-!
# 内在 Henkin 签名上的强完备性

本模块先收束已经处于 `HSignature σ` 中、且背景公理不含见证常量的理论。典范模型
直接解释该内在签名，不再携带 admissibility、句子闭合证书或任意变量环境。

任意原签名理论到本终点的保守提升属于独立的签名迁移层，不在这里恢复旧兼容接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin

open HenkinSignature

universe u v w x

namespace CanonicalModel

/-- 任意 Henkin 完成结果的典范模型都满足背景理论。 -/
theorem models_background {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)} {background : Background T}
    (result : Result background) :
    Theory.Models (model result) T := by
  intro sentence hSentence
  have hCandidate := result.contains_background hSentence
  simpa [Formula.TrueIn, canonical_env] using
    (truth_lemma result sentence).mpr hCandidate

end CanonicalModel

namespace Construction

noncomputable section

/-- 从空候选开始完成背景理论。 -/
def background_result {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (background : Background T) (schedule : Schedule σ) :
    Result background :=
  result (Stage.initial background) schedule

/-- 从目标否定开始完成背景理论。 -/
def refutation_result {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (background : Background T) (schedule : Schedule σ)
    (sentence : Sentence (HSignature σ))
    (hNotDerives : ¬ Derives T [] sentence) :
    Result background :=
  result (Stage.refutation_seed background sentence hNotDerives) schedule

/-- 反例完成结果保留种子中的目标否定。 -/
theorem refutation_result_contains_neg {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (background : Background T) (schedule : Schedule σ)
    (sentence : Sentence (HSignature σ))
    (hNotDerives : ¬ Derives T [] sentence) :
    (refutation_result background schedule sentence hNotDerives).candidate
      (.neg sentence) := by
  change
    candidate (Stage.refutation_seed background sentence hNotDerives)
      schedule (.neg sentence)
  exact candidate_of_initial (by
    simp [Stage.refutation_seed, Stage.seed])

end

end Construction

/-- 一致的无见证背景理论在公平调度下具有典范模型。 -/
theorem exists_model_of_background {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (background : Background T) (schedule : Schedule σ) :
    ∃ M : Structure.{u, max u v, w, max v w} (HSignature σ),
      Theory.Models M T := by
  let result := Construction.background_result background schedule
  exact
    ⟨CanonicalModel.model result,
      CanonicalModel.models_background result⟩

/-- 不可推导闭句由 seeded 典范模型给出真实反模型。 -/
theorem exists_countermodel_of_not_derives
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (background : Background T) (schedule : Schedule σ)
    (sentence : Sentence (HSignature σ))
    (hNotDerives : ¬ Derives T [] sentence) :
    ∃ M : Structure.{u, max u v, w, max v w} (HSignature σ),
      Theory.Models M T ∧ ¬ sentence.TrueIn M := by
  let result :=
    Construction.refutation_result
      background schedule sentence hNotDerives
  have hModels :
      Theory.Models (CanonicalModel.model result) T :=
    CanonicalModel.models_background result
  have hNegCandidate : result.candidate (.neg sentence) :=
    Construction.refutation_result_contains_neg
      background schedule sentence hNotDerives
  have hNegSatisfies :
      Formula.satisfies (CanonicalModel.canonical_env result)
        (.neg sentence) :=
    (CanonicalModel.truth_lemma result (.neg sentence)).mpr hNegCandidate
  exact
    ⟨CanonicalModel.model result, hModels, by
      simpa [Formula.TrueIn, CanonicalModel.canonical_env,
        Formula.satisfies] using hNegSatisfies⟩

/-- 无见证背景理论的强完备性。 -/
theorem strong_completeness {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)} (schedule : Schedule σ)
    (hAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ∀ sort index, ¬ Formula.usesWitness sort index sentence)
    {sentence : Sentence (HSignature σ)}
    (hEntails :
      Theory.SemanticallyEntails.{u, max u v, w, max v w}
        T sentence) :
    Derives T [] sentence := by
  apply Classical.byContradiction
  intro hNotDerives
  have hConsistent : Derives.Consistent T (free := []) [] := by
    intro hFalse
    exact hNotDerives (Derives.falsum_elim hFalse)
  let background : Background T :=
    ⟨hConsistent, hAvoids⟩
  rcases exists_countermodel_of_not_derives
      background schedule sentence hNotDerives with
    ⟨M, hModels, hRefutes⟩
  exact hRefutes (hEntails M hModels)

/-- 闭句推导给出任意固定模型 universe 上的语义蕴涵。 -/
theorem semantically_entails_of_derives
    {τ : Signature.{u, v, w}} {T : Theory τ}
    {sentence : Sentence τ} (hDerives : Derives T [] sentence) :
    Theory.SemanticallyEntails.{u, v, w, x} T sentence :=
  hDerives.semantically_entails

/-- 公平调度下，无见证理论的语义蕴涵与推导等价。 -/
theorem semantically_entails_iff_derives
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)} (schedule : Schedule σ)
    (hAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ∀ sort index, ¬ Formula.usesWitness sort index sentence)
    {sentence : Sentence (HSignature σ)} :
    Theory.SemanticallyEntails.{u, max u v, w, max v w} T sentence ↔
      Derives T [] sentence := by
  constructor
  · exact strong_completeness schedule hAvoids
  · exact semantically_entails_of_derives

/-- 公平调度下，无见证理论一致当且仅当它具有典范 universe 中的模型。 -/
theorem consistent_iff_exists_model
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)} (schedule : Schedule σ)
    (hAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ∀ sort index, ¬ Formula.usesWitness sort index sentence) :
    Derives.Consistent T (free := []) [] ↔
      ∃ M : Structure.{u, max u v, w, max v w} (HSignature σ),
        Theory.Models M T := by
  constructor
  · intro hConsistent
    exact exists_model_of_background ⟨hConsistent, hAvoids⟩ schedule
  · rintro ⟨M, hModels⟩ hFalse
    have hSatisfiesFalse :=
      hFalse.sound hModels Env.empty (by
        intro formula hFormula
        cases hFormula)
    simp [Formula.satisfies] at hSatisfiesFalse

end Henkin

/-! ## 原签名上的强完备性终点 -/

open HenkinSignature

/-- 任意原签名理论在公平 Henkin 调度下满足强完备性。 -/
theorem strong_completeness {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} (schedule : Henkin.Schedule σ)
    {sentence : Sentence σ}
    (hEntails :
      Theory.SemanticallyEntails.{u, v, w, max v w} T sentence) :
    Derives T [] sentence := by
  apply Derives.lowerHenkin
  exact Henkin.strong_completeness schedule
    (fun hSentence => liftTheory_avoids hSentence)
    (semanticallyEntails_lift hEntails)

/-- 公平 Henkin 调度下，原签名语义蕴涵与标准 Hilbert 推导等价。 -/
theorem semantically_entails_iff_derives
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (schedule : Henkin.Schedule σ)
    {sentence : Sentence σ} :
    Theory.SemanticallyEntails.{u, v, w, max v w} T sentence ↔
      Derives T [] sentence := by
  constructor
  · exact strong_completeness schedule
  · exact Henkin.semantically_entails_of_derives

/-- 公平 Henkin 调度下，原签名理论一致当且仅当它具有典范 universe 中的模型。 -/
theorem consistent_iff_exists_model
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (schedule : Henkin.Schedule σ) :
    Derives.Consistent T (free := []) [] ↔
      ∃ M : Structure.{u, v, w, max v w} σ, Theory.Models M T := by
  constructor
  · intro hConsistent
    have hLiftConsistent :
        Derives.Consistent (liftTheory T) (free := []) [] := by
      intro hFalse
      exact hConsistent (Derives.lowerHenkin hFalse)
    rcases (Henkin.consistent_iff_exists_model schedule
        (fun hSentence => liftTheory_avoids hSentence)).mp
        hLiftConsistent with ⟨M, hModels⟩
    exact ⟨henkinReduct M, models_henkinReduct hModels⟩
  · rintro ⟨M, hModels⟩ hFalse
    have hSatisfiesFalse :=
      hFalse.sound hModels Env.empty (by
        intro formula hFormula
        cases hFormula)
    simp [Formula.satisfies] at hSatisfiesFalse

end Completeness
end FirstOrder
end Logic
end YesMetaZFC
