import YesMetaZFC.Model.Forcing.CH
import YesMetaZFC.Model.Forcing.NotCH
import YesMetaZFC.Model.SetTheory.ProjectSoundness

/-! # 原 ZFC 上的 CH 独立性

同一可数地模型分别作可数闭塌缩和 Cohen 添加，得到 CH 的两侧模型。
原 Project 句子经既有纯语言翻译进入原 Derives 核，模型可靠性排除双侧可推导性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

/-- 同一任意可数地模型的两侧力迫模型；允许外部非良基与非标准内部 ω。 -/
theorem ch_extensions_l (M : SetTheory.Structure.{u}) (hZFC : M.Models ZFC)
    (e : Nat → M.Domain) (he : Function.Surjective e) :
    ∃ N₀ N₁ : SetTheory.Structure.{u}, N₀.Models (ZFC_CH kpair_convention_l) ∧
      N₁.Models (ZFC_not_CH kpair_convention_l) := by
  obtain ⟨B, R, U, _, _, hCH⟩ := ch_extension_l M hZFC e he
  obtain ⟨C, S, V, _, _, hnCH⟩ := not_ch_extension_l M hZFC e he
  exact ⟨extension_l M (ZFC.models_zf_l hZFC) B R B U,
    extension_l M (ZFC.models_zf_l hZFC) C S C V, hCH, hnCH⟩

/-- 原 ZFC 加 CH 与加 ¬CH 都一致；实际两侧模型无需额外模型存在前提。 -/
theorem ch_consistency_l : Consistent (ZFC_CH kpair_convention_l) ∧ Consistent (ZFC_not_CH kpair_convention_l) := by
  obtain ⟨M, hM⟩ := ch_model_l
  obtain ⟨N, hN⟩ := not_ch_model_l
  exact ⟨FirstOrderSemantics.consistent_l hM, FirstOrderSemantics.consistent_l hN⟩

/-- 在原 Project／纯隶属 Derives 核中，ZFC 既不证明 CH，也不证明其否定。 -/
theorem ch_independent_l : ¬ Derives ZFC (ch_sentence_l kpair_convention_l) ∧
    ¬ Derives ZFC (not_ch_sentence_l kpair_convention_l) := by
  have incompatible {M : SetTheory.Structure.{1}} (hc : M.SatisfiesSentence (ch_sentence_l kpair_convention_l))
      (hn : M.SatisfiesSentence (not_ch_sentence_l kpair_convention_l)) : False := by
    obtain ⟨a⟩ := M.nonempty
    exact (Formula.satisfies_neg_iff (⟨Fin.elim0, fun _ => a⟩ : Env M 0) _).mp (hn (fun _ => a))
      (hc (fun _ => a))
  constructor
  · intro h
    obtain ⟨M, hM⟩ := not_ch_model_l
    exact incompatible (FirstOrderSemantics.sound_l ⟨hM.1, fun s hs => hM.2 s (Or.inl hs)⟩ h)
      (hM.2 _ (Or.inr rfl))
  · intro h
    obtain ⟨M, hM⟩ := ch_model_l
    exact incompatible (hM.2 _ (Or.inr rfl))
      (FirstOrderSemantics.sound_l ⟨hM.1, fun s hs => hM.2 s (Or.inl hs)⟩ h)

end YesMetaZFC.Model.Forcing.Internal
