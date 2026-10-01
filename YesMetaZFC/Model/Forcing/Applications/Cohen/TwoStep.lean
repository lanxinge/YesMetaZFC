import YesMetaZFC.Model.Forcing.TwoStep.Generic.Composition
import YesMetaZFC.Model.Forcing.Applications.Cohen.Add
import YesMetaZFC.Model.Forcing.Applications.Cohen.Names
import YesMetaZFC.Model.Forcing.TwoStep.Embedding

/-! # 扩张内部 Cohen 偏序的后继装配实例

添加量 κ 是任意首阶段名称。一次生成条件集与关系名称，对每个正条件装配实际
二步偏序，并对每个首阶段泛型证明其解释为添加指定量实数的 Cohen 偏序。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
include O hZFC

/-- 一次取得全局 Cohen 后继名称、任意正条件下的二步序及全部泛型解释的添加成果。 -/
theorem cohen_step_l {κ : M.Domain} (hκ : Name_d M B κ) :
    ∃ A T t, Cohen_names_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R z κ A T t ∧
      (∀ b, M.mem b B → b ≠ z →
        ∃ W C S, Two_step_d M B R z b A T W C S ∧ Cond_order_d M C S C ∧ Name_pool_d M B A t W ∧
          (∃ x, KPair_d M x b t ∧ M.mem x C ∧ ∀ y, M.mem y C → Entry_d M y x S) ∧
          ∃ P F, (∀ p, M.mem p P ↔ Below_d M B R z p b) ∧
            (∀ p x, Entry_d M p x F ↔ Below_d M B R z p b ∧ KPair_d M x p t) ∧
            Reg_embed_d M P R z C S C F) ∧
      ∀ U, ∀ hU : Generic_d M B R z U,
        let E := extension_l M (ZFC.models_zf_l hZFC) B R z U
        ∃ K Q D : E.Domain, Qval_d M B R z U κ K ∧ Qval_d M B R z U A Q ∧ Qval_d M B R z U T D ∧
          ∃ ω, E.IsOmega ω ∧ ∃ L : Cond_order_d E Q D Q,
            Ccc_d E (kpair_interpretation_l E (preserves_zfc_l O hZFC hU).1
              (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l (preserves_zfc_l O hZFC hU))))) ω Q D Q ∧
            ∀ V, ∀ hV : Generic_d E Q D Q V, Cohen_result_d L (preserves_zfc_l O hZFC hU) hV ω K := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨A, T, t, hNames, _⟩ := cohen_names_l O hZF hκ
  obtain ⟨hA, hT, ht⟩ := hNames.1
  have step b (hb : M.mem b B) (hz : b ≠ z) :
      ∃ W C S, Two_step_d M B R z b A T W C S ∧ Cond_order_d M C S C ∧ Name_pool_d M B A t W ∧
        (∃ x, KPair_d M x b t ∧ M.mem x C ∧ ∀ y, M.mem y C → Entry_d M y x S) ∧
        ∃ P F, (∀ p, M.mem p P ↔ Below_d M B R z p b) ∧
          (∀ p x, Entry_d M p x F ↔ Below_d M B R z p b ∧ KPair_d M x p t) ∧
          Reg_embed_d M P R z C S C F := by
    obtain ⟨W, C, S, h, L, hHull, hx⟩ :=
      two_step_pointed_l O hZF hA hT ht hb hz (hNames.2.2.2.1 b hb hz) (hNames.2.2.2.2 b hb hz)
    obtain ⟨P, F, hP, hF, he⟩ := two_step_embed_l O hZF h L hT hHull.right (hNames.2.2.2.2 b hb hz)
    exact ⟨W, C, S, h, L, hHull, hx, P, F, hP, hF, he⟩
  refine ⟨A, T, t, hNames, step, fun U hU => ?_⟩
  let E := extension_l M hZF B R z U
  have hE := preserves_zfc_l O hZFC hU
  let I := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hE)))
  obtain ⟨K, hK⟩ := name_value_l (R := R) (z := z) (U := U) hκ
  obtain ⟨Q, hQ⟩ := name_value_l (R := R) (z := z) (U := U) hA
  obtain ⟨D, hD⟩ := name_value_l (R := R) (z := z) (U := U) hT
  have hρ : Env_val_d hZF (cohen_env_l κ A T) (cohen_env_l (M := E) K Q D) := by
    intro t
    cases t with
    | free _ => exact hK
    | bound i => exact Fin.cases hQ (Fin.cases hD (fun _ => hK)) i
  obtain ⟨p, hUp⟩ := hU.inhabited
  have h := (forcing_truth_l O hZF hU _ (cohen_m_freeClosed _ _ _ rfl rfl rfl) _ _ hρ).mp
    ⟨p, hUp, hNames.2.2.1 p (hU.proper p hUp).1 (hU.proper p hUp).2⟩
  have h := (cohen_sat_l I hE.1 _ _ _ _).mp h
  obtain ⟨ω, hω, L, _, hccc, hr⟩ := cohen_spec_forcing_l E hE h
  exact ⟨K, Q, D, hK, hQ, hD, ω, hω, L, hccc, hr⟩

end YesMetaZFC.Model.Forcing.Internal
