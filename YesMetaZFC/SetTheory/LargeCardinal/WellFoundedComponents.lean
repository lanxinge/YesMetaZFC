import YesMetaZFC.SetTheory.LargeCardinal.SupportConstruction
import YesMetaZFC.SetTheory.LargeCardinal.ComponentWellFounded

/-! # 武丁基数产生的实际良基分量族

保留同一测度族的任意坐标协调与共同纤维性质，并自动为每个分量构造良基商。
源关系可位于任意秩；原强嵌入只用于产生测度，不作用于代表函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_wf_components_l (hM : M.Models ZFDC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFDC.models_zf_l hM))) δ) :
    let I := kp_pair_l (ZF.modelsKP (ZFDC.models_zf_l hM))
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧
      ∀ L, M.mem L δ → M.MemberSubset ω L → ∃ ν N B j W k S F,
        Wd_witness_d I ω δ X A κ ν N B j W k ∧ M.mem L k ∧
        Fseq_space_d I ω L S ∧ Es_family_d I j κ L S F ∧ Es_coherent_d I ω κ L F ∧
        (∀ H f, Ef_levels_d ω κ H → Es_fiber_d I ω L F H f → ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g) ∧
        ∀ a U, M.PairMember I a U F → ∃ n D, Fn0_d n L a ∧ (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧
          Ed_filter_d I j a D U ∧ FilterZF.Maximal_d (ℳ := M) D U ∧ Ed_complete_d κ D U ∧
          ∀ Q R, (∃ x, M.mem x Q) → Wf_rel_d Q R → ∃ c G q C T,
            (∀ f, M.mem f G ↔ Fn0_d D Q f) ∧ Rp_model_d I D Q U R c G q C T ∧ Wf_rel_d C T := by
  let hZF := ZFDC.models_zf_l hM
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, components⟩ := woodin_components_l I hZF hd
  refine ⟨ω, X, hω, hX, fun A hA => ?_⟩
  obtain ⟨κ, hκ, _, hωκ, family⟩ := components A hA
  refine ⟨κ, hκ, fun L hL hωL => ?_⟩
  obtain ⟨ν, N, B, j, W, k, S, F, hw, _, hLk, hS, _, hF, component, coherent, fiber⟩ := family L hL hωL
  refine ⟨ν, N, B, j, W, k, S, F, hw, hLk, hS, hF, coherent, fiber, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hD, hu, hU, hc, models⟩ := component a U ha
  refine ⟨n, D, hn, hD, hu, hU, hc, fun Q R hQ hR => ?_⟩
  obtain ⟨c, G, q, C, T, hG, hm⟩ := models Q R hQ
  exact ⟨c, G, q, C, T, hG, hm, rp_wf_l hZF hω (ZFDC.dc_l hM hω) hU.1
    (ed_countable_l hωκ hU.2.1 hc) (fun _ => id) hR hm⟩

end YesMetaZFC.SetTheory.LargeCardinal
