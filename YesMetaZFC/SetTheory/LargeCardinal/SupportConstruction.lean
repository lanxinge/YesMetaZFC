import YesMetaZFC.SetTheory.LargeCardinal.SupportCompleteness
import YesMetaZFC.SetTheory.LargeCardinal.Coherence
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower

/-! # 武丁强嵌入同时产生全部有限支撑测度与分量商结构

先用同一个有限次幂集容器覆盖字母表上的所有关系图，再选择覆盖它的强嵌入。
因此有限支撑与完整对局都在目标载体内；各分量的商结构允许任意秩的源载体。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem woodin_components_l (hZF : M.Models ZF) {δ} (hd : Woodin_d I δ) :
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧ M.IsOrdinal κ ∧ M.mem ω κ ∧
      ∀ L, M.mem L δ → M.MemberSubset ω L → ∃ ν N B j W k S F,
        Wd_witness_d I ω δ X A κ ν N B j W k ∧ M.mem L ν ∧ M.mem L k ∧
        Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S ∧ M.mem S N ∧ Es_family_d I j κ L S F ∧
        (∀ a U, M.PairMember I a U F → ∃ n D, Fn0_d n L a ∧ (∀ s, M.mem s D ↔ Fn0_d n κ s) ∧
          Ed_filter_d I j a D U ∧ FilterZF.Maximal_d (ℳ := M) D U ∧ Ed_complete_d κ D U ∧
          ∀ Q R, (∃ x, M.mem x Q) → ∃ c G p C T,
            (∀ f, M.mem f G ↔ Fn0_d D Q f) ∧ Rp_model_d I D Q U R c G p C T) ∧
        Es_coherent_d I ω κ L F ∧
        ∀ H f, Ef_levels_d ω κ H → Es_fiber_d I ω L F H f →
          ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  obtain ⟨ω, X, hω, hωδ, hr, _, hV, hd⟩ := hd
  obtain ⟨D, hD⟩ := hr.2.1
  refine ⟨ω, X, hω, hV, fun A hA => ?_⟩
  obtain ⟨κ, hκ, hk⟩ := hd A hA
  obtain ⟨N₀, B₀, j₀, W₀, k₀, h₀⟩ := hk ω hωδ
  have hc₀ := h₀.2.2.2.2.2.2.1
  have hωκ := ed_critical_omega_l I hZF hω h₀.2.2.2.2.2.1 (ZF.v_transitive_l I hZF hV) h₀.1 hc₀
  refine ⟨κ, hκ, hc₀.ordinal, hωκ, fun L hL hωL => ?_⟩
  obtain ⟨R, hRX, hR⟩ := ZF.v_relation_cover_l I hZF hV hD.1 (ZF.v_ordinal_mem_l I hZF hV hL)
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF R
  have bound {n a} (hn : M.MemberSubset n L) (ha : Fn0_d n L a) : M.mem a R :=
    hR a fun p hp => (ha.1 p hp).elim fun i hi => hi.2.elim fun b hb => ⟨i, hn i hi.1, b, hb⟩
  obtain ⟨ν, N, B, j, W, k, hw, hLν, hLk, hQN⟩ := wd_cover_embedding_l I hZF hV hD.1 hk hL
    (ZF.v_power_mem_l I hZF hV hD.1 hRX hQ)
  obtain ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩ := hw
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω L
  have hSN : M.mem S N := hN Q hQN S ((hQ S).mpr fun a ha => by
    obtain ⟨n, hn, hna⟩ := (hS a).mp ha
    exact bound (fun i hi => hωL i (hω.transitive hZF n hn i hi)) (fn0_of_function_l (ZF.modelsKP hZF) hna))
  obtain ⟨G, hG⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) ω L
  have hGN : M.mem G N := hN Q hQN G ((hQ G).mpr fun f hf =>
    bound hωL (fn0_of_function_l (ZF.modelsKP hZF) ((hG f).mp hf)))
  obtain ⟨F, hF⟩ := es_family_exists_l I hZF hω hS j κ
  refine ⟨ν, N, B, j, W, k, S, F, ⟨hN, hNX, hδN, hW, hWN, hj, hc, hνk, ht⟩, hLν, hLk, hS, hSN, hF,
    ?_,
    es_coherent_l I hZF hω hV hD.1 hj hN hc (hc.ordinal_image.transitive L hLk) (hN S hSN) hF,
    fun _ _ hH hf => ef_common_fiber_l I hZF hω hV hD.1 hj hN hc
      (hc.ordinal_image.transitive L hLk) hG hGN hH ((es_fiber_iff_l I (ZF.modelsKP hZF) hS hF hH).mp hf)⟩
  intro a U ha
  obtain ⟨n, D, hn, hD, hd, hu, hc⟩ := es_family_ultra_l I hZF hω hV hD.1 hj hN hc
    (hc.ordinal_image.transitive L hLk) hS (hN S hSN) hF ha
  refine ⟨n, D, hn, hD, hd, hu, hc, fun Q R hQ => ?_⟩
  obtain ⟨B, hB⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) D Q
  obtain ⟨x, hx⟩ := hQ
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF (kp_pair_l (ZF.modelsKP hZF)) (source := D) hx
  obtain ⟨G, c, p, C, T, hG, hm⟩ := rp_family_model_l I hZF hu.1.base_l ((hB f).mpr hf)
    (fn0_of_function_l (ZF.modelsKP hZF) hf) R
  exact ⟨c, G, p, C, T, fun g => (hG g).trans ⟨And.right,
    fun hg => ⟨(hB g).mpr (fn0_function_l (ZF.modelsKP hZF) hg), hg⟩⟩, hm⟩

end YesMetaZFC.SetTheory.LargeCardinal
