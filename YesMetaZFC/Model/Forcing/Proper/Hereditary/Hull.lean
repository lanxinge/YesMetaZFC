import YesMetaZFC.Model.Forcing.Proper.Generic.ElementaryOn
import YesMetaZFC.Model.Forcing.Proper.Hereditary.Correspondence
import YesMetaZFC.SetTheory.HereditaryCover

/-! # 在实际 H(χ) 中装配主模型及泛型初等提升

不可数正则 χ、H(χ) 及其子集闭性均由原公理构造。选择图和 proper club 的
交闭包沿用共同装配层；小名称定理把泛型环境识别为扩张中实际的 H(χ)。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 自动选择正则 H(χ)、可数初等 N 及主加强，统一提升为扩张中实际 H(eχ) 的初等子模型。 -/
theorem ng_hchi_hull_l {ω A p} (hω : M.IsOmega ω) (hP : Proper_d I ω B R z)
    (hA : M.CardinalLessOrEqual I A ω) (hp : M.mem p B) (hpz : p ≠ z) :
    ∃ χ X c T N d S q, M.IsRegularCardinal I χ ∧ M.mem ω χ ∧ H_d I χ X ∧
      Smem_d I c X T ∧ Ssub_d I c d X T N S ∧ Selem_d I ω c d ∧
      M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧
      Below_d M B R z q p ∧ Mstr_d M B R z N q ∧
      ∀ U (hU : Generic_d M B R z U), U q →
        let E := extension_l M hZF B R z U
        let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
        ∃ (e : M.Domain → E.Domain) (Y Z v c' T' d' S' : E.Domain),
          (∀ a t, Check_d M q a t → Qval_d M B R z U t (e a)) ∧
          (∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y) ∧ Function.Injective e ∧
          E.IsRegularCardinal J (e χ) ∧ H_d J (e χ) Y ∧
          (∀ x, x ∈ Y ↔ Ng_mem_d M B R z U X x) ∧ (∀ x, x ∈ Z ↔ Ng_mem_d M B R z U N x) ∧
          E.IsOmega v ∧ E.TransitiveSet Y ∧ E.CardinalLessOrEqual J Z v ∧ Smem_d J c' Y T' ∧
          Ssub_d J c' d' Y T' Z S' ∧ Selem_d J v c' d' := by
  obtain ⟨Q, hQ⟩ := KP.exists_pair (ZF.modelsKP hZF) A B
  obtain ⟨χ, X, hχ, hωχ, hH, hQX⟩ := ZFC.h_cover_l I hZFC hω Q
  have hX := ZF.h_transitive_l I hZF hH
  have hAX := hX Q hQX A ((hQ A).mpr (Or.inl rfl))
  have hBX := hX Q hQX B ((hQ B).mpr (Or.inr rfl))
  obtain ⟨c, T, N, d, S, q, hc, hs, he, ha, hn, hq, hm, hg⟩ := ng_elementary_on_l O hZFC hω hP hA hp hpz hX
    (ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hBX) (hX A hAX)
  refine ⟨χ, X, c, T, N, d, S, q, hχ, hωχ, hH, hc, hs, he, ha, hn, hq, hm, ?_⟩
  intro U hU hqU
  obtain ⟨Y, Z, v, c', T', d', S', hY, hZ, hv, hYt, hZc, hc', hs', he'⟩ := hg U hU hqU
  obtain ⟨e, hval, hmem, hinj⟩ := check_map_l O hZF hU hqU
  obtain ⟨hreg, hH'⟩ := h_generic_l O hZFC hU hω hχ hωχ hH hBX hqU e hinj hmem hval hY
  exact ⟨e, Y, Z, v, c', T', d', S', hval, hmem, hinj, hreg, hH', hY, hZ, hv, hYt, hZc, hc', hs', he'⟩

end YesMetaZFC.Model.Forcing.Internal
