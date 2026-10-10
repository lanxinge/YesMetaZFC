import YesMetaZFC.Model.Forcing.Proper.Generic.ElementaryOn
import YesMetaZFC.SetTheory.CumulativeRank

/-! # proper 力迫下 N[G] 内部初等提升的一键装配

从可数种子和原正条件出发，先取得包含幂集 𝒫(B) 的实际传递环境 X，再构造
统一满足关系的判定／选择图。在 proper club 中同时闭合两图及地模型司寇伦图，
得到同一个内部初等 N 和主加强 q。每个接受 q 的泛型都满足完整内部 N[G]≺X[G]。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 自动构造内部初等 N、主加强，以及每个泛型中的可数初等 N[G]；不交付未实现的闭包参数。 -/
theorem ng_elementary_hull_l {ω A p} (hω : M.IsOmega ω) (hP : Proper_d I ω B R z)
    (hA : M.CardinalLessOrEqual I A ω) (hp : M.mem p B) (hpz : p ≠ z) :
    ∃ X c T N d S q, M.TransitiveSet X ∧ Smem_d I c X T ∧ Ssub_d I c d X T N S ∧
      Selem_d I ω c d ∧ M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧
      Below_d M B R z q p ∧ Mstr_d M B R z N q ∧
      ∀ U (hU : Generic_d M B R z U), U q →
        let E := extension_l M hZF B R z U
        let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
        ∃ Y Z v c' T' d' S' : E.Domain,
          (∀ x, x ∈ Y ↔ Ng_mem_d M B R z U X x) ∧ (∀ x, x ∈ Z ↔ Ng_mem_d M B R z U N x) ∧
          E.IsOmega v ∧ E.TransitiveSet Y ∧ E.CardinalLessOrEqual J Z v ∧ Smem_d J c' Y T' ∧
          Ssub_d J c' d' Y T' Z S' ∧ Selem_d J v c' d' := by
  obtain ⟨P, hPow⟩ := ZF.exists_powerSet hZF B
  obtain ⟨Q, hQ⟩ := KP.exists_pair (ZF.modelsKP hZF) P A
  obtain ⟨α, X, hV, hQX⟩ := ZF.v_cover_l I hZF Q
  have hX := ZF.v_transitive_l I hZF hV
  have hPX := hX Q hQX P ((hQ P).mpr (Or.inl rfl))
  have hAX := hX Q hQX A ((hQ A).mpr (Or.inr rfl))
  have hBound D (hD : M.MemberSubset D B) : M.mem D X := hX P hPX D ((hPow D).mpr hD)
  obtain ⟨c, T, N, d, S, q, h⟩ := ng_elementary_on_l O hZFC hω hP hA hp hpz hX hBound (hX A hAX)
  exact ⟨X, c, T, N, d, S, q, hX, h⟩

end YesMetaZFC.Model.Forcing.Internal
