import YesMetaZFC.Model.SetTheory.Internal.ElementaryHull
import YesMetaZFC.SetTheory.FinitaryClub

/-! # 指定内部 club 中的实际初等模型

先构造真实司寇伦图，再在给定 club 中闭合该图。因此同一个内部可数集合同时
具有 club 成员资格和完整内部初等性，供 proper 主条件与泛型提升共同使用。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem selem_club_hull_l (hZFC : M.Models ZFC) {ω c X R C A} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hC : Cc_club_d I ω X C) (hA : M.MemberSubset A X)
    (ha : M.CardinalLessOrEqual I A ω) : ∃ N d S,
      Ssub_d I c d X R N S ∧ Selem_d I ω c d ∧ M.MemberSubset A N ∧ M.mem N C := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨u, L, S, T, D, K, hK⟩ := ssk_exists_l I hZFC hω c hM.2.1
  obtain ⟨J, hJ⟩ := ZF.exists_identityBijection hZF I ω
  have ht := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hK.codes) ⟨J, hJ.1⟩ hK.labels
  obtain ⟨N, hN, hAN, hc⟩ := ZFC.fc_club_hull_l I hZFC hω hK.params hK.domain hK.graph ht hC hA ha
  obtain ⟨d, Q, hQ, he⟩ := selem_of_skolem_l I hZF hω hM hK.codes (hC.members N hN).1
    (hK.point_mem_l I hZF hω hM hc) (hK.closed_l I (hC.members N hN).1 hc)
  exact ⟨N, d, Q, hQ, he, hAN, hN⟩

end YesMetaZFC.SetTheory.Internal
