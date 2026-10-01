import YesMetaZFC.Model.SetTheory.Internal.ElementaryHull
import YesMetaZFC.SetTheory.FinitaryTrace

/-! # 内部初等小模型在指定子集上的实际 club

固定一次司寇伦选择图后，最小闭包的交集组成真实 club。每个成员都给出一个
包含固定种子的内部可数初等模型见证，交集等式精确保留原成员，而非仅给出包含。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem selem_trace_club_l (hZFC : M.Models ZFC) {ω c H R A X} (hω : M.IsOmega ω)
    (hM : Smdl_d I c H R) (hA : M.MemberSubset A H) (ha : M.CardinalLessOrEqual I A ω)
    (hX : M.MemberSubset X H) : ∃ C, Cc_club_d I ω X C ∧
      ∀ Y, M.mem Y C → ∃ N d S, Ssub_d I c d H R N S ∧ Selem_d I ω c d ∧
        M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧ ∀ x, M.mem x Y ↔ M.mem x N ∧ M.mem x X := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨u, V, S, T, D, K, hK⟩ := ssk_exists_l I hZFC hω c hM.2.1
  obtain ⟨f, hf⟩ := ZF.exists_identityBijection hZF I ω
  have ht := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hK.codes) ⟨f, hf.1⟩ hK.labels
  obtain ⟨C, hC, hc⟩ := ZFC.fc_trace_club_l I hZFC hω hK.params hK.domain hK.graph ht hA ha hX
  refine ⟨C, hC, fun Y hY => ?_⟩
  obtain ⟨N, hn, hCount, he⟩ := (hc Y).mp hY
  obtain ⟨d, S', hSub, hElem⟩ := selem_of_skolem_l I hZF hω hM hK.codes hn.2.2.1
    (hK.point_mem_l I hZF hω hM hn.2.2.2.1) (hK.closed_l I hn.2.2.1 hn.2.2.2.1)
  exact ⟨N, d, S', hSub, hElem, hn.1, hCount, he⟩

end YesMetaZFC.SetTheory.Internal
