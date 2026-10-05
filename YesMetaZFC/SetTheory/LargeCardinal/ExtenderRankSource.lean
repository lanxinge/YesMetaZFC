import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource

/-! # 正则秩层本身的源实例

源就是 Vδ。全内部分离与有限集合代数适用于极限秩层；小定义域统一化
使用 δ 的正则性。此处没有强极限前提，也不再通过 Vδ=Hδ 改换源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_regular_source_l (hZFC : M.Models ZFC) {ω δ V κ K : M.Domain}
    (hω : M.IsOmega ω) (hωδ : M.mem ω δ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V)
    (hκ : M.mem κ δ) (hωκ : M.MemberSubset ω κ)
    (hK : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K) :
    ∃ R, Ep_source_d (ZFC.models_zf_l hZFC) ω κ K V R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hκV := ZF.v_ordinal_mem_l I hZF hV hκ
  have hωV := ZF.v_ordinal_mem_l I hZF hV hωδ
  have ht := ZF.v_transitive_l I hZF hV
  obtain ⟨c, R, hc, code⟩ := smdl_membership_l I hZF ⟨κ, hκV⟩
  have theory := sc_v_theory_l hZFC hr.isLimitOrdinal hV ω R
  exact ⟨R, hω, hωκ, ht, hωV, hκV,
    sc_ordinal_small_l hZF hω ht ⟨hc, code⟩ theory hκV (hr.isCardinal.1.mem hκ),
    ZF.v_fseq_mem_l I hZF hV hr.isLimitOrdinal hω hωV hκV hK, hK, ⟨c, hc, code⟩,
    theory, sc_v_collection_l hZFC hr hV ω R, sc_v_sequences_l hZF hω hr.isLimitOrdinal hωδ hV,
    sc_v_collapse_l hZF hr.isCardinal hr.isLimitOrdinal hV⟩

end YesMetaZFC.SetTheory.LargeCardinal
