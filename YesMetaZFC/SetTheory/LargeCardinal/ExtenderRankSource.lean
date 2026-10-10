import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource

/-! # 正则秩层本身的源实例

源就是 Vδ。全内部分离与有限集合代数适用于极限秩层；小定义域统一化
使用 δ 的正则性。此处没有强极限前提，也不再通过 Vδ=Hδ 改换源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 测度图的支撑与有限 κ 列给出统一秩界，故整张扩展器属于原极限秩层。 -/
theorem Em_family_d.rank_mem_l (hZF : M.Models ZF) {ω κ L F δ X : M.Domain}
    (family : Em_family_d ω κ L F) (graph : M.IsSetRelation (kp_pair_l (ZF.modelsKP hZF)) F)
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (hωX : M.mem ω X) (hκX : M.mem κ X) (hLX : M.mem L X) : M.mem F X := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω L
  have hKX := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hκX hK
  have hSX := ZF.v_fseq_mem_l I hZF hX hδ hω hωX hLX hS
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF K
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  have hQX := ZF.v_power_mem_l I hZF hX hδ (ZF.v_power_mem_l I hZF hX hδ hKX hP) hQ
  obtain ⟨B, hB, hSB, hQB⟩ := ZF.v_joint_bound_l I hZF hX hSX hQX
  apply ZF.v_relation_mem_l I hZF hX hδ hB
  intro p hp
  obtain ⟨a, U, pair⟩ := graph p hp
  obtain ⟨n, D, hn, ha, hd, hu⟩ := family.measure a U ⟨p, pair, hp⟩
  refine ⟨a, hSB a ((hS a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ha⟩), U, hQB U ((hQ U).mpr ?_), pair⟩
  intro A hA
  exact (hP A).mpr (fun s hs => (hK s).mpr ⟨n, hn,
    fn0_function_l (ZF.modelsKP hZF) ((hd s).mp (hu.1.1 A hA s hs))⟩)

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
