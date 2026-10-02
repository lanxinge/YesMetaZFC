import YesMetaZFC.SetTheory.Descriptive.Projective.Relative

/-! # 解析与射影层入口

固定实际内部自然数配对图后，Baire×Baire 与 Baire 由逐坐标配对同胚。
解析类采用 Borel 关系投影，余解析类取补；Σ¹ₙ、Π¹ₙ、Δ¹ₙ 沿内部 ω 定义。
`Pcode_d` 将内部层号、极性和 Borel 码打包为单个集合，`pden_exists_unique_l`
给出唯一实际解释。全部层又收集成唯一内部函数图；Cantor 的点类用子空间迹得到。

当前不包含 Suslin 分离及完美集定理、Δ¹₁ ⊆ Borel、
射影层次严格性、统一化或决定性结论。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 自动读取任意内部层，连同其实际 Δ 类一起返回。 -/
theorem phier_stage_l (hZF : M.Models ZF) {ω A B J H n}
    (hH : Phier_d I ω A B J H) (hn : M.mem n ω) : ∃ p S P D,
      M.PairMember I n p H ∧ I.Codes p S P ∧
      (∀ K, M.mem K S ↔ Ps_d I ω A B J n K) ∧
      (∀ K, M.mem K P ↔ Pp_d I ω A B J n K) ∧ ∀ K, M.mem K D ↔ Pd_d I ω A B J n K := by
  obtain ⟨p, hp⟩ := plevel_exists_l I hZF ω A B J n
  have hnH := (hH.2 n p).mpr ⟨hn, hp⟩
  obtain ⟨D, hd⟩ := plevel_delta_l I (ZF.modelsKP hZF) hp
  obtain ⟨S, P, hp, hs, ht⟩ := hp
  exact ⟨p, S, P, D, hnH, hp, hs, ht, hd⟩

/-- 空间、编号、配对、全层函数图及 Baire/Cantor 的射影集合族同时实际构造。 -/
theorem dst_projective_l (hZF : M.Models ZF) : ∃ ω A B C J H P Q,
    Baire_d I ω B ∧ Cantor_d I ω C ∧ Fseq_space_d I ω ω A ∧ M.CardinalLessOrEqual I A ω ∧
    Npair_d I ω J ∧ Phier_d I ω A B J H ∧
    (∀ K, M.mem K P ↔ Projective_d I ω A B J K) ∧ ∀ K, M.mem K Q ↔ Rclass_d C P K := by
  obtain ⟨ω, D, B, C, A, _, hB, hD, hC, hA, ha, _, _⟩ := ds_spaces_l I hZF
  obtain ⟨J, hJ⟩ := npair_exists_l I hZF hB.1
  obtain ⟨H, hH, _⟩ := phier_exists_unique_l I hZF ω A B J
  obtain ⟨P, hP⟩ := projective_collection_l I hZF ω A B J
  obtain ⟨Q, hQ⟩ := rclass_collection_l hZF C P
  exact ⟨ω, A, B, C, J, H, P, Q, hB, ⟨hB.1, D, hD, hC⟩, hA, ha, hJ, hH, hP, hQ⟩

end YesMetaZFC.SetTheory.Descriptive
