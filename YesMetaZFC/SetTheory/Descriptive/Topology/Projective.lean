import YesMetaZFC.SetTheory.Descriptive.Projective.Strict

/-! # 解析与射影层入口

固定实际内部自然数配对图后，Baire×Baire 与 Baire 由逐坐标配对同胚。
解析类采用 Borel 关系投影，余解析类取补；Σ¹ₙ、Π¹ₙ、Δ¹ₙ 沿内部 ω 定义。
`Pcode_d` 将内部层号、极性和 Borel 码打包为单个集合，`pden_exists_unique_l`
给出唯一实际解释。全部层又收集成唯一内部函数图；Cantor 的点类用子空间迹得到。
`Pedit_d` 构造补码与交替量词码；连续逆像、升层及二元并交均在 ZF 中完成。
`pf_countable_l`、`pd_countable_l` 对实际码族构造同层可数并交，使用内部实数
可数选择；更弱入口 `pf_countable_with_l` 只要求该码族指标集上的选择。
`ps_standard_l`、`pp_standard_l`、`pd_standard_l` 识别每个标准有限层的交替量词式。

`suslin_l`、`pd_one_borel_l` 完成 Δ¹₁=Borel；`an_separation_l` 返回实际分离码。
`universal_ps_l`、`universal_pp_l` 构造全部正内部层的通用集；`projective_strict_l`
与 `pd_strict_l` 给出严格上升的实际集合见证，Δ₀=Δ₁ 是唯一零层例外。
`suslin_relative_l` 处理解析子空间中的相对 Borel 解释。以上结果只需 ZF。
当前不包含 Borel 秩、完美集定理、统一化或决定性结论。
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

/-- 从原 ZFC 模型实际构造空间及可数选择实例，直接启动每层的码运算。 -/
theorem dst_countable_l (hZFC : M.Models ZFC) : ∃ ω A B J,
    Baire_d I ω B ∧ Fseq_space_d I ω ω A ∧ M.CardinalLessOrEqual I A ω ∧ Npair_d I ω J ∧ Rcc_d I ω B ∧
    ∀ n t H, Pf_d I ω A n t H → ∀ b : Bool, ∃ q, Pjoin_d I b ω A B J n t H q := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨ω, _, B, _, A, _, hB, _, _, hA, ha, _, _⟩ := ds_spaces_l I hZF
  obtain ⟨J, hJ⟩ := npair_exists_l I hZF hB.1
  have hcc := rcc_zfc_l I hZFC ω B
  exact ⟨ω, A, B, J, hB, hA, ha, hJ, hcc, fun _ _ _ h b =>
    pjoin_exists_l I hZF hB hA ha hJ (fcc_real_l I hcc (fun i p hp => (h.2.2.2 i p hp).1)) h b⟩

/-- 直接从 ZF 模型启动 Suslin 定理及任意非零内部层的通用集构造。 -/
theorem dst_suslin_l (hZF : M.Models ZF) : ∃ ω A B J,
    Baire_d I ω B ∧ Fseq_space_d I ω ω A ∧ M.CardinalLessOrEqual I A ω ∧ Npair_d I ω J ∧
    (∀ K, Borel_d I ω A A B K ↔ An_d I ω A B J K ∧ Coan_d I ω A B J K) ∧
    (∀ n, M.mem n ω → (∃ i, M.mem i n) → ∃ U, Us_d I ω A B J n U) ∧
    ∀ n m, M.mem n ω → M.SuccessorOf m n →
      (∃ S, Ps_d I ω A B J m S ∧ ¬ Ps_d I ω A B J n S) ∧
      ∃ P, Pp_d I ω A B J m P ∧ ¬ Pp_d I ω A B J n P := by
  obtain ⟨ω, _, B, _, A, _, hB, _, _, hA, ha, _, _⟩ := ds_spaces_l I hZF
  obtain ⟨J, hJ⟩ := npair_exists_l I hZF hB.1
  exact ⟨ω, A, B, J, hB, hA, ha, hJ, fun _ => suslin_l I hZF hB hA ha hJ,
    fun _ hn hne => universal_ps_l I hZF hB hA ha hJ hn hne,
    fun _ _ hn hm => (projective_strict_l I hZF hB hA ha hJ hn hm).2.2⟩

end YesMetaZFC.SetTheory.Descriptive
