import YesMetaZFC.SetTheory.FlatPairing.Pair
import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 平坦配对不越出任何无限秩层

标签至多把有限层提高一次；ω 以上的层保持不变。对一对输入先取得共同的
较早秩界，再分别处理有限界与无限界，得到所有 ν≥ω 上的配对闭包。
后继秩层同样适用，不添加极限性或正则性假设。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

private theorem fp_omega_le_l {ω α : M.Domain} (hω : M.IsOmega ω) (hα : M.IsOrdinal α)
    (hn : ¬ M.mem α ω) : M.MemberSubset ω α := by
  rcases Structure.IsOrdinal.trichotomy hZF.1 (hω.isOrdinal hZF) hα
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) ω α) with eq | lt | gt
  · exact fun x hx => (eq x).mp hx
  · exact hα.transitive ω lt
  · exact (hn gt).elim

/-- 输入属于 Vν 时，标签的每个成员仍属于 Vν。 -/
theorem Fp_tag_d.subset_rank_l {b : Bool} {ω ν V x y : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν V) (hx : M.mem x V) (h : Fp_tag_d b ω x y) : M.MemberSubset y V := by
  obtain ⟨α, W, hα, hW, bound⟩ := (ZF.v_unfold_l I hZF hV x).mp hx
  intro z hz
  rcases (h z).mp hz with ⟨_, empty⟩ | ⟨a, ha, shift⟩
  · exact (ZF.v_unfold_l I hZF hV z).mpr ⟨α, W, hα, hW, fun t ht => (empty t ht).elim⟩
  · rcases shift with ⟨haω, succ⟩ | ⟨_, rfl⟩
    · have oa := hω.members_areOrdinals hZF a haω
      have haα := ZF.v_ordinal_height_l hZF hW oa (bound a ha)
      have sub : M.MemberSubset z α := fun t ht => ((succ t).mp ht).elim
        ((v_ordinal_l I hW).transitive a haα t) (fun eq => (hZF.1.eq_of_same_members t a eq).symm ▸ haα)
      have hzν := ordinal_down_l (ZF.modelsKP hZF) (KP.successor_isOrdinal (ZF.modelsKP hZF) oa succ)
        (v_ordinal_l I hV) sub hα
      exact ZF.v_ordinal_mem_l I hZF hV hzν
    · exact ZF.v_mono_l I hZF hW hV ((v_ordinal_l I hV).transitive α hα) _ (bound _ ha)

/-- 任意无限秩层都对两类标签封闭，包括 Vω 和后继秩层。 -/
theorem Fp_tag_d.rank_mem_l {b : Bool} {ω ν V x y : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν V) (hων : M.MemberSubset ω ν) (hx : M.mem x V) (h : Fp_tag_d b ω x y) : M.mem y V := by
  classical
  obtain ⟨α, W, hα, hW, bound⟩ := (ZF.v_unfold_l I hZF hV x).mp hx
  by_cases finite : M.mem α ω
  · obtain ⟨β, succ, hβω⟩ := hω.1.2 α finite
    obtain ⟨T, hT⟩ := ZF.v_exists_l I hZF (hω.members_areOrdinals hZF β hβω)
    have hxT := (ZF.v_unfold_l I hZF hT x).mpr ⟨α, W, succ.predecessor_mem, hW, bound⟩
    exact (ZF.v_unfold_l I hZF hV y).mpr ⟨β, T, hων β hβω, hT, h.subset_rank_l I hZF hω hT hxT⟩
  · have hωα := fp_omega_le_l hZF hω (v_ordinal_l I hW) finite
    apply (ZF.v_unfold_l I hZF hV y).mpr
    refine ⟨α, W, hα, hW, fun z hz => ?_⟩
    rcases (h z).mp hz with ⟨_, empty⟩ | ⟨a, ha, shift⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      have hzω := hZF.1.eq_of_same_members e z (fun t => iff_of_false (he t) (empty t)) ▸ heω
      exact ZF.v_ordinal_mem_l I hZF hW (hωα z hzω)
    · have natural := shift.natural_l hZF.1 hω.1
      rcases shift with ⟨haω, _⟩ | ⟨_, rfl⟩
      · exact ZF.v_ordinal_mem_l I hZF hW (hωα z (natural.mpr haω))
      · exact bound _ ha

/-- ν≥ω 时，平坦有序对保持 Vν；两个坐标可以有任意高的相对秩。 -/
theorem Fp_pair_d.rank_mem_l {ω ν V x y p : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν V) (hων : M.MemberSubset ω ν) (hx : M.mem x V) (hy : M.mem y V)
    (h : Fp_pair_d ω x y p) : M.mem p V := by
  classical
  obtain ⟨R, hR, hxR, hyR⟩ := ZF.v_joint_bound_l I hZF hV hx hy
  obtain ⟨α, W, hα, hW, bound⟩ := (ZF.v_unfold_l I hZF hV R).mp hR
  have tags : ∃ β T, M.mem β ν ∧ V_d I β T ∧
      ∀ b a z, M.mem a W → Fp_tag_d b ω a z → M.mem z T := by
    by_cases finite : M.mem α ω
    · obtain ⟨β, succ, hβω⟩ := hω.1.2 α finite
      obtain ⟨T, hT⟩ := ZF.v_exists_l I hZF (hω.members_areOrdinals hZF β hβω)
      exact ⟨β, T, hων β hβω, hT, fun _ _ z ha tag => (ZF.v_unfold_l I hZF hT z).mpr
        ⟨α, W, succ.predecessor_mem, hW, tag.subset_rank_l I hZF hω hW ha⟩⟩
    · exact ⟨α, W, hα, hW, fun _ _ _ ha tag =>
        tag.rank_mem_l I hZF hω hW (fp_omega_le_l hZF hω (v_ordinal_l I hW) finite) ha⟩
  obtain ⟨β, T, hβ, hT, tags⟩ := tags
  apply (ZF.v_unfold_l I hZF hV p).mpr
  refine ⟨β, T, hβ, hT, fun z hz => ?_⟩
  rcases (h z).mp hz with ⟨a, ha, tag⟩ | ⟨a, ha, tag⟩
  · exact tags false a z (bound a (hxR a ha)) tag
  · exact tags true a z (bound a (hyR a ha)) tag

/-- 在同一个秩层内自动构造原平坦约定的编码，不从存在性选择全局数据。 -/
theorem fp_rank_pair_l {ω ν V x y : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν V) (hων : M.MemberSubset ω ν) (hx : M.mem x V) (hy : M.mem y V) :
    ∃ p, M.mem p V ∧ (fp_interpretation_l (ZF.models_kpi_l hZF)).Codes p x y := by
  obtain ⟨p, hp⟩ := fp_pair_exists_l (ZF.modelsKP hZF) hω.1 x y
  exact ⟨p, hp.rank_mem_l I hZF hω hV hων hx hy, ω, hω, hp⟩

/-- 标签的反解不提高秩，亦适用于有限秩层。 -/
theorem Fp_tag_d.inverse_rank_l {b : Bool} {ω ν V x y : M.Domain} (hω : M.IsInductive ω)
    (hV : V_d I ν V) (hy : M.mem y V) (h : Fp_tag_d b ω x y) : M.mem x V := by
  obtain ⟨α, W, hα, hW, bound⟩ := (ZF.v_unfold_l I hZF hV y).mp hy
  refine (ZF.v_unfold_l I hZF hV x).mpr ⟨α, W, hα, hW, fun a ha => ?_⟩
  obtain ⟨z, shift⟩ := fp_shift_exists_l hω a
  exact shift.mem_l (ZF.v_transitive_l I hZF hW) (bound z ((h z).mpr (Or.inr ⟨a, ha, shift⟩)))

/-- 已属于秩层的平坦对，其两个坐标也实际属于该层。 -/
theorem Fp_pair_d.inverse_rank_l {ω ν V x y p : M.Domain} (hω : M.IsInductive ω)
    (hV : V_d I ν V) (hp : M.mem p V) (h : Fp_pair_d ω x y p) : M.mem x V ∧ M.mem y V := by
  obtain ⟨α, W, hα, hW, bound⟩ := (ZF.v_unfold_l I hZF hV p).mp hp
  have sub (b : Bool) : M.MemberSubset (if b then y else x) W := by
    intro a ha
    obtain ⟨z, tag⟩ := fp_tag_exists_l (ZF.modelsKP hZF) hω b a
    apply tag.inverse_rank_l I hZF hω hW (bound z ?_)
    apply (h z).mpr
    cases b
    · exact Or.inl ⟨a, ha, tag⟩
    · exact Or.inr ⟨a, ha, tag⟩
  exact ⟨(ZF.v_unfold_l I hZF hV x).mpr ⟨α, W, hα, hW, sub false⟩,
    (ZF.v_unfold_l I hZF hV y).mpr ⟨α, W, hα, hW, sub true⟩⟩

end YesMetaZFC.SetTheory
