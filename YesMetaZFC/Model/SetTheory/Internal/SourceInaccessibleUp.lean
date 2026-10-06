import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessible

/-! # 初始秩模型的不可达性向上读取

在实际极限 Vδ 中，相关函数图、值域和幂集都由秩界回收。因此内部的
基数、正则性和强极限判断就是原背景判断；一般传递源不作这一提升。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_v_inaccessible_up_l (hZF : M.Models ZF) {δ X ω κ : M.Domain}
    (hδ : M.IsLimitOrdinal δ) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X)
    (h : Sc_inaccessible_d ω X κ) : M.mem ω κ ∧
      M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) κ ∧
      M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP hZF)) κ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hω, hκ, h⟩ := h
  have ht := ZF.v_transitive_l I hZF hX
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  have hp := sc_v_pair_l hZF hδ hX
  let J := rt_pair_l ht nx hZF.1 hp
  let k : N.Domain := ⟨κ, hκ⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hZF.1 ht nx),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hZF.1 ht nx)] at h
  change M.mem ω κ ∧ N.IsRegularCardinal J k ∧ N.IsStrongLimitCardinal J k at h
  obtain ⟨above, hr, hs⟩ := h
  have owned {A B f} (ha : M.mem A X) (hb : M.mem B X) (fn : Fn0_d A B f) : M.mem f X := by
    obtain ⟨U, hu, au, bu⟩ := ZF.v_joint_bound_l I hZF hX ha hb
    exact ZF.v_relation_mem_l I hZF hX hδ hu (fun p hp => (fn.1 p hp).elim fun a ha =>
      ha.2.elim fun b hb => ⟨a, au a ha.1, b, bu b hb.1, hb.2⟩)
  have ho := (rt_ordinal_iff_l ht nx (ZF.modelsKP hZF) k).mp hr.1.1
  have cardinal : M.IsCardinal I κ := by
    refine ⟨ho, ?_⟩
    rintro μ hμ ⟨f, bij⟩
    have hμX := ht κ hκ μ hμ
    have hf := owned hμX hκ (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)
    exact hr.1.2 ⟨μ, hμX⟩ hμ ⟨⟨f, hf⟩,
      (rt_bijection_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp ⟨f, hf⟩ ⟨μ, hμX⟩ k).mpr bij⟩
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  · obtain ⟨f, cf⟩ := hr.2.1
    exact ⟨f.val, rt_cofinal_up_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (ZF.modelsKP hZF) f k k cf⟩
  · rintro μ ⟨f, cf⟩
    rcases ho.trichotomy hZF.1 cf.2.1.1.1.1 (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ) with eq | lt | gt
    · exact Or.inl (hZF.1.eq_of_same_members κ μ eq)
    · exact Or.inr lt
    · have hμX := ht κ hκ μ gt
      have hf := owned hμX hκ (fn0_of_function_l (ZF.modelsKP hZF) cf.isSetFunctionFromTo)
      obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
      have hR := ZF.v_subset_mem_l I hZF hX hκ (cf.range_isCofinalSubset hZF.1 range).2.1
      exact (hr.2.2 ⟨μ, hμX⟩ ⟨⟨f, hf⟩, rt_cofinal_down_l ht nx hZF.1
        (KP.exists_pair (ZF.modelsKP hZF)) hp ⟨f, hf⟩ ⟨μ, hμX⟩ k ⟨R, hR⟩ range cf⟩).imp
        (congrArg Subtype.val) id
  · intro a ha P power
    have haX := ht κ hκ a ha
    have hP := ZF.v_power_mem_l I hZF hX hδ haX power
    have pow : N.IsPowerSetOf ⟨P, hP⟩ ⟨a, haX⟩ := fun B =>
      ⟨fun hb z hz => (power B.val).mp hb z.val hz,
        fun sub => (power B.val).mpr (fun z hz => sub ⟨z, ht B.val B.property z hz⟩ hz)⟩
    obtain ⟨⟨f, inj⟩, not_bij⟩ := hs.2 ⟨a, haX⟩ ha ⟨P, hP⟩ pow
    refine ⟨⟨f.val, (rt_injection_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp f ⟨P, hP⟩ k).mp inj⟩, ?_⟩
    rintro ⟨g, bij⟩
    have hg := owned hP hκ (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)
    exact not_bij ⟨⟨g, hg⟩, (rt_bijection_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp ⟨g, hg⟩ ⟨P, hP⟩ k).mpr bij⟩

end YesMetaZFC.SetTheory.Internal
