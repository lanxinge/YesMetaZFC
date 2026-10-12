import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessible

/-! # 任意秩层的原不可达性判断向上读取

反例图的坐标均在 Vκ 中，因而图本身已经属于当前秩层。这个精确秩界
使后继秩层也能检验全部较短双射、共尾序列及小幂集上的单射。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_v_inaccessible_read_l {η Y ω κ : M.Domain} (hY : V_d I η Y)
    (h : Sc_inaccessible_d ω Y κ) :
    M.mem ω κ ∧ M.IsRegularCardinal I κ ∧ M.IsStrongLimitCardinal I κ := by
  obtain ⟨hw, hk, h⟩ := h
  have ht := ZF.v_transitive_l I hZF hY
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, hw⟩⟩
  let N := rt_model_l Y ny
  simp only [sc_inaccessible_m, Formula.isRegularCardinal, Formula.isCofinality,
    Formula.isStrongLimitCardinal, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.hasCofinalOrdinalSequence, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 ht ny),
    rt_cofinal_formula_l (ZF.modelsKP hZF) ht ny, Formula.satisfies_forallMem_iff,
    Formula.satisfies_isPowerSet_iff, Formula.cardinalLess, Formula.cardinalLessOrEqual,
    Formula.equinumerous, Formula.satisfies_neg_iff,
    rt_injection_formula_l ht ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    rt_bijection_formula_l ht ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push,
    Term.eval_bound_one_push] at h
  obtain ⟨above, ⟨card, ⟨f, cf, _⟩, least⟩, _, small⟩ := h
  obtain ⟨K, hK⟩ := ZF.v_exists_l I hZF cf.1.1
  have ks := ZF.v_ordinal_subset_l I hZF hK
  have graph {A B g} := @sc_rank_graph_l M hZF η Y κ K A B g hY hk cf.1 hK
  have cardinal : M.IsCardinal I κ := by
    simp only [Formula.isCardinal, Formula.equinumerous, Formula.satisfies_conj_iff,
      Formula.satisfies_isOrdinal_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_exists_iff, rt_bijection_formula_l ht ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)),
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at card
    refine ⟨cf.1.1, fun a ha ⟨g, hg⟩ => ?_⟩
    exact card.2 ⟨a, ht κ hk a ha⟩ ha ⟨⟨g, graph (fun x hx => ks x (cf.1.1.transitive a ha x hx)) ks hg.1.1⟩, hg⟩
  refine ⟨above, ⟨cardinal, ⟨f.val, cf⟩, ?_⟩, cardinal, ?_⟩
  · rintro μ ⟨g, hg⟩
    rcases Structure.IsOrdinal.trichotomy hZF.1 cf.1.1 hg.2.1.1.1.1
        (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ) with eq | lt | gt
    · exact Or.inl (hZF.1.eq_of_same_members κ μ eq)
    · exact Or.inr lt
    · have hm := ht κ hk μ gt
      have hgy := graph (fun x hx => ks x (cf.1.1.transitive μ gt x hx)) ks hg.isSetFunctionFromTo
      obtain ⟨R, range, _⟩ := hg.2.2.1.2.2
      have hr := ZF.v_subset_mem_l I hZF hY hk (hg.range_isCofinalSubset hZF.1 range).2.1
      exact (least ⟨μ, hm⟩ ⟨⟨g, hgy⟩, hg, R, hr, range⟩).imp (congrArg Subtype.val) id
  · intro a ha P power
    have hay := ht κ hk a ha
    have hpk := ZF.v_power_mem_l I hZF hK cf.1 (ZF.v_ordinal_mem_l I hZF hK ha) power
    have hp := ZF.v_transitive_l I hZF hY K
      (ZF.v_mem_l I hZF hK hY (ZF.v_ordinal_height_l hZF hY cf.1.1 hk)) P hpk
    have pow : N.IsPowerSetOf ⟨P, hp⟩ ⟨a, hay⟩ := fun B => (power B.val).trans
      ⟨fun sub x hx => sub x.val hx, fun sub x hx => sub ⟨x, ht B.val B.property x hx⟩ hx⟩
    obtain ⟨⟨g, hg⟩, not_bij⟩ := small ⟨a, hay⟩ ha ⟨P, hp⟩ pow
    refine ⟨⟨g.val, hg⟩, fun ⟨b, hb⟩ => ?_⟩
    exact not_bij ⟨⟨b, graph (ZF.v_transitive_l I hZF hK P hpk) ks hb.1.1⟩, hb⟩

end YesMetaZFC.SetTheory.Internal
