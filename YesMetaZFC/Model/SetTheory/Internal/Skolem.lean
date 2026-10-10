import YesMetaZFC.Model.SetTheory.Internal.SkolemSyntax
import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.SetTheory.FinitaryHull

/-! # 实际内部司寇伦函数与最小闭包

原选择公理把满足关系的见证纤维统一选成一张函数图。规则域内部可数，任意无限 κ 的 κ 小种子之有限
参数闭包仍为 κ 小。假公式的零元运算确保基点进入每个闭集，空种子同样有效。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 由非空内部载体及其结构码构造整张司寇伦选择图。 -/
theorem ssk_exists_l (hZFC : M.Models ZFC) {ω X} (hω : M.IsOmega ω) (c : M.Domain)
    (hX : ∃ x, M.mem x X) : ∃ u C S T D K, Ssk_d I ω c X u C S T D K := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨u, hu⟩ := hX
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω X
  obtain ⟨T, hT⟩ := ZF.exists_cartesianProduct hZF I C ω
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I T S
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push c).push X).push u
  let φ : BinarySchema 4 := { body := ssk_choice_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ p x : φ.denote ρ p x ↔ Ssk_choice_d I ω c X u p x := ssk_choice_sat_l I hZF.1 _ _ _ _ _ _ _
  obtain ⟨K, hK, hk⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := X) (by
    intro p hp
    obtain ⟨t, ht, s, _, hps⟩ := (hD p).mp hp
    obtain ⟨a, _, i, _, hti⟩ := (hT t).mp ht
    by_cases he : ∃ x, M.mem x X ∧ Ssk_wit_d I ω c X u a i s x
    · obtain ⟨x, hx, hw⟩ := he
      exact ⟨x, hx, (hφ p x).mpr ⟨a, i, t, s, hti, hps, Or.inl hw⟩⟩
    · exact ⟨u, hu, (hφ p u).mpr ⟨a, i, t, s, hti, hps, Or.inr ⟨he, rfl⟩⟩⟩)
  exact ⟨u, C, S, T, D, K, hu, hC, hS, hT, hD, hK, fun p x hx => (hφ p x).mp (hk p x hx)⟩

theorem Ssk_d.value_l {ω c X u C S T D K a i t s p x} (h : Ssk_d I ω c X u C S T D K)
    (ht : I.Codes t a i) (hp : I.Codes p t s) (hx : M.PairMember I p x K) :
    Ssk_wit_d I ω c X u a i s x ∨ ((¬ ∃ y, M.mem y X ∧ Ssk_wit_d I ω c X u a i s y) ∧ x = u) := by
  obtain ⟨b, j, v, r, hv, hr, hs⟩ := h.select p x hx
  obtain ⟨rfl, rfl⟩ := I.injective hp hr
  obtain ⟨rfl, rfl⟩ := I.injective ht hv
  exact hs

/-- 对选择图闭合的子集实际承接全部内部有限参数下的存在见证。 -/
theorem Ssk_d.closed_l {ω c X u C S T D K N} (h : Ssk_d I ω c X u C S T D K)
    (hN : M.MemberSubset N X) (hc : Fc_closed_d I ω T K N) : Ssk_closed_d I ω c X u C N := by
  intro a i n s ha hi hn hs he
  obtain ⟨t, ht⟩ := I.total a i
  obtain ⟨p, hp⟩ := I.total t s
  have htT := (h.labels t).mpr ⟨a, ha, i, hi, ht⟩
  have hpD := (h.domain p).mpr ⟨t, htT, s, (h.params s).mpr ⟨n, hn, hs.mono_target_l I hN⟩, hp⟩
  obtain ⟨x, _, hx⟩ := h.graph.2.2 p hpD
  refine ⟨x, hc x ⟨n, s, t, p, hn, hs, htT, hp, hx⟩, ?_⟩
  exact (h.value_l I ht hp hx).elim id (fun hx => (hx.1 he).elim)

/-- 假公式提供返回基点的零元运算，所以任意闭集都非空，包括空种子的闭包。 -/
theorem Ssk_d.point_mem_l (hZF : M.Models ZF) {ω c X R u C S T D K N}
    (hω : M.IsOmega ω) (hM : Smdl_d I c X R) (h : Ssk_d I ω c X u C S T D K)
    (hN : Fc_closed_d I ω T K N) : M.mem u N := by
  obtain ⟨a, l, F, k, v, ha, _, hv⟩ := source_compile_l I hZF hω (.falsum : Formula 1 0)
    (by simp only [Definitional.Formula.FreeClosed])
  obtain ⟨e, he, heω⟩ := hω.1.1
  have empty_fun (B : M.Domain) : M.IsSetFunctionFromTo I e e B :=
    ⟨(Structure.IsSequenceOfLength.empty I he).2.1, (Structure.IsSequenceOfLength.empty I he).2.2,
      fun i hi => (he i hi).elim⟩
  obtain ⟨t, ht⟩ := I.total a e
  obtain ⟨p, hp⟩ := I.total t e
  have htT := (h.labels t).mpr ⟨a, (h.codes a).mpr ⟨l, F, k, ha⟩, e, heω, ht⟩
  obtain ⟨x, hxX, hx⟩ := h.graph.2.2 p ((h.domain p).mpr
    ⟨t, htT, e, (h.params e).mpr ⟨e, heω, empty_fun X⟩, hp⟩)
  have hxN := hN x ⟨e, e, t, p, heω, empty_fun N, htT, hp, hx⟩
  rcases h.value_l I ht hp hx with ⟨n, f, g, _, hs, hf, hg, hgSat⟩ | ⟨_, heq⟩
  · obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
    have hgE := (hE g).mpr (hg.function_l I (hf.function_l I hs h.point) heω hxX)
    let ρ : Env (smdl_structure_l I (R := R) hM.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨u, h.point⟩⟩
    have hh := (hv X R hM.2.1 E hE g hgE ρ (fun j => Fin.elim0 j)).mp
      ((satisfies_decode_l I hZF.1 hM ha hE).mp hgSat)
    simp only [Definitional.Semantics.satisfies] at hh
  · exact heq ▸ hxN

/-- 一次装配实际选择图与最小内部司寇伦闭包，允许任意 κ 小种子，包括空集。 -/
theorem ssk_hull_bound_l (hZFC : M.Models ZFC) {ω κ c X R A} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ)
    (hM : Smdl_d I c X R) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A κ) :
    ∃ u C S T D K N, Ssk_d I ω c X u C S T D K ∧ Fc_hull_d I ω X T K A N ∧
      M.CardinalLessOrEqual I N κ ∧ M.mem u N ∧ Ssk_closed_d I ω c X u C N := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨u, C, S, T, D, K, hK⟩ := ssk_exists_l I hZFC hω c hM.2.1
  obtain ⟨J, hJ⟩ := ZF.exists_identityBijection hZF I ω
  have htω := ZF.countable_product_l I hZF hω (scode_countable_l I hZF hω hK.codes) ⟨J, hJ.1⟩ hK.labels
  obtain ⟨t, ht⟩ := htω
  obtain ⟨j, hj⟩ := hκ.2
  have ht := ZF.exists_compositionInjection hZF I ht hj
  obtain ⟨P, Q, N, hP, hQ, hz, hs, hu, hN⟩ := ZF.fc_hull_chain_l I hZF hω hK.graph hA
  -- 固定已构造的选择图后，各闭包阶段按实际原公式归纳保持大小不超过 κ。
  let ρ : Env M 2 := (⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push κ
  let φ : UnarySchema 2 := { body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
    (Formula.cardinalLessOrEqual 𝒞 .newest (.bound 2))) }
  have hφ i : φ.denote ρ i ↔ ∀ B, M.PairMember I i B Q → M.CardinalLessOrEqual I B κ := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]
    rfl
  have count : ∀ i, M.mem i ω → ∀ B, M.PairMember I i B Q → M.CardinalLessOrEqual I B κ := by
    apply hω.induction (fun i => ∀ B, M.PairMember I i B Q → M.CardinalLessOrEqual I B κ)
    · obtain ⟨U, hU⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨U, fun i => (hU i).trans (and_congr_right fun _ => hφ i)⟩
    · exact fun e he B hB => hQ.1.2 e A B (hz e he) hB ▸ ha
    · intro i hi ih j hji E hj
      obtain ⟨B, hB, hb⟩ := hQ.2.2 i hi
      exact ZF.fc_step_bound_l I hZF hω hκ hK.params hK.domain hK.graph ht
        ((hP B).mp hB) (ih B hb) (hs i j B E hji hb hj)
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I hQ.1 hQ.2.1
  have hQY : M.IsSetFunctionFromTo I Q ω Y := ⟨hQ.1, hQ.2.1, fun i hi => by
    obtain ⟨B, _, hb⟩ := hQ.2.2 i hi
    exact ⟨B, (hY B).mpr ⟨i, hb⟩, hb⟩⟩
  have hn := ZFC.cc_union_bound_l I hZFC hω hκ hQY hu (fun B hB => by
    obtain ⟨i, hi⟩ := (hY B).mp hB
    exact count i (hQ.input_mem_of_pairMember hi) B hi)
  exact ⟨u, C, S, T, D, K, N, hK, hN, hn, hK.point_mem_l I hZF hω hM hN.2.2.1,
    hK.closed_l I hN.2.1 hN.2.2.1⟩

/-- 可数 Skolem 壳是一般 κ 小闭包的实例。 -/
theorem ssk_hull_l (hZFC : M.Models ZFC) {ω c X R A} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ u C S T D K N, Ssk_d I ω c X u C S T D K ∧ Fc_hull_d I ω X T K A N ∧
      M.CardinalLessOrEqual I N ω ∧ M.mem u N ∧ Ssk_closed_d I ω c X u C N := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨F, hF⟩ := ZF.exists_identityBijection hZF I ω
  exact ssk_hull_bound_l I hZFC hω ⟨ZF.omega_cardinal_l I hZF hω, F, hF.1⟩ hM hA ha

end YesMetaZFC.SetTheory.Internal
