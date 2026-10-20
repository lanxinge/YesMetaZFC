import YesMetaZFC.Model.SetTheory.Internal.ZfcDecode
import YesMetaZFC.Model.SetTheory.Internal.SourceTheory
import YesMetaZFC.SetTheory.InaccessibleHierarchy

/-! # 不可达秩段上的实际内部 ZFC 证书

固定公理由秩闭包验证。不可达性给出 Vδ = Hδ，全部内部收集实例因此拥有
实际集合界；不使用外部可数闭性，也不以待证证书作为实例前提。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem zc_v_base_l {ω δ X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (above : M.mem ω δ) (rank : V_d I δ X) (nx : Nonempty {x // M.mem x X})
    (ρ : Env (rt_model_l X nx) 0) : Formula.satisfies ρ zc_base_m := by
  have tr := ZF.v_transitive_l I hZF rank
  have ext := rt_model_ext_l hZF.1 tr nx
  have alg := sc_v_algebra_l hZFC hδ rank
  have same (x y : (rt_model_l X nx).Domain) : (rt_model_l X nx).SameMembers x y ↔ x.val = y.val :=
    ⟨fun h => congrArg Subtype.val (ext.eq_of_same_members x y h), fun h => (Subtype.ext h : x = y) ▸ fun _ => Iff.rfl⟩
  simp only [zc_base_m, Formula.satisfies_conj_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Axioms.extensionality, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq ext]
    exact ext.eq_of_same_members
  · obtain ⟨e, he, heω⟩ := hω.1.1
    exact (Axioms.satisfies_emptySet_iff ρ.free).mpr
      ⟨⟨e, tr ω (ZF.v_ordinal_mem_l I hZF rank above) e heω⟩, fun z => he z.val⟩
  · apply (Axioms.satisfies_pairing_iff ρ.free).mpr
    intro a b
    obtain ⟨p, hp, pair⟩ := alg.pair a.val b.val a.property b.property
    exact ⟨⟨p, hp⟩, fun z => (pair z.val).trans (or_congr (same z a).symm (same z b).symm)⟩
  · apply (Axioms.satisfies_union_iff ρ.free).mpr
    intro A
    obtain ⟨U, hu, un⟩ := alg.union A.val A.property
    exact ⟨⟨U, hu⟩, fun z => (un z.val).trans
      ⟨fun ⟨a, ha, hz⟩ => ⟨⟨a, tr A.val A.property a ha⟩, ha, hz⟩, fun ⟨a, ha, hz⟩ => ⟨a.val, ha, hz⟩⟩⟩
  · apply (Axioms.satisfies_powerSet_iff ρ.free).mpr
    intro A
    obtain ⟨P, power⟩ := ZF.exists_powerSet hZF A.val
    exact ⟨⟨P, ZF.v_power_mem_l I hZF rank hδ A.property power⟩, fun z => (power z.val).trans
      ⟨fun sub y hy => sub y.val hy, fun sub y hy => sub ⟨y, tr z.val z.property y hy⟩ hy⟩⟩
  · apply (Axioms.satisfies_infinity_iff ρ.free).mpr
    have hwX := ZF.v_ordinal_mem_l I hZF rank above
    refine ⟨⟨ω, hwX⟩, ?_, fun a ha => ?_⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨⟨e, tr ω hwX e heω⟩, fun z => he z.val, heω⟩
    · obtain ⟨s, hs, hsω⟩ := hω.1.2 a.val ha
      exact ⟨⟨s, tr ω hwX s hsω⟩, fun z => (hs z.val).trans (or_congr_right
        ⟨fun h v => h v.val, fun h => (same z a).mp h ▸ fun _ => Iff.rfl⟩), hsω⟩
  · apply (Axioms.foundation_sat_iff_d ρ.free).mpr
    intro A hn
    obtain ⟨z, hz⟩ := hn
    obtain ⟨a, ha, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨z.val, hz⟩
    exact ⟨⟨a, tr A.val A.property a ha⟩, ha, fun y hy => minimal y.val hy⟩
  · simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, Formula.extensionalNe, Formula.satisfies_neg_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq ext,
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    intro A hn
    obtain ⟨C, select⟩ := ZFC.choice_set_l hZFC A.val (fun a ha =>
      (hn.1 ⟨a, tr A.val A.property a ha⟩ ha).elim fun x hx => ⟨x.val, hx⟩) (by
        intro a ha b hb ne ⟨x, hx, hy⟩
        exact hn.2 ⟨a, tr A.val A.property a ha⟩ ha ⟨b, tr A.val A.property b hb⟩ hb
          (fun e => ne (congrArg Subtype.val e)) ⟨⟨x, tr a (tr A.val A.property a ha) x hx⟩, hx, hy⟩)
    -- 选择集先截到族的并集，故所得实际对象仍属于原秩段。
    obtain ⟨U, hu, un⟩ := alg.union A.val A.property
    let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => C, fun _ => C⟩ U
    have spec x : M.mem x B ↔ M.mem x U ∧ M.mem x C := hb x
    refine ⟨⟨B, ZF.v_subset_mem_l I hZF rank hu (fun x hx => ((spec x).mp hx).1)⟩, fun a ha => ?_⟩
    obtain ⟨x, hx, unique⟩ := select a.val ha
    exact ⟨⟨x, tr a.val a.property x hx.2⟩, ⟨(spec x).mpr ⟨(un x).mpr ⟨a.val, ha, hx.2⟩, hx.1⟩, hx.2⟩,
      fun y hy => Subtype.ext (unique y.val ⟨((spec y.val).mp hy.1).2, hy.2⟩)⟩

/-- 载体、隶属图和全部公理实例同时产生，不从证书前提取出另一份证书。 -/
theorem zc_inaccessible_l {ω δ X : M.Domain} (hω : M.IsOmega ω) (above : M.mem ω δ)
    (regular : M.IsRegularCardinal I δ) (strong : M.IsStrongLimitCardinal I δ) (rank : V_d I δ X) :
    ∃ c R, Smem_d I c X R ∧ Zc_model_d I ω c X R := by
  have tr := ZF.v_transitive_l I hZF rank
  have hwX := ZF.v_ordinal_mem_l I hZF rank above
  obtain ⟨c, R, hm⟩ := smdl_membership_l I hZF ⟨ω, hwX⟩
  have mem x y (hx : M.mem x X) (hy : M.mem y X) : M.PairMember I x y R ↔ M.mem x y :=
    (hm.2 x y).trans ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩
  have hereditary := ZFC.inaccessible_hereditary_l I hZFC hω above regular strong rank
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hwX⟩⟩
  refine ⟨c, R, hm, hm.1, rf_ext_mem_l I hZF.1 tr hm, ?_, ?_, ?_⟩
  · intro ρ
    exact (smem_formula_l I hm nx zc_base_m ⟨ρ.bound, ρ.free⟩).mp
      (zc_v_base_l hZFC hω regular.isLimitOrdinal above rank nx ⟨ρ.bound, ρ.free⟩)
  · intro E F n r i f D hE hF hr hi hf hD
    obtain ⟨A, hA, sep⟩ := (sc_v_theory_l hZFC regular.isLimitOrdinal rank ω R).separation
      E F n r i f D hE hF hr hi hf hD
    exact ⟨A, hA, (ssep_relation_l I tr hm hD hA).mpr sep⟩
  · intro E F n r i j f D _ _ _ _ _ _ _ hD total
    obtain ⟨C, q, hC, fn, select⟩ := h_collect_function_l I hZFC hω regular above hereditary hD
      (fun x hx => total x (tr D hD x hx) ((mem x D (tr D hD x hx) hD).mpr hx))
    refine ⟨C, hC, fun x hx hd => ?_⟩
    obtain ⟨y, hy, hxy⟩ := fn.2.2 x ((mem x D hx hD).mp hd)
    exact ⟨y, tr C hC y hy, (mem y C (tr C hC y hy) hC).mpr hy, select x y hxy⟩

end YesMetaZFC.SetTheory.Internal
