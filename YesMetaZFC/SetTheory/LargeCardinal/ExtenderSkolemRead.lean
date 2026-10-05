import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemCode

/-! # 源内 Skolem 选择图与闭包的完整读取 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sh_closed_relative_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (ω A J T D K B : Term d)
    (hJ : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ).val (A.eval ρ).val (J.eval ρ).val)
    (hD : M.IsCartesianProduct (kp_pair_l hKP) (D.eval ρ).val (T.eval ρ).val (J.eval ρ).val)
    (hK : M.IsSetFunctionFromTo (kp_pair_l hKP) (K.eval ρ).val (D.eval ρ).val (A.eval ρ).val)
    (hB : M.MemberSubset (B.eval ρ).val (A.eval ρ).val) :
    Formula.satisfies ρ (sh_closed_m ω A J T D K B) ↔
      Fc_closed_d (kp_pair_l hKP) (ω.eval ρ).val (T.eval ρ).val (K.eval ρ).val (B.eval ρ).val := by
  have read := sh_closed_sat_l hKP (image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val ρ) ω A J T D K B
  simp only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] at read
  exact (rt_model_delta_l hZ hz (sh_closed_delta_l ω A J T D K B) ρ).trans (read hJ hD hK hB)

theorem sh_hull_relative_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (ω A J T D K U N : Term d)
    (hJ : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ).val (A.eval ρ).val (J.eval ρ).val)
    (hD : M.IsCartesianProduct (kp_pair_l hKP) (D.eval ρ).val (T.eval ρ).val (J.eval ρ).val)
    (hK : M.IsSetFunctionFromTo (kp_pair_l hKP) (K.eval ρ).val (D.eval ρ).val (A.eval ρ).val) :
    Formula.satisfies ρ (sh_hull_m ω A J T D K U N) ↔
      Sh_hull_d hKP Z (ω.eval ρ).val (A.eval ρ).val (T.eval ρ).val (K.eval ρ).val (U.eval ρ).val (N.eval ρ).val := by
  have sub {e} (η : Env (rt_model_l Z hz) e) (A B : Term e) : Formula.satisfies η (Formula.subset A B) ↔
      M.MemberSubset (A.eval η).val (B.eval η).val := by
    simpa only [Formula.subset, Structure.MemberSubset,
      eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ hz (.atom ..) η).trans (Formula.satisfies_subset_iff (ℳ := M) (image_env_l Subtype.val η) A B)
  have closed (B : (rt_model_l Z hz).Domain) (hB : M.MemberSubset B.val (A.eval ρ).val) :
      Formula.satisfies (ρ.push B) (sh_closed_m ω.weaken A.weaken J.weaken T.weaken D.weaken K.weaken .newest) ↔
        Fc_closed_d (kp_pair_l hKP) (ω.eval ρ).val (T.eval ρ).val (K.eval ρ).val B.val := by
    simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      sh_closed_relative_l hKP hZ hz (ρ.push B) ω.weaken A.weaken J.weaken T.weaken D.weaken K.weaken .newest
        (by simpa only [Definitional.Term.eval_weaken] using hJ)
        (by simpa only [Definitional.Term.eval_weaken] using hD)
        (by simpa only [Definitional.Term.eval_weaken] using hK)
        (by simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using hB)
  simp only [sh_hull_m, Formula.satisfies_conj_iff, sub, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨hU, hN, hc, minimal⟩
    refine ⟨hU, hN, (sh_closed_relative_l hKP hZ hz ρ ω A J T D K N hJ hD hK hN).mp hc, ?_⟩
    intro B hB hUB hBA hc
    exact minimal ⟨B, hB⟩ hUB hBA ((closed ⟨B, hB⟩ hBA).mpr hc)
  · rintro ⟨hU, hN, hc, minimal⟩
    refine ⟨hU, hN, (sh_closed_relative_l hKP hZ hz ρ ω A J T D K N hJ hD hK hN).mpr hc, ?_⟩
    intro B hUB hBA hc
    exact minimal B.val B.property hUB hBA ((closed B hBA).mp hc)

end YesMetaZFC.SetTheory.Internal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.select_sat_l {ω κ K₀ Z W c : M.Domain} (source : Ep_source_d hZF ω κ K₀ Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A R u C J T D K : Term d)
    (hw : (w.eval ρ).val = ω) (hm : Smdl_d I c (A.eval ρ).val (R.eval ρ).val)
    (hu : M.mem (u.eval ρ).val (A.eval ρ).val) (hC : Scode_d I ω (C.eval ρ).val)
    (hJ : Fseq_space_d I ω (A.eval ρ).val (J.eval ρ).val)
    (hT : M.IsCartesianProduct I (T.eval ρ).val (C.eval ρ).val ω)
    (hD : M.IsCartesianProduct I (D.eval ρ).val (T.eval ρ).val (J.eval ρ).val)
    (hK : M.IsSetFunctionFromTo I (K.eval ρ).val (D.eval ρ).val (A.eval ρ).val) :
    Formula.satisfies ρ (sh_select_m w A R u C J T D K) ↔
      Ssk_d I ω c (A.eval ρ).val (u.eval ρ).val (C.eval ρ).val (J.eval ρ).val
        (T.eval ρ).val (D.eval ρ).val (K.eval ρ).val := by
  have pair {e} (η : Env (rt_model_l Z hz) e) (p a b : Term e) :
      Formula.satisfies η (kpair0_m p a b) ↔ KPair_d M (p.eval η).val (a.eval η).val (b.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (kpair0_delta_l p a b) η).trans (kpair0_sat_l hZF.1 ..)
  have entry {e} (η : Env (rt_model_l Z hz) e) (a b f : Term e) :
      Formula.satisfies η (rd_entry0_m a b f) ↔ Rd_entry_d (a.eval η).val (b.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (rd_entry0_delta_l a b f) η).trans (rd_entry0_sat_l hZF.1 ..)
  simp only [sh_select_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, pair, entry,
    sh_choice_m, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    fw_relative_sat_l (ZF.modelsKP hZF) source.transitive hz,
    Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hZF.1 source.transitive hz),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hw]
  have wit a i s x (hi : M.mem i ω) (hx : M.mem x (A.eval ρ).val) :=
    source.finite_witness_l hZF (A.eval ρ).property (R.eval ρ).property hm hJ hu hi hx (a := a) (s := s)
  constructor
  · intro h
    refine ⟨hu, hC, hJ, hT, hD, hK, fun p x hpx => ?_⟩
    obtain ⟨t, ht, s, hs, hp⟩ := (hD p).mp (hK.input_mem_of_pairMember hpx)
    obtain ⟨a, ha, i, hi, hti⟩ := (hT t).mp ht
    have hx := hK.output_mem_of_pairMember hpx
    let v : {x // M.mem x Z} := ⟨x, source.transitive _ (A.eval ρ).property x hx⟩
    have choice := h ⟨a, source.transitive _ (C.eval ρ).property a ha⟩ ha
      ⟨i, source.transitive ω source.omega_mem i hi⟩ (hw.symm ▸ hi)
      ⟨t, source.transitive _ (T.eval ρ).property t ht⟩ ht
      ⟨s, source.transitive _ (J.eval ρ).property s hs⟩ hs
      ⟨p, source.transitive _ (D.eval ρ).property p (hK.input_mem_of_pairMember hpx)⟩
      (hK.input_mem_of_pairMember hpx) v hx hti hp hpx
    refine ⟨a, i, t, s, hti, hp, ?_⟩
    rcases choice with h | ⟨none, eq⟩
    · exact Or.inl ((wit a i s x hi hx).mp h)
    · refine Or.inr ⟨?_, congrArg Subtype.val eq⟩
      rintro ⟨y, hy, ht⟩
      exact none ⟨y, source.transitive _ (A.eval ρ).property y hy⟩ hy ((wit a i s y hi hy).mpr ht)
  · intro h a _ i hi t _ s _ p _ x hx ht hp hpx
    have hi : M.mem i.val ω := hw ▸ hi
    rcases h.value_l I ht hp hpx with ht | ⟨none, eq⟩
    · exact Or.inl ((wit a.val i.val s.val x.val hi hx).mpr ht)
    · exact Or.inr ⟨fun y hy h => none ⟨y.val, hy, (wit a.val i.val s.val y.val hi hy).mp h⟩, Subtype.ext eq⟩

theorem Ep_source_d.skolem_sat_l {ω κ K₀ Z W c : M.Domain} (source : Ep_source_d hZF ω κ K₀ Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A R u C J T D K : Term d)
    (hw : (w.eval ρ).val = ω) (hm : Smdl_d I c (A.eval ρ).val (R.eval ρ).val) :
    Formula.satisfies ρ (sh_skolem_m w A R u C J T D K) ↔
      Ssk_d I ω c (A.eval ρ).val (u.eval ρ).val (C.eval ρ).val (J.eval ρ).val
        (T.eval ρ).val (D.eval ρ).val (K.eval ρ).val := by
  have prod (P A B : Term d) : Formula.satisfies ρ (sh_product_m P A B) ↔
      M.IsCartesianProduct I (P.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (sh_product_delta_l P A B) ρ).trans (sh_product_sat_l (ZF.modelsKP hZF) ..)
  have fn : Formula.satisfies ρ (fn0_m D A K) ↔ Fn0_d (D.eval ρ).val (A.eval ρ).val (K.eval ρ).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (fn0_delta_l D A K) ρ).trans (fn0_sat_l hZF.1 ..)
  simp only [sh_skolem_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, prod, fn, hw]
  rw [source.codes_sat_l hZF hz ρ w C hw, source.sequences_sat_l hZF hz ρ w A J hw]
  exact ⟨fun ⟨hu, hC, hJ, hT, hD, hK, hs⟩ => (source.select_sat_l hZF hz ρ w A R u C J T D K hw hm
    hu hC hJ hT hD (fn0_function_l (ZF.modelsKP hZF) hK)).mp hs,
    fun h => ⟨h.point, h.codes, h.params, h.labels, h.domain, fn0_of_function_l (ZF.modelsKP hZF) h.graph,
      (source.select_sat_l hZF hz ρ w A R u C J T D K hw hm h.point h.codes h.params h.labels h.domain h.graph).mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
