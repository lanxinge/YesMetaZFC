import YesMetaZFC.SetTheory.LargeCardinal.DerivedEvaluation

/-! # 派生求值保持带谓词的关系原子

真值集用背景分离得到，并由完整幂集包含于源证明可输入原嵌入。
图求值使用解码后的成员语言；最后的关系原子直接保留谓词结构的关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ed_predicate_trace_l {ω c X A R d Y B S j f g H f' g' H' : M.Domain}
    (hω : M.IsOmega ω) (hx : Spred_d I c X A R) (hy : Spred_d I d Y B S)
    (hj : Smap_d I ω c d X Y j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hf : Rd_entry_d f f' j) (hg : Rd_entry_d g g' j) (hH : Rd_entry_d H H' j)
    (trace : ∀ u v w, M.mem u X → M.mem v X → M.mem w X → Rd_entry_d u v f → Rd_entry_d u w g →
      (M.mem u H ↔ Rd_entry_d v w R)) :
    ∀ u v w, M.mem u Y → M.mem v Y → M.mem w Y → Rd_entry_d u v f' → Rd_entry_d u w g' →
      (M.mem u H' ↔ Rd_entry_d v w S) := by
  let decode {n} (φ : Formula 1 n) := spred_core_l (source_core_l φ)
  have read {Z P T e} (he : Spred_d I e Z P T) (ht : M.TransitiveSet Z) {n}
      (φ : Formula 1 n) (hd : φ.IsDelta0) (ρ : Env (smdl_structure_l I (R := T) he.1.2.1) n) :
      Formula.satisfies ρ (decode φ) ↔ Formula.satisfies ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩ φ := by
    obtain ⟨z, hz⟩ := he.1.2.1
    let hn : Nonempty {x // M.mem x Z} := ⟨⟨z, hz⟩⟩
    let ρ' : Env (rt_model_l Z hn) n := ⟨ρ.bound, ρ.free⟩
    exact (spred_core_sat_l I (ZF.modelsKP hZF) he hn (source_core_l φ) ρ').trans
      ((source_core_sat_l φ ρ').trans (rt_model_delta_l ht hn hd ρ'))
  let φ : Formula 1 3 := .forallE (.forallE (.forallE (.imp
    (decode (.conj (rd_entry0_m (.bound 2) (.bound 1) (.bound 3)) (rd_entry0_m (.bound 2) .newest (.bound 4))))
    (.iff (decode (.mem (.bound 2) (.bound 5))) (.mem (.bound 1) .newest)))))
  let ρ : Env (smdl_structure_l I (R := R) hx.1.2.1) 3 := {
    bound := Fin.cases ⟨f, hj.1.1.input_mem_of_pairMember hf⟩
      (Fin.cases ⟨g, hj.1.1.input_mem_of_pairMember hg⟩ (fun _ => ⟨H, hj.1.1.input_mem_of_pairMember hH⟩))
    free := fun _ => ⟨f, hj.1.1.input_mem_of_pairMember hf⟩ }
  let η : Env (smdl_structure_l I (R := S) hy.1.2.1) 3 := {
    bound := Fin.cases ⟨f', hj.1.1.output_mem_of_pairMember hf⟩
      (Fin.cases ⟨g', hj.1.1.output_mem_of_pairMember hg⟩ (fun _ => ⟨H', hj.1.1.output_mem_of_pairMember hH⟩))
    free := fun _ => ⟨f', hj.1.1.output_mem_of_pairMember hf⟩ }
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj φ (by
    simp only [φ, Definitional.Formula.FreeClosed]
    exact ⟨spred_core_closed_l _ (source_core_closed_l _ (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])),
      spred_core_closed_l _ (source_core_closed_l _ (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])), by simp⟩)
    ρ η (Fin.cases hf (Fin.cases hg (fun _ => hH)))
  have source : Formula.satisfies ρ φ := by
    simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
      read hx hX _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)), read hx hX _ (.mem _ _),
      Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]
    exact fun u v w huv => trace u.val v.val w.val u.property v.property w.property huv.1 huv.2
  have target := tr.mp source
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    read hy hY _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)), read hy hY _ (.mem _ _),
    Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff] at target
  exact fun u v w hu hv hw huv huw => target ⟨u, hu⟩ ⟨v, hv⟩ ⟨w, hw⟩ ⟨huv, huw⟩

theorem ed_predicate_evaluation_l {ω c X A R d Y B S j D D' a U P f g y z : M.Domain}
    (hω : M.IsOmega ω) (hx : Spred_d I c X A R) (hy : Spred_d I d Y B S)
    (hj : Smap_d I ω c d X Y j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hD : Rd_entry_d D D' j) (ha : M.mem a D') (hP : M.IsPowerSetOf P D) (hPX : M.MemberSubset P X)
    (hU : Ed_filter_d I j a D U) (hf : Sfun_d X D f) (hg : Sfun_d X D g)
    (ey : Ee_value_d j a f y) (ez : Ee_value_d j a g z) : Rp_rel_d I X U R f g ↔ Rd_entry_d y z S := by
  have h : Spred_emb_d I ω X A Y B j := ⟨c, R, d, S, hx, hy, hj⟩
  obtain ⟨_, C, hC, hf⟩ := hf
  obtain ⟨_, E, hE, hg⟩ := hg
  obtain ⟨f', hjf, hay⟩ := ey
  obtain ⟨g', hjg, haz⟩ := ez
  obtain ⟨C', hC', hjC⟩ := hj.1.1.2.2 C hC
  obtain ⟨E', hE', hjE⟩ := hj.1.1.2.2 E hE
  have ff := (spred_function_l I hZF hω h hX hY hD hjC hjf).mp hf
  have gg := (spred_function_l I hZF hω h hX hY hD hjE hjg).mp hg
  let ρ := (((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push f).push g
  let φ : UnarySchema 4 := { body := rp_atom_m (𝒞 := kpair_convention_l) false (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨H, hs⟩ := ZF.separation_exists_d hZF φ ρ D
  have spec v : M.mem v H ↔ M.mem v D ∧ Rp_atom_d I false X R f g v :=
    (hs v).trans (and_congr_right fun _ => rp_atom_sat_l I hZF.1 false ..)
  have hHX := hPX H ((hP H).mpr fun v hv => ((spec v).mp hv).1)
  obtain ⟨H', _, hjH⟩ := hj.1.1.2.2 H hHX
  have tr := ed_predicate_trace_l hZF hω hx hy hj hX hY hjf hjg hjH (fun u v w _ hv hw huv huw =>
    (spec u).trans ⟨fun ⟨_, x, _, t, _, hux, hut, hxt⟩ =>
      (fn0_function_l (ZF.modelsKP hZF) hf).1.2 u x v hux huv ▸
        (fn0_function_l (ZF.modelsKP hZF) hg).1.2 u t w hut huw ▸ hxt,
      fun hvw => ⟨(hf.bound_l huv).1, v, hv, w, hw, huv, huw, hvw⟩⟩)
  have value := tr a y z (hY D' (hj.1.1.output_mem_of_pairMember hD) a ha)
    (hY C' hC' y (ff.bound_l hay).2) (hY E' hE' z (gg.bound_l haz).2) hay haz
  have measure := (ed_filter_member_l I hj.1.1.1 hU (fun v hv => ((spec v).mp hv).1) hjH).trans value
  refine ⟨fun ⟨W, hw, truth⟩ => measure.mp ?_, fun ht =>
    ⟨H, measure.mpr ht, fun v hv => ((spec v).mp hv).2⟩⟩
  obtain ⟨hWD, W', hjW, haW⟩ := (hU W).mp hw
  exact (hU H).mpr ⟨fun v hv => ((spec v).mp hv).1, H', hjH,
    (ed_subset_l I hZF hω h hX hY hjW hjH).mp
      (fun v hv => (spec v).mpr ⟨hWD v hv, truth v hv⟩) a haW⟩

end YesMetaZFC.SetTheory.LargeCardinal
