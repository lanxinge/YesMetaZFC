import YesMetaZFC.Model.SetTheory.Internal.PointwiseSyntax

/-! # 逐点翻译的原子与布尔步骤

原子只读取两个代表函数在同一点的值；函数图的单值性给出精确语义。
或非复用已翻译的两行。这两步以及程序扩展均只需要 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pe_atom_step_l (hZF : M.Models ZF) {ω b t F n m G r z i j σ}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hb : Sbound_d I F b)
    (hG : Sfm_d I ω m G) (hc : M.PairMember I r z F)
    (e : Bool) (hs : Sop_d I (if e then 1 else 0) z i j)
    (hσ : M.mem σ ω) (ht : M.mem t σ) (hi : M.mem i σ) (hj : M.mem j σ) :
    ∃ v J k, Sbuild_d I ω m G v J k ∧ ∀ c X R D E, Pe_context_d I ω c X R D E →
      Pe_row_d I b t D X R E F n v J r k := by
  let q : Fin 3 → M.Domain := Fin.cases t (Fin.cases i (fun _ => j))
  let φ : Formula 1 3 := pe_atom_m e (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨v, J, k, h, read⟩ := sfm_template_l I hZF hω hG φ
    (pe_atom_closed_l e _ _ _ rfl rfl rfl) q hσ (Fin.cases ht (Fin.cases hi (fun _ => hj)))
  refine ⟨v, J, k, h, fun c X R D E context p a f hp ha hf _ htp he => ?_⟩
  obtain ⟨ext, model, hE, _, _⟩ := context
  let N := smdl_structure_l I (R := R) model.2.1
  have en := ext.native_l I model.2.1
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨g, x, hgi, hg, hpx, hix⟩ := he i (hb.operands_l I hc hs).1
  obtain ⟨l, y, hlj, hl, hpy, hjy⟩ := he j (hb.operands_l I hc hs).2
  let P : N.Domain := ⟨p, model.2.2.2 p D hp |>.1⟩
  let A : N.Domain := ⟨g, hg.mem_l I⟩
  let B : N.Domain := ⟨l, hl.mem_l I⟩
  let x' : N.Domain := ⟨x, hpx.bounds_l I |>.2.1⟩
  let y' : N.Domain := ⟨y, hpy.bounds_l I |>.2.1⟩
  let ρ : Env N 3 := ⟨Fin.cases P (Fin.cases A (fun _ => B)), fun _ => P⟩
  have new := (read X R model.2.1 E hE a ha ρ (Fin.cases htp (Fin.cases hgi (fun _ => hlj)))).trans
    (pe_atom_sat_l en ρ e (.bound 0) (.bound 1) (.bound 2))
  have value : (∃ u v : N.Domain, Rd_entry_d P u A ∧ Rd_entry_d P v B ∧
      if e then u = v else N.mem u v) ↔ if e then x = y else M.PairMember I x y R := by
    have eqv : (if e then x' = y' else N.mem x' y') ↔ if e then x = y else M.PairMember I x y R := by
      cases e
      · rfl
      · exact Subtype.ext_iff
    refine ⟨?_, fun hh => ⟨x', y', (rf_val_native_l I model.2.1 en P x' A).mp hpx,
      (rf_val_native_l I model.2.1 en P y' B).mp hpy, eqv.mpr hh⟩⟩
    rintro ⟨u, v, hu, hv, hh⟩
    have ex : u = x' := Subtype.ext (hg.unique_l I ext ((rf_val_native_l I model.2.1 en P u A).mpr hu) hpx)
    have ey : v = y' := Subtype.ext (hl.unique_l I ext ((rf_val_native_l I model.2.1 en P v B).mpr hv) hpy)
    exact eqv.mp (ex ▸ ey ▸ hh)
  have old : Ssat_d I X R E F n r f ↔ if e then x = y else M.PairMember I x y R := by
    cases e
    · exact ssat_rel_l I hZF hF hH hc hs hE hf hix hjy
    · exact ssat_eq_l I hZF hF hH hc hs hE hf hix hjy
  exact old.trans (new.trans value).symm

theorem pe_nor_step_l (hZF : M.Models ZF) {ω b t F n m G r c i j u v}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G)
    (hc : M.PairMember I r c F) (hs : Sop_d I 2 c i j) (hu : M.mem u m) (hv : M.mem v m) :
    ∃ l J k, Sbuild_d I ω m G l J k ∧ ∀ c X R D E, Pe_context_d I ω c X R D E →
      Pe_row_d I b t D X R E F n m G i u → Pe_row_d I b t D X R E F n m G j v →
      Pe_row_d I b t D X R E F n l J r k := by
  obtain ⟨l, J, k, h, read⟩ := sfm_nor_l I hZF hω hG hu hv
  refine ⟨l, J, k, h, fun c X R D E _ hi hj p a f hp ha hf hD ht he => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  exact (ssat_nor_l I hZF hF hH hc hs hf).trans ((not_congr
    (or_congr (hi p a f hp ha hf hD ht he) (hj p a f hp ha hf hD ht he))).trans (read X R E a ha).symm)

end YesMetaZFC.SetTheory.Internal
