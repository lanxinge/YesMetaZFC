import YesMetaZFC.Model.SetTheory.Internal.PointwiseSyntax

/-! # 逐点翻译的原子与布尔步骤

原子只读取两个代表函数在同一点的值；函数图的单值性给出精确语义。
或非复用已翻译的两行。这两步以及程序扩展均只需要 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pe_atom_step_l (hZF : M.Models ZF) {ω b t D X R E F n H m G r c z i j σ}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hE : M.IsFunctionSpace I E ω X)
    (hb : Sbound_d I F b) (hG : Sfm_d I ω m G) (hc : M.PairMember I r z F)
    (e : Bool) (hs : Sop_d I (if e then 1 else 0) z i j)
    (hσ : M.mem σ ω) (ht : M.mem t σ) (hi : M.mem i σ) (hj : M.mem j σ) :
    ∃ v J k, Sbuild_d I ω m G v J k ∧ Pe_row_d I b t D X R E F n v J r k := by
  let q : Fin 3 → M.Domain := Fin.cases t (Fin.cases i (fun _ => j))
  let φ : Formula 1 3 := pe_atom_m e (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨v, J, k, h, read⟩ := sfm_delta_l I hZF hω hG φ
    (pe_atom_closed_l e _ _ _ rfl rfl rfl) (pe_atom_delta_l ..) q hσ (Fin.cases ht (Fin.cases hi (fun _ => hj)))
  refine ⟨v, J, k, h, fun p a f hp ha hf _ htp he => ?_⟩
  obtain ⟨g, x, hgi, hg, hpx, hix⟩ := he i (hb.operands_l I hc hs).1
  obtain ⟨l, y, hlj, hl, hpy, hjy⟩ := he j (hb.operands_l I hc hs).2
  let ρ : Env M 3 := ⟨Fin.cases p (Fin.cases g (fun _ => l)), fun _ => p⟩
  have new := (read X R E c a ρ hX hm hE ha (Fin.cases htp (Fin.cases hgi (fun _ => hlj)))).trans
    (pe_atom_sat_l hZF.1 ρ e (.bound 0) (.bound 1) (.bound 2))
  have value : (∃ x' y', Rd_entry_d p x' g ∧ Rd_entry_d p y' l ∧
      if e then x' = y' else M.mem x' y') ↔ if e then x = y else M.mem x y := by
    refine ⟨?_, fun hh => ⟨x, y, hpx, hpy, hh⟩⟩
    rintro ⟨x', y', hx', hy', hh⟩
    have ex := (fn0_function_l (ZF.modelsKP hZF) (hg.function_l hX)).1.2 p x' x hx' hpx
    have ey := (fn0_function_l (ZF.modelsKP hZF) (hl.function_l hX)).1.2 p y' y hy' hpy
    exact ex ▸ ey ▸ hh
  have old : Ssat_d I X R E F n r f ↔ if e then x = y else M.mem x y := by
    cases e
    · exact (ssat_rel_l I hZF hF hH hc hs hE hf hix hjy).trans ((hm.2 x y).trans
        ⟨fun h => h.2.2, fun h => ⟨((hE f).mp hf).output_mem_of_pairMember hix,
          ((hE f).mp hf).output_mem_of_pairMember hjy, h⟩⟩)
    · exact ssat_eq_l I hZF hF hH hc hs hE hf hix hjy
  exact old.trans (new.trans value).symm

theorem pe_nor_step_l (hZF : M.Models ZF) {ω b t D X R E F n H m G r c i j u v}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H)
    (hG : Sfm_d I ω m G) (hc : M.PairMember I r c F) (hs : Sop_d I 2 c i j)
    (hu : M.mem u m) (hv : M.mem v m) (hi : Pe_row_d I b t D X R E F n m G i u)
    (hj : Pe_row_d I b t D X R E F n m G j v) :
    ∃ l J k, Sbuild_d I ω m G l J k ∧ Pe_row_d I b t D X R E F n l J r k := by
  obtain ⟨l, J, k, h, read⟩ := sfm_nor_l I hZF hω hG hu hv
  refine ⟨l, J, k, h, fun p a f hp ha hf hD ht he => ?_⟩
  exact (ssat_nor_l I hZF hF hH hc hs hf).trans ((not_congr
    (or_congr (hi p a f hp ha hf hD ht he) (hj p a f hp ha hf hD ht he))).trans (read X R E a ha).symm)

end YesMetaZFC.SetTheory.Internal
