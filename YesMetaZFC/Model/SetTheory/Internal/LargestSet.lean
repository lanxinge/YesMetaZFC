import YesMetaZFC.Model.SetTheory.Internal.LargestSetCode

/-! # 最大集合指令的完整语义

两个新变量寻找一个集合及其未被候选最大集合包含的成员。
传递性保证所有反例成员仍在量词域内，故七条指令精确表达最大性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Sr_top_code_d.correct_l (hZF : M.Models ZF) {ω b G m w c Y S D g X : M.Domain}
    (hω : M.IsOmega ω) (hG : Sfm_d I ω m G) (h : Sr_top_code_d I b G w)
    (hm : Smem_d I c Y S) (hY : M.TransitiveSet Y) (hD : M.IsFunctionSpace I D ω Y)
    (hg : M.mem g D) (hx : M.PairMember I b X g) : Ssat_d I Y S D G m w g ↔ Sr_top_d Y X := by
  obtain ⟨i, j, a, d, e, t, u, v, hi, hj, ha, hd, he, ht, hu, hv, hw⟩ := h
  obtain ⟨ca, hca, opa⟩ := ha
  obtain ⟨cd, hcd, opd⟩ := hd
  obtain ⟨ce, hce, ope⟩ := he
  obtain ⟨ct, hct, opt⟩ := ht
  obtain ⟨cu, hcu, opu⟩ := hu
  obtain ⟨cv, hcv, opv⟩ := hv
  obtain ⟨cw, hcw, opw⟩ := hw
  obtain ⟨V, hV⟩ := seval_exists_l I hZF Y S D G hG.2.1.1
  have refs := (hG.2.2 a ca hca).refs_l I (ZF.modelsKP hZF) opa
  have hjOrd := hω.members_areOrdinals hZF j refs.1
  have hbj := hjOrd.transitive i hj.predecessor_mem b hi.predecessor_mem
  have ne {x y : M.Domain} (h : M.mem x y) : x ≠ y := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) y (eq ▸ h)
  have hbi := ne hi.predecessor_mem
  have hbj' := ne hbj
  have hij := ne hj.predecessor_mem
  have fn := (hD g).mp hg
  have hXY := fn.output_mem_of_pairMember hx
  have body A g' B g'' (hA : M.mem A Y) (hB : M.mem B Y)
      (ui : Senv_update_d I g i A g') (uj : Senv_update_d I g' j B g'') :
      Ssat_d I Y S D G m t g'' ↔ M.mem B A ∧ ¬ M.mem B X := by
    have fg := ui.function_l I fn refs.2 hA
    have hg'' := (hD g'').mpr (uj.function_l I fg refs.1 hB)
    have hBv := (uj.2 j B).mpr (Or.inl ⟨rfl, rfl⟩)
    have hAv := (uj.2 i A).mpr (Or.inr ⟨hij, (ui.2 i A).mpr (Or.inl ⟨rfl, rfl⟩)⟩)
    have hXv := (uj.2 b X).mpr (Or.inr ⟨hbj', (ui.2 b X).mpr (Or.inr ⟨hbi, hx⟩)⟩)
    rw [ssat_nor_l I hZF hG hV hct opt hg'', ssat_nor_l I hZF hG hV hce ope hg'',
      ssat_rel_l I hZF hG hV hca opa hD hg'' hBv hAv,
      ssat_rel_l I hZF hG hV hcd opd hD hg'' hBv hXv, hm.2 B A, hm.2 B X]
    simp only [hB, hA, hXY, true_and, or_self, not_or, Classical.not_not]
  have bad : Ssat_d I Y S D G m v g ↔ ∃ A B, M.mem A Y ∧ M.mem B Y ∧ M.mem B A ∧ ¬ M.mem B X := by
    rw [ssat_exists_l I hZF hG hV hcv opv hg]
    constructor
    · rintro ⟨A, g', hA, ui, truth⟩
      have hg' := (hD g').mpr (ui.function_l I fn refs.2 hA)
      obtain ⟨B, g'', hB, uj, truth⟩ := (ssat_exists_l I hZF hG hV hcu opu hg').mp truth
      exact ⟨A, B, hA, hB, (body A g' B g'' hA hB ui uj).mp truth⟩
    · rintro ⟨A, B, hA, hB, hBA, hBX⟩
      obtain ⟨g', ui, fg⟩ := senv_update_exists_l I hZF fn refs.2 hA
      obtain ⟨g'', uj, _⟩ := senv_update_exists_l I hZF fg refs.1 hB
      exact ⟨A, g', hA, ui, (ssat_exists_l I hZF hG hV hcu opu ((hD g').mpr fg)).mpr
        ⟨B, g'', hB, uj, (body A g' B g'' hA hB ui uj).mpr ⟨hBA, hBX⟩⟩⟩
  rw [ssat_nor_l I hZF hG hV hcw opw hg, or_self, bad]
  constructor
  · intro h
    exact ⟨hXY, fun A hA B hBA => Classical.byContradiction fun hn => h ⟨A, B, hA, hY A hA B hBA, hBA, hn⟩⟩
  · rintro h ⟨A, B, hA, _, hBA, hBX⟩
    exact hBX (h.2 A hA B hBA)

end YesMetaZFC.SetTheory.Internal
