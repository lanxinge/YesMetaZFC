import YesMetaZFC.Model.SetTheory.Internal.Relativization

/-! # 纯语法限制证书的完整正确性

对原程序行作内部强归纳。此证明适用于任意通过语法检查的翻译，
并不依赖构造编译器时所取的程序或追加见证。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Sr_state_d.correct_l (hZF : M.Models ZF) {ω b F n m G T X R Y S E D r u : M.Domain}
    (hF : Sfm_d I ω n F) (bound : Sbound_d I F b) (h : Sr_state_d I ω b F n m G T)
    (context : Sr_context_d I ω X R Y S E D) (hr : M.mem r n) (hru : M.PairMember I r u T) :
    Sr_row_d I b X R Y S E D F n m G r u := by
  obtain ⟨V, hV⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨W, hW⟩ := seval_exists_l I hZF Y S D G h.program.2.1.1
  let ρ : Env M 12 := ⟨Fin.cases T (Fin.cases G (Fin.cases m (Fin.cases n (Fin.cases F (Fin.cases D
    (Fin.cases E (Fin.cases S (Fin.cases Y (Fin.cases R (Fin.cases X (fun _ => b))))))))))), fun _ => X⟩
  let φ : UnarySchema 12 := { body := .forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (sr_row_m (𝒞 := 𝒞) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)) }
  have sat k : φ.denote ρ k ↔ ∀ v, M.PairMember I k v T → Sr_row_d I b X R Y S E D F n m G k v := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, sr_row_sat_l I hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr) u hru
  intro r hr ih
  apply (sat r).mpr
  intro u hru f g hf hg hbg agree
  have ff := (context.small f).mp hf
  have gg := (context.large g).mp hg
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp hr
  rcases h.rules r c u hc hru with ⟨i, j, code, d, hd, op⟩ | ⟨i, j, code, d, hd, op⟩ |
    ⟨i, j, v, w, code, hiv, hjw, d, hd, op⟩ | ⟨i, j, v, a, p, q, t, code, hjv, ha, hp, hq, ht, hu⟩
  · have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    obtain ⟨x, hx, hix⟩ := ff.2.2 i refs.1
    obtain ⟨y, hy, hjy⟩ := ff.2.2 j refs.2
    have ij := bound.operands_l I hc code
    exact ((ssat_rel_l I hZF hF hV hc code context.small hf hix hjy).trans
      (context.relation x y hx hy)).trans
      (ssat_rel_l I hZF h.program hW hd op context.large hg ((agree i x ij.1).mp hix) ((agree j y ij.2).mp hjy)).symm
  · have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    obtain ⟨x, _, hix⟩ := ff.2.2 i refs.1
    obtain ⟨y, _, hjy⟩ := ff.2.2 j refs.2
    have ij := bound.operands_l I hc code
    exact (ssat_eq_l I hZF hF hV hc code context.small hf hix hjy).trans
      (ssat_eq_l I hZF h.program hW hd op context.large hg ((agree i x ij.1).mp hix) ((agree j y ij.2).mp hjy)).symm
  · have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    rw [ssat_nor_l I hZF hF hV hc code hf, ssat_nor_l I hZF h.program hW hd op hg]
    exact not_congr (or_congr ((sat i).mp (ih i refs.1) v hiv f g hf hg hbg agree)
      ((sat j).mp (ih j refs.2) w hjw f g hf hg hbg agree))
  · obtain ⟨ca, hca, opa⟩ := ha
    obtain ⟨cp, hcp, opp⟩ := hp
    obtain ⟨cq, hcq, opq⟩ := hq
    obtain ⟨ct, hct, opt⟩ := ht
    obtain ⟨cu, hcu, opu⟩ := hu
    have refs := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) code
    have hbi : b ≠ i := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b
      (eq.symm ▸ (bound.operands_l I hc code).1)
    have body x g' (hx : M.mem x Y) (update : Senv_update_d I g i x g') :
        Ssat_d I Y S D G m t g' ↔ M.mem x X ∧ Ssat_d I Y S D G m v g' := by
      have hg' := (context.large g').mpr (update.function_l I gg refs.1 hx)
      rw [ssat_nor_l I hZF h.program hW hct opt hg', ssat_nor_l I hZF h.program hW hcp opp hg',
        ssat_nor_l I hZF h.program hW hcq opq hg', ssat_rel_l I hZF h.program hW hca opa context.large hg'
          ((update.2 i x).mpr (Or.inl ⟨rfl, rfl⟩)) ((update.2 b X).mpr (Or.inr ⟨hbi, hbg⟩)), context.guard x hx]
      simp only [or_self, not_or, Classical.not_not]
    have transport x f' g' (hx : M.mem x X) (uf : Senv_update_d I f i x f') (ug : Senv_update_d I g i x g') :
        Ssat_d I X R E F n j f' ↔ Ssat_d I Y S D G m v g' :=
      (sat j).mp (ih j refs.2) v hjv f' g'
        ((context.small f').mpr (uf.function_l I ff refs.1 hx))
        ((context.large g').mpr (ug.function_l I gg refs.1 (context.subset x hx)))
        ((ug.2 b X).mpr (Or.inr ⟨hbi, hbg⟩)) (agree.update_l I uf ug)
    rw [ssat_exists_l I hZF hF hV hc code hf, ssat_exists_l I hZF h.program hW hcu opu hg]
    constructor
    · rintro ⟨x, f', hx, uf, truth⟩
      obtain ⟨g', ug, _⟩ := senv_update_exists_l I hZF gg refs.1 (context.subset x hx)
      exact ⟨x, g', context.subset x hx, ug, (body x g' (context.subset x hx) ug).mpr
        ⟨hx, (transport x f' g' hx uf ug).mp truth⟩⟩
    · rintro ⟨x, g', hx, ug, truth⟩
      obtain ⟨hxX, truth'⟩ := (body x g' hx ug).mp truth
      obtain ⟨f', uf, _⟩ := senv_update_exists_l I hZF ff refs.1 hxX
      exact ⟨x, f', hxX, uf, (transport x f' g' hxX uf ug).mpr truth'⟩

end YesMetaZFC.SetTheory.Internal
