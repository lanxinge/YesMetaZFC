import YesMetaZFC.SetTheory.LargeCardinal.IterationColumnPull

/-! # 初等图回拉部分列

支撑列在恒等步处没有值。回拉只反射已有条目，不能给空操作填造支撑。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.partial_column_l {ω B R b U S u π C V f g : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (vt : M.TransitiveSet V)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hCV : Rd_entry_d C V π) (hw : Rd_entry_d ω ω π) (hfg : Rd_entry_d f g π)
    (hf : M.mem f C) (gf : M.IsSetFunction I g) (bound : ∀ i x, Rd_entry_d i x g → M.mem i ω) :
    M.IsSetFunction I f ∧ ∀ i x, Rd_entry_d i x f → M.mem i ω ∧ M.mem x C := by
  let φ : Formula 1 3 := set[3] ⟪∀ p ∈ ⌜(Term.newest : Term 3)⌝ₛ,
    ∃ i ∈ ⌜(Term.bound 2 : Term 3)⌝ₛ, ∃ x ∈ ⌜(Term.bound 1 : Term 3)⌝ₛ, ⌜kpair0_m⌝ₚ(p, i, x)⟫
  have tr := smap_delta_l I hZF hω bt ut mb mu hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases f (Fin.cases C (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases g (Fin.cases V (fun _ => ω)), fun _ => ω⟩ (Fin.cases hfg (Fin.cases hCV (fun _ => hw)))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have shape := tr.mpr (fun p hp => by
    obtain ⟨i, x, pair⟩ := gf.1 p hp
    have hx := rd_entry_transitive_l vt ((hj.member_l I hZF hω mb mu hfg hCV).mp hf) ⟨p, pair, hp⟩
    exact ⟨i, bound i x ⟨p, pair, hp⟩, x, hx.2, pair⟩)
  have bd i x (h : Rd_entry_d i x f) : M.mem i ω ∧ M.mem x C := by
    obtain ⟨p, pair, hp⟩ := h
    obtain ⟨i', hi, x', hx, pair'⟩ := shape p hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    exact ⟨hi, hx⟩
  refine ⟨⟨fun p hp => by obtain ⟨i, _, x, _, pair⟩ := shape p hp; exact ⟨i, x, pair⟩, ?_⟩, bd⟩
  intro i x y hx hy
  have hB := hj.1.1.input_mem_of_pairMember hfg
  obtain ⟨i', _, hi'⟩ := hj.1.1.2.2 i (rd_entry_transitive_l bt hB hx).1
  obtain ⟨x', _, hx'⟩ := hj.1.1.2.2 x (rd_entry_transitive_l bt hB hx).2
  obtain ⟨y', _, hy'⟩ := hj.1.1.2.2 y (rd_entry_transitive_l bt hB hy).2
  have eq := gf.2 i' x' y' ((hj.entry_l hZF hω bt ut mb mu hi' hx' hfg).mp hx)
    ((hj.entry_l hZF hω bt ut mb mu hi' hy' hfg).mp hy)
  exact hj.1.2 x y y' (eq ▸ hx') hy'

theorem Smap_d.partial_entry_preimage_l {ω B R b U S u π C V f g i i' y : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (vt : M.TransitiveSet V)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hCV : Rd_entry_d C V π) (hf : M.mem f C) (gf : M.IsSetFunction I g)
    (hfg : Rd_entry_d f g π) (hi : Rd_entry_d i i' π) (hy : Rd_entry_d i' y g) :
    ∃ x, M.mem x C ∧ Rd_entry_d i x f ∧ Rd_entry_d x y π := by
  have tr := hj.exists_delta_l hZF hω bt ut mb mu
    (.conj (.mem (.newest : Term 4) (.bound 3)) (rd_entry0_m (.bound 2) .newest (.bound 1)))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.conj (.mem ..) (rd_entry0_delta_l ..))
    ⟨Fin.cases f (Fin.cases i (fun _ => C)), fun _ => C⟩
    ⟨Fin.cases g (Fin.cases i' (fun _ => V)), fun _ => V⟩ (Fin.cases hfg (Fin.cases hi (fun _ => hCV)))
  simp only [Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1] at tr
  have hyU := (rd_entry_transitive_l ut (hj.1.1.output_mem_of_pairMember hfg) hy).2
  have hyV := (rd_entry_transitive_l vt ((hj.member_l I hZF hω mb mu hfg hCV).mp hf) hy).2
  obtain ⟨x, hxB, hxC, hix⟩ := tr.mpr ⟨y, hyU, hyV, hy⟩
  obtain ⟨z, _, hxz⟩ := hj.1.1.2.2 x hxB
  exact ⟨x, hxC, hix, gf.2 i' z y ((hj.entry_l hZF hω bt ut mb mu hi hxz hfg).mp hix) hy ▸ hxz⟩

end YesMetaZFC.SetTheory.Internal
