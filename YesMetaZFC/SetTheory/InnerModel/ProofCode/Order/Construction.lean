import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Certificate

/-! # 比较证书的拼接与展开 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem po_extend_l (hM : M.Models KPi) {A T F h c d : M.Domain}
    (hf : Po_cert_d F A) (hn : KP.N0_d h) (hs : Po_step_d T (Pc_read_d F h) c d) : Po_lt_d c d := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨r, hr⟩ := pc_triple_exists_l hKP h c d
  obtain ⟨G, hg⟩ := KP.exists_insert hKP F r
  obtain ⟨U, hu, hU⟩ := pc_cover_l hM [A, T, G, h, c, d]
  have ai := hu A (hU A (by simp))
  have ti := hu T (hU T (by simp))
  have fi : M.MemberSubset F G := fun s hs => (hg s).mpr (Or.inl hs)
  have read n a b : Pc_read_d F n a b → Pc_read_d G n a b :=
    fun ⟨m, hm, s, hs, he⟩ => ⟨m, hm, s, fi s hs, he⟩
  refine ⟨h, U, G, ⟨hu, hU G (by simp), ?_⟩, r, (hg r).mpr (Or.inr rfl), hr⟩
  intro s hsg
  rcases (hg s).mp hsg with hs | rfl
  · obtain ⟨n, hn, a, ha, b, hb, he, ho, hs⟩ := hf.row s hs
    exact ⟨n, ai n hn, a, ai a ha, b, ai b hb, he, ho, po_step_mono_l ai (read n) hs⟩
  · exact ⟨h, hU h (by simp), c, hU c (by simp), d, hU d (by simp), hr, hn, po_step_mono_l ti (read h) hs⟩

theorem po_close_l (hM : M.Models KPi) {T c d : M.Domain} (hs : Po_step_d T Po_lt_d c d) : Po_lt_d c d := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have base (hs : Po_step_d T (fun _ _ => False) c d) : Po_lt_d c d := by
    obtain ⟨F, he⟩ := KP.exists_empty hKP
    obtain ⟨A, ha, hA⟩ := pc_cover_l hM [F]
    exact po_extend_l hM ⟨ha, hA F (by simp), fun r hr => (he r hr).elim⟩ (KP.n0_empty_l he)
      (po_step_mono_l (fun _ h => h) (fun _ _ h => h.elim) hs)
  rcases hs with hl | ht | ⟨k, a, ha, b, hb, e, he, x, hx, y, hy, z, hz, hc, hd, hs⟩
  · exact base (Or.inl hl)
  · exact base (Or.inr (Or.inl ht))
  have lift (p q : M.Domain) (hpq : Po_lt_d p q)
      (hh : Po_lex_d (fun i j => i = p ∧ j = q) a b e x y z) : Po_lt_d c d := by
    obtain ⟨n, A, F, hf, hpq⟩ := hpq
    obtain ⟨s, hs⟩ := KP.exists_successor hKP n
    have hn := (hf.at_l hpq).2.2.2.1
    apply po_extend_l hM hf (KP.n0_succ_l hKP.1 hn hs)
    exact po_step_mono_l (fun _ h => h)
      (fun i j ⟨hi, hj⟩ => ⟨n, hs.predecessor_mem, hi.symm ▸ hj.symm ▸ hpq⟩)
      (Or.inr (Or.inr ⟨k, a, ha, b, hb, e, he, x, hx, y, hy, z, hz, hc, hd, hh⟩))
  rcases hs with h | ⟨h, g | ⟨g, f⟩⟩
  · exact lift a x h (Or.inl ⟨rfl, rfl⟩)
  · exact lift b y g (Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩)
  · exact lift e z f (Or.inr ⟨h, Or.inr ⟨g, rfl, rfl⟩⟩)

theorem po_unfold_l {c d : M.Domain} (h : Po_lt_d c d) : ∃ T, Po_step_d T Po_lt_d c d := by
  obtain ⟨n, T, F, hf, hc⟩ := h
  exact ⟨T, po_step_mono_l (fun _ h => h)
    (fun _ _ ⟨m, hm⟩ => ⟨m, T, F, hf, hm.2⟩) (hf.at_l hc).2.2.2.2⟩

end YesMetaZFC.SetTheory.InnerModel
