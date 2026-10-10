import YesMetaZFC.SetTheory.InnerModel.ProofCode.Parser.Step

/-! # 在给定内部高度重建语法证书 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem ps_step_mono_l {T U F G h c : M.Domain} (ht : M.MemberSubset T U) (hf : M.MemberSubset F G) :
    Ps_step_d T F h c → Ps_step_d U G h c := by
  have read {a} : Ps_read_d F h a → Ps_read_d G h a := fun ⟨n, hn, p, hp, hpf⟩ => ⟨n, hn, p, hp, hf p hpf⟩
  rintro (⟨a, ha, hc, ho⟩ | ⟨k, a, ha, b, hb, d, hd, hc, h1, h2, h3⟩)
  · exact Or.inl ⟨a, ht a ha, po_leaf_mono_l ht hc, ho⟩
  · exact Or.inr ⟨k, a, ht a ha, b, ht b hb, d, ht d hd, po_node_mono_l ht hc, read h1, read h2, read h3⟩

theorem ps_extend_l (hM : M.Models KPi) {A T F h c : M.Domain}
    (hf : Ps_cert_d F A) (hn : KP.N0_d h) (hs : Ps_step_d T F h c) : Ps_rank_d h c := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total h c
  obtain ⟨G, hg⟩ := KP.exists_insert hKP F p
  obtain ⟨U, hu, hU⟩ := pc_cover_l hM [A, T, G, h, c]
  have ai := hu A (hU A (by simp))
  have ti := hu T (hU T (by simp))
  have fi : M.MemberSubset F G := fun r hr => (hg r).mpr (Or.inl hr)
  refine ⟨U, G, ⟨hu, hU G (by simp), ?_⟩, p, hp, (hg p).mpr (Or.inr rfl)⟩
  intro r hr
  rcases (hg r).mp hr with hr | rfl
  · obtain ⟨n, hn, d, hd, he, ho, hr⟩ := hf.row r hr
    exact ⟨n, ai n hn, d, ai d hd, he, ho, ps_step_mono_l ai fi hr⟩
  · exact ⟨h, hU h (by simp), c, hU c (by simp), hp, hn, ps_step_mono_l ti fi hs⟩

theorem ps_leaf_rank_l (hM : M.Models KPi) {h T c a : M.Domain} (hh : KP.N0_d h)
    (hc : Pc_leaf_d T c a) (ha : M.IsOrdinal a) : Ps_rank_d h c := by
  obtain ⟨F, he⟩ := KP.exists_empty (KPi.models_iff_l.mp hM).1
  obtain ⟨U, hu, hU⟩ := pc_cover_l hM [F, T, a]
  exact ps_extend_l hM ⟨hu, hU F (by simp), fun r hr => (he r hr).elim⟩ hh
    (Or.inl ⟨a, hU a (by simp), po_leaf_mono_l (hu T (hU T (by simp))) hc, ha⟩)

theorem ps_node_rank_l (hM : M.Models KPi) {h T c a b d : M.Domain} {k} (hh : KP.N0_d h)
    (hc : Pc_node_d T k c a b d) (ha : ∃ i, M.mem i h ∧ Ps_rank_d i a)
    (hb : ∃ j, M.mem j h ∧ Ps_rank_d j b) (hd : ∃ l, M.mem l h ∧ Ps_rank_d l d) : Ps_rank_d h c := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨i, hi, A, F, hf, ha⟩ := ha
  obtain ⟨j, hj, B, G, hg, hb⟩ := hb
  obtain ⟨l, hl, C, H, hhf, hd⟩ := hd
  obtain ⟨E, he⟩ := KP.exists_unionOfTwo hKP F G
  obtain ⟨D, hD⟩ := KP.exists_unionOfTwo hKP E H
  have fi : M.MemberSubset F D := fun r hr => (hD r).mpr (Or.inl ((he r).mpr (Or.inl hr)))
  have gi : M.MemberSubset G D := fun r hr => (hD r).mpr (Or.inl ((he r).mpr (Or.inr hr)))
  have hi' : M.MemberSubset H D := fun r hr => (hD r).mpr (Or.inr hr)
  obtain ⟨U, hu, hU⟩ := pc_cover_l hM [A, B, C, T, D, a, b, d]
  have old {V W} (hf : Ps_cert_d V W) (hw : M.MemberSubset W U) (hf' : M.MemberSubset V D) (r : M.Domain) (hr : M.mem r V) :
      ∃ n, M.mem n U ∧ ∃ c, M.mem c U ∧ KPair_d M r n c ∧ KP.N0_d n ∧ Ps_step_d U D n c := by
    obtain ⟨n, hn, c, hc, hp, ho, hs⟩ := hf.row r hr
    exact ⟨n, hw n hn, c, hw c hc, hp, ho, ps_step_mono_l hw hf' hs⟩
  have cert : Ps_cert_d D U := ⟨hu, hU D (by simp), fun r hr =>
    ((hD r).mp hr).elim (fun hr => ((he r).mp hr).elim
      (old hf (hu A (hU A (by simp))) fi r) (old hg (hu B (hU B (by simp))) gi r))
      (old hhf (hu C (hU C (by simp))) hi' r)⟩
  have read {V n x} (hv : M.MemberSubset V D) (hn : M.mem n h) (hx : Rd_entry_d n x V) : Ps_read_d D h x :=
    ⟨n, hn, hx.elim fun p hp => ⟨p, hp.1, hv p hp.2⟩⟩
  exact ps_extend_l hM cert hh (Or.inr ⟨k, a, hU a (by simp), b, hU b (by simp), d, hU d (by simp),
    po_node_mono_l (hu T (hU T (by simp))) hc, read fi hi ha, read gi hj hb, read hi' hl hd⟩)

end YesMetaZFC.SetTheory.InnerModel
