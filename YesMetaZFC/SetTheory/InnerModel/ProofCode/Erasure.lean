import YesMetaZFC.SetTheory.InnerModel.ProofCode.WellFormed
import YesMetaZFC.SetTheory.InnerModel.ProofCode.Coverage

/-! # 擦除值列与合法码的精确求值域 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

/-- 给已有传递集合加入一张坐标落在其中的对表，只需有限次并集。 -/
private theorem pc_table_cover_l (hKP : M.Models KP) {U D : M.Domain} (hu : M.TransitiveSet U)
    (hd : ∀ r, M.mem r D → ∃ a, M.mem a U ∧ ∃ b, M.mem b U ∧ KPair_d M r a b) :
    ∃ T, M.TransitiveSet T ∧ M.MemberSubset U T ∧ M.mem D T := by
  obtain ⟨V, hv⟩ := KP.exists_union hKP D
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo hKP U D
  obtain ⟨X, hx⟩ := KP.exists_unionOfTwo hKP W V
  obtain ⟨T, ht⟩ := KP.exists_insert hKP X D
  have hi z : M.mem z T ↔ ((M.mem z U ∨ M.mem z D) ∨ M.mem z V) ∨ z = D := by rw [ht z, hx z, hw z]
  refine ⟨T, fun z hz t htz => ?_, fun z hz => (hi z).mpr (Or.inl (Or.inl (Or.inl hz))), (ht D).mpr (Or.inr rfl)⟩
  apply (hi t).mpr
  rcases (hi z).mp hz with ((hz | hz) | hz) | rfl
  · exact Or.inl (Or.inl (Or.inl (hu z hz t htz)))
  · exact Or.inl (Or.inr ((hv t).mpr ⟨z, hz, htz⟩))
  · obtain ⟨r, hr, hz⟩ := (hv z).mp hz
    obtain ⟨a, ha, b, hb, hp⟩ := hd r hr
    exact Or.inl (Or.inl (Or.inl (((kpair_union_l M hp t).mp ⟨z, hz, htz⟩).elim
      (fun he => he.symm ▸ ha) (fun he => he.symm ▸ hb))))
  · exact Or.inl (Or.inl (Or.inr htz))

theorem pc_eval_valid_l (hKP : M.Models KP) {c x : M.Domain} (hx : Pc_eval_d c x) : Ps_valid_d c := by
  obtain ⟨h, U, F, hf, hc⟩ := hx
  let ρ : Env M 1 := rd_seed_env_l U
  let φ : Delta0BinarySchema 1 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
      (.conj (rd_triple0_m (.bound 4) (.bound 2) (.bound 1) .newest) (kpair0_m (.bound 3) (.bound 2) (.bound 1)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_triple0_delta_l ..) (kpair0_delta_l ..)))) }
  have hφ r p : φ.toBinarySchema.denote ρ r p ↔ ∃ n, M.mem n U ∧ ∃ d, M.mem d U ∧ ∃ y, M.mem y U ∧
      Rd_triple_d r n d y ∧ KPair_d M p n d := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_triple0_sat_l hKP.1, kpair0_sat_l hKP.1]; rfl
  obtain ⟨D, hD⟩ := KP.d0_image_l hKP φ ρ F (by
    intro r hr
    obtain ⟨n, hn, d, hd, y, hy, hp, _⟩ := hf.row r hr
    obtain ⟨p, hc⟩ := (kp_pair_l hKP).total n d
    exact ⟨p, (hφ r p).mpr ⟨n, hn, d, hd, y, hy, hp, hc⟩⟩) (by
    intro r _ p q hp hq
    obtain ⟨n, _, d, _, y, _, hr, hp⟩ := (hφ r p).mp hp
    obtain ⟨m, _, e, _, z, _, hs, hq⟩ := (hφ r q).mp hq
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hr hs
    exact kpair_unique_l M hKP.1 hp hq)
  have entry n d : Rd_entry_d n d D ↔ ∃ y, Pc_at_d F n d y := by
    constructor
    · rintro ⟨p, hp, hpd⟩
      obtain ⟨r, hr, hg⟩ := (hD p).mp hpd
      obtain ⟨m, _, e, _, y, _, hs, hg⟩ := (hφ r p).mp hg
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hg hp
      exact ⟨y, r, hr, hs⟩
    · rintro ⟨y, r, hr, hp⟩
      obtain ⟨p, hg⟩ := (kp_pair_l hKP).total n d
      have hb := hf.at_l ⟨r, hr, hp⟩
      exact ⟨p, hg, (hD p).mpr ⟨r, hr, (hφ r p).mpr ⟨n, hb.1, d, hb.2.1, y, hb.2.2.1, hp, hg⟩⟩⟩
  obtain ⟨T, ht, ui, hDT⟩ := pc_table_cover_l hKP hf.trans (by
    intro p hp
    obtain ⟨r, _, h⟩ := (hD p).mp hp
    obtain ⟨n, hn, d, hd, _, _, _, hp⟩ := (hφ r p).mp h
    exact ⟨n, hn, d, hd, hp⟩)
  have read {n d y} (h : Pc_read_d F n d y) : Ps_read_d D n d :=
    h.elim fun m hm => ⟨m, hm.1, (entry m d).mpr ⟨y, hm.2⟩⟩
  have cert : Ps_cert_d D T := by
    refine ⟨ht, hDT, fun p hp => ?_⟩
    obtain ⟨r, hr, hg⟩ := (hD p).mp hp
    obtain ⟨n, hn, d, hd, y, _, hs, hp⟩ := (hφ r p).mp hg
    have hh := hf.at_l ⟨r, hr, hs⟩
    refine ⟨n, ui n hn, d, ui d hd, hp, hh.2.2.2.1, ?_⟩
    rcases hh.2.2.2.2 with ⟨a, ha, ⟨e, he, hz, hc⟩, ho, _⟩ |
      ⟨k, a, ha, b, hb, c, hc, u, _, v, _, w, _, ⟨tag, htag, q, hq, ho, hargs, hcode⟩, h1, h2, h3, _⟩
    · exact Or.inl ⟨a, ui a ha, ⟨e, ui e he, hz, hc⟩, ho⟩
    · exact Or.inr ⟨k, a, ui a ha, b, ui b hb, c, ui c hc,
        ⟨tag, ui tag htag, q, ui q hq, ho, hargs, hcode⟩, read h1, read h2, read h3⟩
  exact ⟨h, T, D, cert, (entry h c).mpr ⟨x, hc⟩⟩

theorem ps_valid_iff_l (hM : M.Models KPi) (c : M.Domain) : Ps_valid_d c ↔ ∃ x, Pc_eval_d c x :=
  ⟨ps_eval_total_l hM, fun ⟨_, h⟩ => pc_eval_valid_l (KPi.models_iff_l.mp hM).1 h⟩

theorem pc_valid_cover_l (hM : M.Models KPi) (x : M.Domain) :
    L_d x ↔ ∃ c, Ps_valid_d c ∧ Pc_eval_d c x := by
  refine ⟨fun hx => ?_, fun ⟨_, _, hx⟩ => pc_eval_in_l_l hM hx⟩
  obtain ⟨c, hc⟩ := (pc_coded_iff_l hM x).mpr hx
  exact ⟨c, pc_eval_valid_l (KPi.models_iff_l.mp hM).1 hc, hc⟩

end YesMetaZFC.SetTheory.InnerModel
