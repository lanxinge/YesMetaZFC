import YesMetaZFC.SetTheory.InnerModel.ProofCode.Parser.Certificate

/-! # 检查器恰好判定既有的内部语法高度关系 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem Po_arg_d.bound_l {T c x : M.Domain} {i} (hx : Po_arg_d i T c x) : M.mem x T := by
  obtain ⟨t, _, p, _, a, ha, b, hb, d, hd, _, _, rfl⟩ := hx
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hd

theorem pg_level_rank_l (hM : M.Models KPi) {T n Y : M.Domain} (ht : M.TransitiveSet T)
    (hn : KP.N0_d n) (hy : Pg_level_d T n Y) (c : M.Domain) : M.mem c Y ↔ M.mem c T ∧ Ps_rank_d n c := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let φ : UnarySchema 1 := { body := .imp (KP.n0_m .newest) (.forallE
    (.imp (pg_level_m (.bound 2) (.bound 1) .newest) (.forallE
      (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 3)) (ps_rank_m (.bound 2) .newest)))))) }
  have hφ h : φ.denote (rd_seed_env_l T) h ↔ KP.N0_d h → ∀ Y, Pg_level_d T h Y →
      ∀ c, M.mem c Y ↔ M.mem c T ∧ Ps_rank_d h c := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.n0_sat_l hKP.1,
      Formula.satisfies_forall_iff, pg_level_sat_l hKP.1, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, ps_rank_formula_l hKP]; rfl
  apply (hφ n).mp (hi φ (rd_seed_env_l T) ?_ n) hn Y hy c
  intro h ih
  apply (hφ h).mpr
  intro hh Y hy c
  obtain ⟨V, hY, hV⟩ := pg_level_equation_l hM hy
  have child {d} (hd : M.mem d V) : ∃ m, M.mem m h ∧ Ps_rank_d m d := by
    obtain ⟨m, hm, Z, hz, hd⟩ := (hV d).mp hd
    exact ⟨m, hm, (((hφ m).mp (ih m hm) (hh.mem_l hm) Z hz d).mp hd).2⟩
  have child' {d} (hd : M.mem d T) (hr : ∃ m, M.mem m h ∧ Ps_rank_d m d) : M.mem d V := by
    obtain ⟨m, hm, hr⟩ := hr
    obtain ⟨Z, hz⟩ := pg_level_exists_l hM T m
    exact (hV d).mpr ⟨m, hm, Z, hz, ((hφ m).mp (ih m hm) (hh.mem_l hm) Z hz d).mpr ⟨hd, hr⟩⟩
  constructor
  · intro hc
    obtain ⟨hcT, hg⟩ := (hY c).mp hc
    refine ⟨hcT, ?_⟩
    rcases hg with ⟨a, _, hc, ha⟩ | ⟨k, a, _, b, _, d, _, hc, ha, hb, hd⟩
    · exact ps_leaf_rank_l hM hh hc ha
    · exact ps_node_rank_l hM hh hc (child ha) (child hb) (child hd)
  · rintro ⟨hcT, hc⟩
    apply (hY c).mpr
    refine ⟨hcT, ?_⟩
    rcases ps_rank_unfold_l hc with ⟨U, a, ⟨e, _, he, hp⟩, ha⟩ | ⟨U, k, a, b, d, hc, ha, hb, hd⟩
    · have bound := po_pair_bound_l ht hcT hp
      exact Or.inl ⟨a, bound.2, ⟨e, bound.1, he, hp⟩, ha⟩
    · obtain ⟨hc, hf⟩ := po_node_fields_l ht hcT hc
      exact Or.inr ⟨k, a, (hf 0).bound_l, b, (hf 1).bound_l, d, (hf 2).bound_l,
        hc, child' (hf 0).bound_l ha, child' (hf 1).bound_l hb, child' (hf 2).bound_l hd⟩

theorem pg_level_mono_l (hM : M.Models KPi) {T n m Y Z : M.Domain} (hnm : M.MemberSubset n m)
    (hy : Pg_level_d T n Y) (hz : Pg_level_d T m Z) : M.MemberSubset Y Z := by
  obtain ⟨V, hY, hV⟩ := pg_level_equation_l hM hy
  obtain ⟨W, hZ, hW⟩ := pg_level_equation_l hM hz
  have sub c hc := (hW c).mpr (((hV c).mp hc).imp (fun n hn => ⟨hnm n hn.1, hn.2⟩))
  intro c hc
  obtain ⟨hcT, hg⟩ := (hY c).mp hc
  apply (hZ c).mpr
  refine ⟨hcT, ?_⟩
  rcases hg with hl | ⟨k, a, ha, b, hb, d, hd, hc, haV, hbV, hdV⟩
  · exact Or.inl hl
  · exact Or.inr ⟨k, a, ha, b, hb, d, hd, hc, sub a haV, sub b hbV, sub d hdV⟩

theorem pg_level_height_l (hM : M.Models KPi) {T n Y : M.Domain} (ht : M.TransitiveSet T)
    (hn : KP.N0_d n) (hy : Pg_level_d T n Y) (c : M.Domain) : M.mem c Y ↔ M.mem c T ∧ Ps_height_d n c := by
  constructor
  · intro hc
    obtain ⟨hcT, hc⟩ := (pg_level_rank_l hM ht hn hy c).mp hc
    exact ⟨hcT, n, Or.inr rfl, hc⟩
  · rintro ⟨hcT, m, hm, hc⟩
    obtain ⟨Z, hz⟩ := pg_level_exists_l hM T m
    have hmn : KP.N0_d m := hm.elim hn.mem_l (fun he => he.symm ▸ hn)
    have sub : M.MemberSubset m n := fun x hx => hm.elim (fun hm => hn.1 m hm x hx) (fun he => he ▸ hx)
    exact pg_level_mono_l hM sub hz hy c ((pg_level_rank_l hM ht hmn hz c).mpr ⟨hcT, hc⟩)

end YesMetaZFC.SetTheory.InnerModel
