import YesMetaZFC.SetTheory.InnerModel.ProofCode.Global.Initial

/-! # L 良序的 Δ₁ 判定与集合编码良序实例 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def lo_not_lt_s : S1_binary 0 where
  matrix := {
    body := .disj (Formula.extensionalEq (.bound 2) (.bound 1)) (lo_lt_s.matrix_m Fin.elim0 (.bound 1) (.bound 2) .newest)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .disj (.atom _ _ _) (lo_lt_s.matrix.delta0.bind_l _) }
theorem lo_not_lt_sat_l (hM : M.Models KPi) (ρ : Env M 0) (x y : M.Domain) :
    lo_not_lt_s.schema.denote ρ x y ↔ x = y ∨ Lo_lt_d y x := by
  rw [S1_binary.sat_l]
  simp only [lo_not_lt_s, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq (KPi.models_iff_l.mp hM).1.1, po_matrix_env_l lo_lt_s ρ]
  change (∃ T, x = y ∨ lo_lt_s.matrix_binary.toBinarySchema.denote (ρ.push y) x T) ↔ _
  exact ⟨fun ⟨T, h⟩ => h.elim Or.inl (fun h => Or.inr ((lo_lt_sat_l hM ρ y x).mp ((lo_lt_s.sat_l ρ y x).mpr ⟨T, h⟩))),
    fun h => h.elim (fun he => ⟨x, Or.inl he⟩) (fun h =>
      ((lo_lt_s.sat_l ρ y x).mp ((lo_lt_sat_l hM ρ y x).mpr h)).imp (fun _ h => Or.inr h))⟩

theorem lo_delta1_l (hM : M.Models KPi) {x y : M.Domain} (hx : L_d x) (hy : L_d y) (ρ : Env M 0) :
    lo_lt_s.schema.denote ρ x y ↔ ¬ lo_not_lt_s.schema.denote ρ x y := by
  rw [lo_lt_sat_l hM, lo_not_lt_sat_l hM]
  constructor
  · intro h g
    rcases g with rfl | g
    · exact lo_irrefl_l hM x h
    · exact lo_irrefl_l hM x (lo_trans_l hM h g)
  · intro hn
    exact (lo_compare_l hM hx hy).elim (fun h => (hn (Or.inl h)).elim) (fun h => h.elim id (fun h => (hn (Or.inr h)).elim))

def Lo_table_d (X R : M.Domain) : Prop :=
  ∀ p, M.mem p R ↔ ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧ KPair_d M p x y ∧ Lo_lt_d x y

theorem lo_table_exists_l (hM : M.Models KPi) {X : M.Domain} (hx : ∀ x, M.mem x X → L_d x) : ∃ R, Lo_table_d X R := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := (jh_env_l X).push X
  obtain ⟨P, hp⟩ := KP.kprod_exists_l hKP X X
  obtain ⟨R, hr⟩ := KP.d1_separation_l hKP (pn_pair_s lo_lt_s) (pn_pair_s lo_not_lt_s) ρ P (by
    intro p hpP
    obtain ⟨x, hxX, y, hyX, hpair⟩ := (hp p).mp hpP
    rw [pn_pair_at_l hKP lo_lt_s ρ hxX hyX hpair, pn_pair_at_l hKP lo_not_lt_s ρ hxX hyX hpair]
    exact lo_delta1_l hM (hx x hxX) (hx y hyX) (jh_env_l p))
  refine ⟨R, fun p => ?_⟩
  rw [hr p, pn_pair_sat_l hKP lo_lt_s]
  simp only [lo_lt_sat_l hM]
  exact ⟨And.right, fun h => ⟨h.elim (fun x hx => hx.2.elim (fun y hy => (hp p).mpr ⟨x, hx.1, y, hy.1, hy.2.1⟩)), h⟩⟩

theorem Lo_table_d.entry_l (hKP : M.Models KP) {X R x y : M.Domain} (hr : Lo_table_d X R) :
    Rd_entry_d x y R ↔ M.mem x X ∧ M.mem y X ∧ Lo_lt_d x y := by
  constructor
  · rintro ⟨p, hp, hpR⟩
    obtain ⟨a, ha, b, hb, he, h⟩ := (hr p).mp hpR
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M he hp
    exact ⟨ha, hb, h⟩
  · rintro ⟨hx, hy, h⟩
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total x y
    exact ⟨p, hp, (hr p).mpr ⟨x, hx, y, hy, hp, h⟩⟩

theorem lo_table_unique_l (hE : Extensional M) {X R S : M.Domain} (hr : Lo_table_d X R) (hs : Lo_table_d X S) : R = S :=
  hE.eq_of_same_members R S (fun p => (hr p).trans (hs p).symm)

theorem Lo_table_d.wellorder_l (hM : M.Models KPi) {X R : M.Domain} (hx : ∀ x, M.mem x X → L_d x)
    (hr : Lo_table_d X R) : M.IsSetCodedWellOrder (kp_pair_l (KPi.models_iff_l.mp hM).1) R X := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have entry x y : M.PairMember (kp_pair_l hKP) x y R ↔ M.mem x X ∧ M.mem y X ∧ Lo_lt_d x y := hr.entry_l hKP
  refine ⟨⟨?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, _, y, _, hp, _⟩ := (hr p).mp hp
    exact ⟨x, y, hp⟩
  · intro x _ h; exact lo_irrefl_l hM x ((entry x x).mp h).2.2
  · intro x hxX y _ z hzX h g
    exact (entry x z).mpr ⟨hxX, hzX, lo_trans_l hM ((entry x y).mp h).2.2 ((entry y z).mp g).2.2⟩
  · intro x hxX y hyX
    rcases lo_compare_l hM (hx x hxX) (hx y hyX) with he | he | he
    · exact Or.inl (he ▸ (fun _ => Iff.rfl))
    · exact Or.inr (Or.inl ((entry x y).mpr ⟨hxX, hyX, he⟩))
    · exact Or.inr (Or.inr ((entry y x).mpr ⟨hyX, hxX, he⟩))
  · intro Y hy hn
    obtain ⟨x, hxY, hm⟩ := lo_min_l hM (fun x hxY => hx x (hy x hxY)) hn
    exact ⟨x, hxY, fun y hyY => (hm y hyY).elim (fun he => Or.inl (he ▸ (fun _ => Iff.rfl)))
      (fun he => Or.inr ((entry x y).mpr ⟨hy x hxY, hy y hyY, he⟩))⟩

theorem lo_order_table_l (hM : M.Models KPi) {X : M.Domain} (hx : ∀ x, M.mem x X → L_d x) :
    ∃ R, Lo_table_d X R ∧ M.IsSetCodedWellOrder (kp_pair_l (KPi.models_iff_l.mp hM).1) R X := by
  obtain ⟨R, hr⟩ := lo_table_exists_l hM hx
  exact ⟨R, hr, hr.wellorder_l hM hx⟩

end YesMetaZFC.SetTheory.InnerModel
