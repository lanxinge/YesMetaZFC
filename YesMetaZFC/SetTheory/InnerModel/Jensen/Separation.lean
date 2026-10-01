import YesMetaZFC.SetTheory.InnerModel.Jensen.Class
import YesMetaZFC.SetTheory.InnerModel.Separation.Bounded

/-! # J 类中的分离与全部内部序数 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem l_finite_bound_l (hM : M.Models KPi) {n} (e : Fin n → M.Domain) (he : ∀ i, L_d (e i)) :
    ∃ a U, J_d a U ∧ ∀ i, M.mem (e i) U := by
  let hKP := (KPi.models_iff_l.mp hM).1
  induction n with
  | zero =>
    obtain ⟨a, ha⟩ := KP.exists_empty hKP
    obtain ⟨U, hu⟩ := jh_value_exists_l hM a
    exact ⟨a, U, ⟨Structure.IsOrdinal.of_no_members ha, hu⟩, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨a, U, ha, hU⟩ := ih (fun i => e i.succ) (fun i => he i.succ)
    obtain ⟨S, hs⟩ := KP.exists_insert hKP U (e 0)
    obtain ⟨b, V, hb, hv⟩ := l_bound_l hM (X := S) (fun x hx => ((hs x).mp hx).elim
      (fun hx => ⟨a, U, ha, hx⟩) (fun hx => hx.symm ▸ he 0))
    exact ⟨b, V, hb, Fin.cases (hv _ ((hs _).mpr (Or.inr rfl)))
      (fun i => hv _ ((hs _).mpr (Or.inl (hU i))))⟩

theorem l_separation_l (hM : M.Models KPi) {n} (φ : Delta0UnarySchema n) (ρ : Env M n)
    (hρ : ∀ i, L_d (ρ.bound i)) {X : M.Domain} (hX : L_d X) :
    ∃ Y, L_d Y ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.toUnarySchema.denote ρ x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, U, ha, hU⟩ := l_finite_bound_l hM (ρ.push X).bound (Fin.cases hX hρ)
  obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l hKP ha.1
  obtain ⟨C, hc⟩ := jh_value_exists_l hM s
  have hstep := jh_step_spec_l hM (jh_successor_l hM ha.1 hs ha.2 hc)
  obtain ⟨Y, hy, hY⟩ := rd_separation_l hKP hstep.1 (jh_value_transitive_l hM hc)
    hstep.2.2 (jh_value_transitive_l hM ha.2) φ ρ (fun i => hU i.succ) (hU 0)
  exact ⟨Y, ⟨s, C, ⟨ho, hc⟩, hy⟩, hY⟩

/-- 先收集前序数的层界，再在该层中分离序数；不预设 J 含全部序数。 -/
theorem l_ordinal_l (hM : M.Models KPi) {a : M.Domain} (ha : M.IsOrdinal a) : L_d a := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let φ : UnarySchema 0 := { body := .imp (KP.ord0_m .newest) (l_m .newest) }
  have hφ b : φ.denote (jh_env_l a) b ↔ (M.IsOrdinal b → L_d b) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.ord0_sat_l hKP, l_sat_l hKP,
      Definitional.Term.eval_newest]
  apply (hφ a).mp (hi φ (jh_env_l a) ?_ a) ha
  intro b ih
  apply (hφ b).mpr
  intro hb
  obtain ⟨c, U, hc, hU⟩ := l_bound_l hM (fun x hx => (hφ x).mp (ih x hx) (hb.mem hx))
  let ψ : Delta0UnarySchema 0 := { body := KP.ord0_m .newest, delta0 := KP.ord0_delta_l _ }
  obtain ⟨D, hd, hD'⟩ := l_separation_l hM ψ (jh_env_l a) (fun i => Fin.elim0 i) (l_layer_l hM hc)
  have hD x : M.mem x D ↔ M.mem x U ∧ M.IsOrdinal x :=
    (hD' x).trans (and_congr_right fun _ => KP.ord0_sat_l hKP _ _)
  have ht : M.TransitiveSet D := fun x hx y hy => (hD y).mpr
    ⟨jh_value_transitive_l hM hc.2 x ((hD x).mp hx).1 y hy, ((hD x).mp hx).2.mem hy⟩
  have ho := KP.ordinal_of_transitive_l hKP ht (fun x hx => ((hD x).mp hx).2)
  have hsub : M.MemberSubset b D := fun x hx => (hD x).mpr ⟨hU x hx, hb.mem hx⟩
  rcases Structure.IsOrdinal.trichotomy hKP.1 hb ho (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP b D) with he | he | he
  · exact (hKP.1.eq_of_same_members b D he).symm ▸ hd
  · exact l_transitive_l hM hd he
  · exact (KP.mem_irrefl_d hKP D (hsub D he)).elim

end YesMetaZFC.SetTheory.InnerModel
