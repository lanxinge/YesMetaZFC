import YesMetaZFC.SetTheory.Collapse.Mostowski

/-! # 传递坍塌的规范性与唯一性

任意传递值域上的隶属同构都满足已构造的同一递归，因此其值域和集合图
均唯一。这里不要求调用者另给“与规范坍塌一致”的证明。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Mc_iso_d.canonical_l (hM : M.Models KPi) {X B F a y : M.Domain}
    (h : Mc_iso_d X B F) (hb : M.TransitiveSet B) (hp : Rd_entry_d a y F) : Mc_value_d X a y := by
  let hE := (KPi.models_iff_l.mp hM).1.1
  let ρ := (mc_env_l X).push F
  let φ : UnarySchema 2 := { body := (.forallE <| .imp (rd_entry0_m (.bound 1) .newest (.bound 2))
    (mc_value_m (.bound 3) (.bound 1) .newest)) }
  have sat a : φ.denote ρ a ↔ (∀ y, Rd_entry_d a y F → Mc_value_d X a y) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hE, mc_value_sat_l hE]; rfl
  apply (sat a).mp ((KPi.models_iff_l.mp hM).2 φ ρ ?_ a) y hp
  intro a ih
  apply (sat a).mpr
  intro y hy
  obtain ⟨v, hv⟩ := mc_value_exists_l hM X a
  have eq : y = v := by
    apply hE.eq_of_same_members; intro z
    rw [mc_value_equation_l hM hv z]
    constructor
    · intro hz
      obtain ⟨b, hbf⟩ := h.onto z (hb y (h.function.bound_l hy).2 z hz)
      have hba := (h.member b a z y hbf hy).mpr hz
      exact ⟨b, hba, (h.function.bound_l hbf).1, (sat b).mp (ih b hba) z hbf⟩
    · rintro ⟨b, hba, hbx, hval⟩
      obtain ⟨w, _, hbf⟩ := h.function.2.1 b hbx
      have eq := mc_value_unique_l hM hval ((sat b).mp (ih b hba) w hbf)
      exact eq.symm ▸ (h.member b a w y hbf hy).mp hba
  subst v
  exact hv

theorem mc_iso_unique_l (hM : M.Models KPi) {X B D F G : M.Domain}
    (h : Mc_iso_d X B F) (g : Mc_iso_d X D G) (hb : M.TransitiveSet B) (hd : M.TransitiveSet D) : B = D ∧ F = G := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have entry a y : Rd_entry_d a y F ↔ Rd_entry_d a y G := by
    constructor
    · intro hy
      obtain ⟨z, _, hz⟩ := g.function.2.1 a (h.function.bound_l hy).1
      have eq := mc_value_unique_l hM (h.canonical_l hM hb hy) (g.canonical_l hM hd hz)
      subst z; exact hz
    · intro hy
      obtain ⟨z, _, hz⟩ := h.function.2.1 a (g.function.bound_l hy).1
      have eq := mc_value_unique_l hM (g.canonical_l hM hd hy) (h.canonical_l hM hb hz)
      subst z; exact hz
  refine ⟨hKP.1.eq_of_same_members B D (fun y => ?_),
    (fn0_function_l hKP h.function).1.1.eq_of_pairMember_iff hKP.1 (fn0_function_l hKP g.function).1.1 entry⟩
  exact ⟨fun hy => (h.onto y hy).elim fun a ha => (g.function.bound_l ((entry a y).mp ha)).2,
    fun hy => (g.onto y hy).elim fun a ha => (h.function.bound_l ((entry a y).mpr ha)).2⟩

end YesMetaZFC.SetTheory
