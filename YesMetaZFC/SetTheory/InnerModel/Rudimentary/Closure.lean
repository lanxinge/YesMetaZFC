import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Iteration

/-! # 模型内部的最小 rudimentary 闭包 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rd_closed_d (D : M.Domain) : Prop := ∀ k a b c, M.mem a D → M.mem b D → M.mem c D →
  ∀ t, Rd_fun_d k a b c t → M.mem t D

def rd_closed_m {n} (C : Term n) : Formula 1 n := rd_step_m C C
derive_free_closed rd_closed_m
theorem rd_closed_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (C : Term n) :
    Formula.satisfies ρ (rd_closed_m C) ↔ Rd_closed_d (C.eval ρ) := by
  rw [rd_closed_m, rd_step_sat_l hKP]
  exact ⟨fun h k a b c ha hb hc t ht => (h t).mpr (Or.inr ⟨k, a, b, c, ha, hb, hc, ht⟩),
    fun h t => ⟨Or.inl, fun ht => ht.elim id (fun ⟨k, a, b, c, ha, hb, hc, ht⟩ => h k a b c ha hb hc t ht)⟩⟩

theorem rd_iter_le_l (hM : M.Models KPi) {U D a Y : M.Domain}
    (hd : Rd_closed_d D) (hu : M.MemberSubset U D) (hy : Rd_iter_d U a Y) : M.MemberSubset Y D := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let ρ := (rd_seed_env_l U).push D
  let φ : UnarySchema 2 := { body := .forallE (.imp (rd_iter_m (.bound 3) (.bound 1) .newest)
    (Formula.subset .newest (.bound 2))) }
  have hφ b : φ.denote ρ b ↔ ∀ V, Rd_iter_d U b V → M.MemberSubset V D := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_iter_sat_l hKP.1, Formula.satisfies_subset_iff]
    rfl
  apply (hφ a).mp (hi φ ρ ?_ a) Y hy
  intro b ih
  apply (hφ b).mpr
  intro V hv
  obtain ⟨H, hs, hh⟩ := rd_iter_equation_l hM hv
  have hHD : M.MemberSubset H D := fun t ht => ((hh t).mp ht).elim (hu t)
    (fun ⟨c, hc, W, hw, ht⟩ => (hφ c).mp (ih c hc) W hw t ht)
  intro t ht
  exact ((hs t).mp ht).elim (hHD t) (fun ⟨k, a, b, c, ha, hb, hc, ht⟩ =>
    hd k a b c (hHD a ha) (hHD b hb) (hHD c hc) t ht)

theorem rd_iter_transitive_l (hM : M.Models KPi) {U a Y : M.Domain}
    (hu : M.TransitiveSet U) (hy : Rd_iter_d U a Y) : M.TransitiveSet Y := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let φ : UnarySchema 1 := { body := .forallE (.imp (rd_iter_m (.bound 2) (.bound 1) .newest)
    (Formula.isTransitive .newest)) }
  have hφ b : φ.denote (rd_seed_env_l U) b ↔ ∀ V, Rd_iter_d U b V → M.TransitiveSet V := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_iter_sat_l hKP.1, Formula.satisfies_isTransitive_iff]
    rfl
  apply (hφ a).mp (hi φ (rd_seed_env_l U) ?_ a) Y hy
  intro b ih
  apply (hφ b).mpr
  intro V hv
  obtain ⟨H, hs, hh⟩ := rd_iter_equation_l hM hv
  apply rd_step_transitive_l hKP.1 ?_ hs
  intro t ht z hz
  apply (hh z).mpr
  exact ((hh t).mp ht).elim (fun ht => Or.inl (hu t ht z hz))
    (fun ⟨c, hc, W, hw, ht⟩ => Or.inr ⟨c, hc, W, hw, (hφ c).mp (ih c hc) W hw t ht z hz⟩)

def Omega0_d (ω : M.Domain) : Prop := M.IsInductive ω ∧ ∀ a, M.mem a ω → KP.N0_d a

def omega0_m {n} (ω : Term n) : Formula 1 n :=
  .conj (Formula.existsMem ω (Formula.forallMem .newest .falsum))
    (.conj (Formula.forallMem ω (Formula.existsMem ω.weaken (KP.succ0_m .newest (.bound 1))))
      (Formula.forallMem ω (KP.n0_m .newest)))
derive_free_closed omega0_m

theorem omega0_delta_l {n} (ω : Term n) : (omega0_m ω).IsDelta0 :=
  .conj (.existsMem _ (.forallMem _ .falsum))
    (.conj (.forallMem _ (.existsMem _ (KP.succ0_delta_l ..))) (.forallMem _ (KP.n0_delta_l _)))

theorem omega0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω : Term n) :
    Formula.satisfies ρ (omega0_m ω) ↔ Omega0_d (ω.eval ρ) := by
  simp only [omega0_m, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff, KP.succ0_sat_l hE,
    KP.n0_sat_l hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨⟨e, he, he'⟩, hs, hn⟩ => ⟨⟨⟨e, he', he⟩, fun a ha =>
    (hs a ha).imp (fun _ h => h.symm)⟩, hn⟩,
    fun ⟨⟨⟨e, he, he'⟩, hs⟩, hn⟩ => ⟨⟨e, he', he⟩, fun a ha =>
      (hs a ha).imp (fun _ h => h.symm), hn⟩⟩

theorem omega0_exists_l (hM : M.Models KPi) : ∃ ω : M.Domain, Omega0_d ω := by
  obtain ⟨ω, hω, hn⟩ := KPi.exists_omega_l hM
  exact ⟨ω, hω.1, fun a ha => (hn a).mp ha⟩

theorem rd_iter_omega_closed_l (hM : M.Models KPi) {U ω C : M.Domain}
    (hω : Omega0_d ω) (hc : Rd_iter_d U ω C) : Rd_closed_d C ∧ M.MemberSubset U C := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨H, hs, hh⟩ := rd_iter_equation_l hM hc
  have contains {a X : M.Domain} (hx : Rd_iter_d U a X) : M.MemberSubset U X := by
    obtain ⟨K, hk, hK⟩ := rd_iter_equation_l hM hx
    exact fun t ht => (hk t).mpr (Or.inl ((hK t).mpr (Or.inl ht)))
  have part t (ht : M.mem t H) : ∃ n, M.mem n ω ∧ ∃ X, Rd_iter_d U n X ∧ M.mem t X := by
    rcases (hh t).mp ht with ht | ht
    · obtain ⟨e, _, he⟩ := hω.1.1
      obtain ⟨X, hx⟩ := rd_iter_exists_l hM U e
      exact ⟨e, he, X, hx, contains hx t ht⟩
    · exact ht
  have merge {n m X Y : M.Domain} (hn : M.mem n ω) (hm : M.mem m ω)
      (hx : Rd_iter_d U n X) (hy : Rd_iter_d U m Y) :
      ∃ k, M.mem k ω ∧ ∃ Z, Rd_iter_d U k Z ∧ M.MemberSubset X Z ∧ M.MemberSubset Y Z := by
    have on := KPi.n0_ordinal_l hM (hω.2 n hn)
    have om := KPi.n0_ordinal_l hM (hω.2 m hm)
    rcases Structure.IsOrdinal.trichotomy hKP.1 on om (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP n m) with he | hnm | hmn
    · have he := hKP.1.eq_of_same_members n m he; subst m
      have he := rd_iter_unique_l hM hx hy; subst Y
      exact ⟨n, hn, X, hx, fun _ h => h, fun _ h => h⟩
    · exact ⟨m, hm, Y, hy, rd_iter_mono_l hM (om.transitive n hnm) hx hy, fun _ h => h⟩
    · exact ⟨n, hn, X, hx, fun _ h => h, rd_iter_mono_l hM (on.transitive m hmn) hy hx⟩
  have closed : Rd_closed_d H := by
    intro k a b c ha hb hc t ht
    obtain ⟨i, hi, X, hx, ha⟩ := part a ha
    obtain ⟨j, hj, Y, hy, hb⟩ := part b hb
    obtain ⟨l, hl, Z, hz, hc⟩ := part c hc
    obtain ⟨n, hn, V, hv, hXV, hYV⟩ := merge hi hj hx hy
    obtain ⟨m, hm, W, hw, hVW, hZW⟩ := merge hn hl hv hz
    obtain ⟨s, hsm, hsω⟩ := hω.1.2 m hm
    obtain ⟨S, hS⟩ := rd_iter_exists_l hM U s
    obtain ⟨K, hK, hk⟩ := rd_iter_equation_l hM hS
    have hWK : M.MemberSubset W K := fun t ht => (hk t).mpr (Or.inr ⟨m, hsm.predecessor_mem, W, hw, ht⟩)
    exact (hh t).mpr (Or.inr ⟨s, hsω, S, hS, (hK t).mpr
      (Or.inr ⟨k, a, b, c, hWK a (hVW a (hXV a ha)), hWK b (hVW b (hYV b hb)), hWK c (hZW c hc), ht⟩)⟩)
  have he : C = H := hKP.1.eq_of_same_members C H (fun t => (hs t).trans
    ⟨fun h => h.elim id (fun ⟨k, a, b, c, ha, hb, hc, ht⟩ => closed k a b c ha hb hc t ht), Or.inl⟩)
  subst C
  exact ⟨closed, fun t ht => (hh t).mpr (Or.inl ht)⟩

end YesMetaZFC.SetTheory.InnerModel
