import YesMetaZFC.SetTheory.SetConstruction

/-! # KP 中有限族的共同集合界 -/

namespace YesMetaZFC.SetTheory
universe u
variable {M : Structure.{u}}

theorem kp_finite_cover_l (hKP : M.Models KP) (L : List M.Domain) :
    ∃ T, ∀ A ∈ L, M.MemberSubset A T ∧ M.mem A T := by
  induction L with
  | nil => obtain ⟨a⟩ := M.nonempty; exact ⟨a, fun _ h => (List.not_mem_nil h).elim⟩
  | cons A L ih =>
    obtain ⟨R, hr⟩ := ih
    obtain ⟨U, hu⟩ := KP.exists_unionOfTwo hKP A R
    obtain ⟨T, ht⟩ := KP.exists_insert hKP U A
    have ar x hx := (ht x).mpr (Or.inl ((hu x).mpr (Or.inl hx)))
    have rr x hx := (ht x).mpr (Or.inl ((hu x).mpr (Or.inr hx)))
    refine ⟨T, fun B hb => ?_⟩
    rcases List.mem_cons.mp hb with he | hb
    · subst B; exact ⟨ar, (ht A).mpr (Or.inr rfl)⟩
    · exact ⟨fun x hx => rr x ((hr B hb).1 x hx), rr B (hr B hb).2⟩

end YesMetaZFC.SetTheory
