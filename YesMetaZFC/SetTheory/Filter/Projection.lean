import YesMetaZFC.SetTheory.Filter.Relative
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 容许集合代数之间的测度投影

投影同时携带实际容许逆像及其测度方程。恒等与复合直接沿函数图证明，
不要求容许代数是完整幂集。
-/
namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Pull_d (E t A B : M.Domain) : Prop := ∀ v, M.mem v B ↔
  M.mem v E ∧ ∃ w, M.mem w A ∧ Rd_entry_d v w t

def pull_m {d} (E t A B : Term d) : Formula 1 d := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest E.weaken) (Formula.existsMem A.weaken (rd_entry0_m (.bound 1) .newest t.weaken.weaken))))
derive_free_closed pull_m

theorem pull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (E t A B : Term d) :
    Formula.satisfies ρ (pull_m E t A B) ↔ Pull_d (E.eval ρ) (t.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [pull_m, Pull_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Push_d (D E P Q U V t : M.Domain) : Prop := Fn0_d E D t ∧ ∀ A, M.mem A P →
  ∃ B, M.mem B Q ∧ Pull_d E t A B ∧ (M.mem B V ↔ M.mem A U)

def push_m {d} (D E P Q U V t : Term d) : Formula 1 d := .conj (fn0_m E D t)
  (Formula.forallMem P (Formula.existsMem Q.weaken (.conj
    (pull_m E.weaken.weaken t.weaken.weaken (.bound 1) .newest)
    (.iff (.mem .newest V.weaken.weaken) (.mem (.bound 1) U.weaken.weaken)))))
derive_free_closed push_m

theorem push_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D E P Q U V t : Term d) :
    Formula.satisfies ρ (push_m D E P Q U V t) ↔
      Push_d (D.eval ρ) (E.eval ρ) (P.eval ρ) (Q.eval ρ) (U.eval ρ) (V.eval ρ) (t.eval ρ) := by
  simp only [push_m, Push_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, pull_sat_l hE, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  rfl

theorem Push_d.member_l (hE : Extensional M) {D E P Q U V t A B : M.Domain}
    (h : Push_d D E P Q U V t) (hA : M.mem A P) (hB : Pull_d E t A B) : M.mem B V ↔ M.mem A U := by
  obtain ⟨C, _, hC, hc⟩ := h.2 A hA
  exact hE.eq_of_same_members C B (fun v => (hC v).trans (hB v).symm) ▸ hc

theorem Pull_d.comp_l {D E F t s u A B C : M.Domain} (h : Pull_d E t A B) (k : Pull_d F s B C)
    (ht : Fn0_d E D t) (hs : Fn0_d F E s) (hu : Cp0_d F E D s t u) : Pull_d F u A C := by
  intro v
  refine (k v).trans ⟨?_, ?_⟩
  · rintro ⟨hv, w, hw, hvw⟩
    obtain ⟨_, x, hx, hwx⟩ := (h w).mp hw
    exact ⟨hv, x, hx, (hu.value_l hs ht hvw).mpr hwx⟩
  · rintro ⟨hv, x, hx, hvx⟩
    obtain ⟨w, hw, hvw⟩ := hs.2.1 v hv
    exact ⟨hv, w, (h w).mpr ⟨hw, x, hx, (hu.value_l hs ht hvw).mp hvx⟩, hvw⟩

theorem Push_d.comp_l {D E F P Q R U V W t s u : M.Domain}
    (h : Push_d D E P Q U V t) (k : Push_d E F Q R V W s) (hu : Cp0_d F E D s t u) : Push_d D F P R U W u := by
  refine ⟨hu.1, fun A hA => ?_⟩
  obtain ⟨B, hB, hab, he⟩ := h.2 A hA
  obtain ⟨C, hC, hbc, hf⟩ := k.2 B hB
  exact ⟨C, hC, hab.comp_l hbc h.1 k.1 hu, hf.trans he⟩

theorem push_id_l {D P U t : M.Domain} (hP : Field_d D P) (ht : Fn0_d D D t)
    (hi : ∀ v w, Rd_entry_d v w t ↔ M.mem v D ∧ v = w) : Push_d D D P P U U t := by
  refine ⟨ht, fun A hA => ⟨A, hA, fun v => ?_, Iff.rfl⟩⟩
  exact ⟨fun hv => ⟨hP.bounds A hA v hv, v, hv, (hi v v).mpr ⟨hP.bounds A hA v hv, rfl⟩⟩,
    fun ⟨_, w, hw, hvw⟩ => ((hi v w).mp hvw).2.symm ▸ hw⟩

/-- 把实际相对超滤限制到较小的容许代数，所有成员仍是原来的集合。 -/
theorem restrict_l (hKP : M.Models KP) {D P Q U : M.Domain} (h : Rel_ultra_d D Q U)
    (hP : Field_d D P) (hPQ : M.MemberSubset P Q) :
    ∃ V, Rel_ultra_d D P V ∧ ∀ A, M.mem A V ↔ M.mem A P ∧ M.mem A U := by
  let φ : Delta0UnarySchema 1 := { body := .mem .newest (.bound 1), delta0 := .mem _ _ }
  obtain ⟨V, hV⟩ := KP.separation_exists_d hKP φ ⟨fun _ => U, fun _ => U⟩ P
  have spec A : M.mem A V ↔ M.mem A P ∧ M.mem A U :=
    (hV A).trans (and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  refine ⟨V, ⟨hP, ⟨fun A hA => hP.bounds A ((spec A).mp hA).1,
    (spec D).mpr ⟨hP.top, h.base.top⟩, ?_⟩, fun A hA => ((spec A).mp hA).1, ?_, ?_, ?_⟩, spec⟩
  · intro A B hA hB
    obtain ⟨C, hC, hc⟩ := hP.inter A B ((spec A).mp hA).1 ((spec B).mp hB).1
    obtain ⟨W, hW, hwA, hwB⟩ := h.base.meet A B ((spec A).mp hA).2 ((spec B).mp hB).2
    exact ⟨C, (spec C).mpr ⟨hC, h.upward W C hW (hPQ C hC) (fun v hv => (hc v).mpr ⟨hwA v hv, hwB v hv⟩)⟩,
      fun v hv => ((hc v).mp hv).1, fun v hv => ((hc v).mp hv).2⟩
  · exact fun A B hA hB hab => (spec B).mpr ⟨hB, h.upward A B ((spec A).mp hA).2 (hPQ B hB) hab⟩
  · exact fun A hA => h.proper A ((spec A).mp hA).2
  · intro A B hA hB hc
    exact (h.decides A B (hPQ A hA) (hPQ B hB) hc).elim
      (fun ha => Or.inl ((spec A).mpr ⟨hA, ha⟩)) (fun hb => Or.inr ((spec B).mpr ⟨hB, hb⟩))

end YesMetaZFC.SetTheory.FilterZF
