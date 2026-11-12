import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.KP.OrdinalCore

/-! # 序数的 Δ₀ 刻画与内部序数界 -/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

namespace KP
/-- 非零极限性的有界刻画，可随任意传递成员模型的初等映射运输。 -/
def limit0_m {n} (a : Term n) : Formula 1 n := .conj (ord0_m a)
  (.conj (Formula.existsMem a (.neg .falsum))
    (Formula.forallMem a (Formula.existsMem a.weaken (.mem (.bound 1) .newest))))
derive_free_closed limit0_m

theorem limit0_delta_l {n} (a : Term n) : (limit0_m a).IsDelta0 :=
  .conj (ord0_delta_l ..) (.conj (.existsMem _ (.neg .falsum)) (.forallMem _ (.existsMem _ (.mem ..))))

theorem limit0_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (a : Term n) :
    Formula.satisfies ρ (limit0_m a) ↔ M.IsLimitOrdinal (a.eval ρ) := by
  simp only [limit0_m, Formula.satisfies_conj_iff, ord0_sat_l hKP,
    Formula.satisfies_existsMem_iff, Formula.satisfies_neg_iff, Formula.satisfies_falsum_iff,
    not_false_eq_true, and_true, Formula.satisfies_forallMem_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem ordinal_successor_l (hKP : M.Models KP) {a : M.Domain} (ha : M.IsOrdinal a) :
    ∃ s, M.IsOrdinal s ∧ M.SuccessorOf s a := by
  obtain ⟨s, hs⟩ := exists_insert hKP a a
  have ht : M.TransitiveSet s := fun b hb c hc => (hs c).mpr (Or.inl
    (((hs b).mp hb).elim (fun hb => ha.transitive b hb c hc) (fun he => he ▸ hc)))
  exact ⟨s, ordinal_of_transitive_l hKP ht (fun b hb =>
    ((hs b).mp hb).elim ha.mem (fun he => he.symm ▸ ha)),
    fun b => (hs b).trans (or_congr_right
      ⟨fun he => he ▸ (fun _ => Iff.rfl), hKP.1.eq_of_same_members _ _⟩)⟩
end KP

theorem KPi.ordinal_bound_l (hM : M.Models KPi) (B : M.Domain) :
    ∃ a, M.IsOrdinal a ∧ ∀ T, M.mem T B → ∀ b, M.mem b T → M.IsOrdinal b → M.mem b a := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨U, hu, hBU⟩ := KPi.transitive_cover_l hM B
  let φ : Delta0UnarySchema 0 := { body := KP.ord0_m .newest, delta0 := KP.ord0_delta_l _ }
  obtain ⟨a, ha'⟩ := KP.separation_exists_d hKP φ ⟨Fin.elim0, fun _ => U⟩ U
  have ha b : M.mem b a ↔ M.mem b U ∧ M.IsOrdinal b :=
    (ha' b).trans (and_congr_right fun _ => KP.ord0_sat_l hKP _ _)
  have ht : M.TransitiveSet a := fun b hb c hc =>
    (ha c).mpr ⟨hu b ((ha b).mp hb).1 c hc, ((ha b).mp hb).2.mem hc⟩
  exact ⟨a, KP.ordinal_of_transitive_l hKP ht (fun b hb => ((ha b).mp hb).2),
    fun T hT b hb ho => (ha b).mpr ⟨hu T (hu B hBU T hT) b hb, ho⟩⟩

theorem ordinal_down_l (hKP : M.Models KP) {a b c : M.Domain} (ha : M.IsOrdinal a) (hc : M.IsOrdinal c)
    (hab : M.MemberSubset a b) (hbc : M.mem b c) : M.mem a c := by
  rcases ha.trichotomy hKP.1 (hc.mem hbc) (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP a b) with eq | lt | gt
  · exact (hKP.1.eq_of_same_members a b eq).symm ▸ hbc
  · exact hc.transitive b hbc a lt
  · exact (KP.mem_irrefl_d hKP b (hab b gt)).elim

end YesMetaZFC.SetTheory
