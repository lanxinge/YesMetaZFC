import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.Amalgamation
import YesMetaZFC.Model.Forcing.CCC.Predense
import YesMetaZFC.Model.Forcing.Iteration.Fusion.Countable

/-! # 前缀之外的内部支撑大小

尾支撑用实际分离集合表示。可数个有限支撑条件的坐标并也在模型内部可数；
两个结论供有限大小归纳中的可数覆盖直接调用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_tail_d (α p D : M.Domain) : Prop :=
  ∀ i, M.mem i D ↔ (∃ s, Entry_d M i s p) ∧ ¬ M.mem i α

def row_tail_m {n} (α p D : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest D.weaken) (.conj (.existsE (entry_m (.bound 1) .newest p.weaken.weaken))
    (.neg (.mem .newest α.weaken))))
derive_free_closed row_tail_m

def Row_tail_bound_d (I : kpair_convention_l.Interpretation M) (α p n : M.Domain) : Prop :=
  ∃ D, Row_tail_d α p D ∧ M.CardinalLessOrEqual I D n

def row_tail_bound_m {n} (α p k : Term n) : Formula 1 n :=
  .existsE (.conj (row_tail_m α.weaken p.weaken .newest)
    (Formula.cardinalLessOrEqual kpair_convention_l .newest k.weaken))
derive_free_closed row_tail_bound_m

theorem row_tail_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α p D : Term n) :
    Formula.satisfies ρ (row_tail_m α p D) ↔ Row_tail_d (α.eval ρ) (p.eval ρ) (D.eval ρ) := by
  simp only [row_tail_m, Row_tail_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, entry_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

theorem row_tail_bound_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α p k : Term n) : Formula.satisfies ρ (row_tail_bound_m α p k) ↔
      Row_tail_bound_d I (α.eval ρ) (p.eval ρ) (k.eval ρ) := by
  simp only [row_tail_bound_m, Row_tail_bound_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    row_tail_sat_l hE, Formula.satisfies_cardinalLessOrEqual_iff I hE, Definitional.Term.eval_weaken]
  rfl

theorem row_tail_exists_l (hZF : M.Models ZF) (α p : M.Domain) : ∃ D, Row_tail_d α p D := by
  obtain ⟨S, hS⟩ := coord_exists_l M hZF p
  obtain ⟨D, hD⟩ := KP.difference_exists_d (ZF.modelsKP hZF) α S
  exact ⟨D, fun i => (hD i).trans (and_congr_left fun _ => hS i)⟩

/-- 把一个已有尾坐标移入新前缀，尾支撑大小严格减少一个。 -/
theorem row_tail_delete_l (hZF : M.Models ZF) {α β p n s i}
    (hs : M.SuccessorOf s n) (hαβ : M.MemberSubset α β) (hiβ : M.mem i β) (hiα : ¬ M.mem i α)
    (hi : ∃ v, Entry_d M i v p)
    (hp : Row_tail_bound_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α p s) :
    Row_tail_bound_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β p n := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨D, hD, hd⟩ := hp
  obtain ⟨E, hE⟩ := ZF.erase_set_l hZF i D
  obtain ⟨f, hf⟩ := ZF.delete_bound_l I hZF hs hd ((hD i).mpr ⟨hi, hiα⟩) hE
  obtain ⟨T, hT⟩ := row_tail_exists_l hZF β p
  obtain ⟨g, hg⟩ := ZF.exists_inclusionInjection hZF I (show M.MemberSubset T E from fun j hj => by
    obtain ⟨hj, hjβ⟩ := (hT j).mp hj
    exact (hE j).mpr ⟨(hD j).mpr ⟨hj, fun hjα => hjβ (hαβ j hjα)⟩, fun he => hjβ (he ▸ hiβ)⟩)
  exact ⟨T, hT, ZF.exists_compositionInjection hZF I hg hf⟩

end YesMetaZFC.Model.Forcing.Internal
