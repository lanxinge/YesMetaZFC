import YesMetaZFC.SetTheory.Descriptive.TreeTail

/-! # 任意字母表上的无限列首项拼接

有限列沿用 Cons_d；同一图方程也构造无限拼接和首尾分解。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

omit I in
theorem omega_zero_or_succ_l {ω z j : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) (hj : M.mem j ω) :
    j = z ∨ ∃ i, M.mem i ω ∧ M.SuccessorOf j i := by
  classical
  by_cases eq : j = z
  · exact Or.inl eq
  apply Or.inr
  apply hw.exists_predecessor_of_mem_of_nonempty hZF hj
  exact Classical.byContradiction (fun no => eq (hZF.1.eq_of_same_members j z fun x =>
    iff_of_false (fun hx => no ⟨x, hx⟩) (hz x)))

theorem Cons_d.successor_l {ω z a f g i j x : M.Domain} (hw : M.IsOmega ω) (hz : ∀ v, ¬ M.mem v z)
    (hi : M.mem i ω) (sj : M.SuccessorOf j i) (h : Cons_d I z a f g) : M.PairMember I j x g ↔ M.PairMember I i x f := by
  refine (h.2 j x).trans ⟨?_, fun ix => Or.inr ⟨i, ix, sj⟩⟩
  rintro (⟨eq, _⟩ | ⟨k, kx, sk⟩)
  · exact (hz i (eq ▸ sj.predecessor_mem)).elim
  · exact (sj.predecessor_eq hZF.1 (hw.members_areOrdinals hZF i hi) sk).symm ▸ kx

theorem cons_omega_l {ω X z a f : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ha : M.mem a X) (ff : M.IsSetFunctionFromTo I f ω X) : ∃ g, M.IsSetFunctionFromTo I g ω X ∧ Cons_d I z a f g := by
  obtain ⟨z', hz', hzω⟩ := hw.1.1
  have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x); subst z'
  let ρ : Env M 3 := ⟨fun i => [z, a, f].get i, fun _ => z⟩
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 3)))
      (.existsE (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 5)) (Formula.isSuccessor (.bound 2) .newest))) }
  have sat j x : φ.denote ρ j x ↔ (j = z ∧ x = a) ∨ ∃ i, M.PairMember I i x f ∧ M.SuccessorOf j i := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff]; rfl
  obtain ⟨g, fg, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X) (by
    intro j hj
    rcases omega_zero_or_succ_l hZF hw hz hj with rfl | ⟨i, hi, sj⟩
    · exact ⟨a, (sat _ a).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · obtain ⟨x, _, ix⟩ := ff.2.2 i hi
      exact ⟨x, (sat j x).mpr (Or.inr ⟨i, ix, sj⟩)⟩) (by
      intro j _ x y jx jy
      rcases (sat j x).mp jx with ⟨eq, rfl⟩ | ⟨i, ix, sj⟩ <;>
        rcases (sat j y).mp jy with ⟨eq', rfl⟩ | ⟨k, ky, sk⟩
      · rfl
      · exact (hz k (eq ▸ sk.predecessor_mem)).elim
      · exact (hz i (eq' ▸ sj.predecessor_mem)).elim
      · have eq := sj.predecessor_eq hZF.1 (hw.members_areOrdinals hZF i (ff.input_mem_of_pairMember ix)) sk
        exact ff.1.2 i x y ix (eq.symm ▸ ky)) (by
          intro j x _ jx
          exact ((sat j x).mp jx).elim (fun h => h.2.symm ▸ ha) (fun ⟨_, ix, _⟩ => ff.output_mem_of_pairMember ix))
  refine ⟨g, fg, fg.1.1, fun j x => (graph j x).trans ((and_congr_right fun _ => sat j x).trans ⟨And.right, ?_⟩)⟩
  intro h
  refine ⟨?_, h⟩
  rcases h with ⟨rfl, _⟩ | ⟨i, ix, sj⟩
  · exact hzω
  · obtain ⟨k, sk, hk⟩ := hw.1.2 i (ff.input_mem_of_pairMember ix)
    exact sk.eq hZF.1 sj ▸ hk

theorem tail_omega_l {ω X z f : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ff : M.IsSetFunctionFromTo I f ω X) : ∃ a g, M.mem a X ∧ M.IsSetFunctionFromTo I g ω X ∧ Cons_d I z a g f := by
  obtain ⟨z', hz', hzω⟩ := hw.1.1
  have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x); subst z'
  obtain ⟨a, ha, za⟩ := ff.2.2 z hzω
  let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj (Formula.isSuccessor .newest (.bound 2))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))) }
  have sat i x : φ.denote ρ i x ↔ ∃ j, M.SuccessorOf j i ∧ M.PairMember I j x f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨g, fg, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X) (by
    intro i hi
    obtain ⟨j, sj, hj⟩ := hw.1.2 i hi
    obtain ⟨x, _, jx⟩ := ff.2.2 j hj
    exact ⟨x, (sat i x).mpr ⟨j, sj, jx⟩⟩) (by
      intro i _ x y ix iy
      obtain ⟨j, sj, jx⟩ := (sat i x).mp ix
      obtain ⟨k, sk, ky⟩ := (sat i y).mp iy
      exact ff.1.2 j x y jx (sk.eq hZF.1 sj ▸ ky))
    (fun i x _ ix => ((sat i x).mp ix).elim fun _ h => ff.output_mem_of_pairMember h.2)
  refine ⟨a, g, ha, fg, ff.1.1, fun j x => ⟨?_, ?_⟩⟩
  · intro jx
    rcases omega_zero_or_succ_l hZF hw hz (ff.input_mem_of_pairMember jx) with rfl | ⟨i, hi, sj⟩
    · exact Or.inl ⟨rfl, ff.1.2 _ x a jx za⟩
    · exact Or.inr ⟨i, (graph i x).mpr ⟨hi, (sat i x).mpr ⟨j, sj, jx⟩⟩, sj⟩
  · rintro (⟨rfl, rfl⟩ | ⟨i, ix, sj⟩)
    · exact za
    · obtain ⟨k, sk, kx⟩ := (sat i x).mp ((graph i x).mp ix).2
      exact sk.eq hZF.1 sj ▸ kx

end YesMetaZFC.SetTheory.Descriptive
