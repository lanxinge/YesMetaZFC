import YesMetaZFC.SetTheory.FlatPairing.Shift

/-! # 平坦配对的左右标签

左标签是平移后的成员像，右标签再加入空集。空集不在平移像中，故两类
标签互不相交；平移单射保证标签保留原集合。全部标签由 KP 的实际像集构造。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Fp_tag_d (b : Bool) (ω x y : M.Domain) : Prop := ∀ z,
  M.mem z y ↔ (b = true ∧ ∀ a, ¬ M.mem a z) ∨ ∃ a, M.mem a x ∧ Fp_shift_d ω a z

def fp_tag0_m {d} (b : Bool) (ω x y : Term d) : Formula 1 d := .conj
  (Formula.forallMem y (.disj (if b then Formula.forallMem .newest .falsum else .falsum)
    (Formula.existsMem x.weaken (fp_shift0_m ω.weaken.weaken .newest (.bound 1)))))
  (.conj (Formula.forallMem x (Formula.existsMem y.weaken (fp_shift0_m ω.weaken.weaken (.bound 1) .newest)))
    (if b then Formula.existsMem y (Formula.forallMem .newest .falsum) else .truth))
@[simp] theorem fp_tag0_m_freeClosed {d} (b : Bool) (ω x y : Term d)
    (hω : ω.freeSupport = []) (hx : x.freeSupport = []) (hy : y.freeSupport = []) :
    (fp_tag0_m b ω x y).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [fp_tag0_m, Definitional.Formula.FreeClosed, hω, hx, hy]

theorem fp_tag0_delta_l {d} (b : Bool) (ω x y : Term d) : (fp_tag0_m b ω x y).IsDelta0 := by
  cases b
  · exact .conj (.forallMem _ (.disj .falsum (.existsMem _ (fp_shift0_delta_l ..))))
      (.conj (.forallMem _ (.existsMem _ (fp_shift0_delta_l ..))) .truth)
  · exact .conj (.forallMem _ (.disj (.forallMem _ .falsum) (.existsMem _ (fp_shift0_delta_l ..))))
      (.conj (.forallMem _ (.existsMem _ (fp_shift0_delta_l ..))) (.existsMem _ (.forallMem _ .falsum)))

/-- 原有左右标签公式直接解释为同一语义关系。 -/
theorem fp_tag_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b : Bool) (ω x y : Term d) :
    Formula.satisfies ρ (if b then FlatPairing.isRightTag y x ω else FlatPairing.isLeftTag y x ω) ↔
      Fp_tag_d b (ω.eval ρ) (x.eval ρ) (y.eval ρ) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, FlatPairing.isLeftTag, FlatPairing.isRightTag,
    Fp_tag_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_existsMem_iff,
    fp_shift_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest, false_and, false_or, true_and]
  all_goals rfl

/-- 有界矩阵与原标签完全等价，不要求所在传递模型满足 ZF。 -/
theorem fp_tag0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b : Bool) (ω x y : Term d)
    (hω : M.IsInductive (ω.eval ρ)) :
    Formula.satisfies ρ (fp_tag0_m b ω x y) ↔ Fp_tag_d b (ω.eval ρ) (x.eval ρ) (y.eval ρ) := by
  have shape : Formula.satisfies ρ (fp_tag0_m b ω x y) ↔
      (∀ z, M.mem z (y.eval ρ) → (b = true ∧ ∀ a, ¬ M.mem a z) ∨
        ∃ a, M.mem a (x.eval ρ) ∧ Fp_shift_d (ω.eval ρ) a z) ∧
      (∀ a, M.mem a (x.eval ρ) → ∃ z, M.mem z (y.eval ρ) ∧ Fp_shift_d (ω.eval ρ) a z) ∧
      (b = true → ∃ e, M.mem e (y.eval ρ) ∧ ∀ a, ¬ M.mem a e) := by
    cases b <;> simp only [fp_tag0_m, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_conj_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff,
      Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff, fp_shift0_sat_l hE,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest, false_and, false_or, true_and,
      false_implies, true_implies, and_true]
    all_goals rfl
  refine shape.trans ⟨?_, ?_⟩
  · rintro ⟨bound, total, zero⟩ z
    refine ⟨bound z, ?_⟩
    rintro (⟨hb, hz⟩ | ⟨a, ha, shift⟩)
    · obtain ⟨e, he, empty⟩ := zero hb
      exact hE.eq_of_same_members e z (fun t => iff_of_false (empty t) (hz t)) ▸ he
    · obtain ⟨z', hz', shift'⟩ := total a ha
      exact shift'.unique_l hE shift ▸ hz'
  · intro tag
    refine ⟨fun z => (tag z).mp, fun a ha => ?_, fun hb => ?_⟩
    · obtain ⟨z, shift⟩ := fp_shift_exists_l hω a
      exact ⟨z, (tag z).mpr (Or.inr ⟨a, ha, shift⟩), shift⟩
    · obtain ⟨e, he, _⟩ := hω.1
      exact ⟨e, (tag e).mpr (Or.inl ⟨hb, he⟩), he⟩

theorem Fp_tag_d.unique_l (hE : Extensional M) {b : Bool} {ω x y z : M.Domain}
    (h : Fp_tag_d b ω x y) (k : Fp_tag_d b ω x z) : y = z :=
  hE.eq_of_same_members y z (fun a => (h a).trans (k a).symm)

theorem fp_tag_exists_l (hKP : M.Models KP) {ω : M.Domain} (hω : M.IsInductive ω) (b : Bool) (x : M.Domain) :
    ∃ y, Fp_tag_d b ω x y := by
  let φ : Delta0BinarySchema 1 := { body := fp_shift0_m (.bound 2) (.bound 1) .newest, delta0 := fp_shift0_delta_l .. }
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  have sat a z : φ.toBinarySchema.denote ρ a z ↔ Fp_shift_d ω a z := fp_shift0_sat_l hKP.1 ..
  obtain ⟨Y, image⟩ := KP.d0_image_l hKP φ ρ x
    (fun a _ => (fp_shift_exists_l hω a).imp fun z hz => (sat a z).mpr hz)
    (fun _ _ z w hz hw => ((sat _ z).mp hz).unique_l hKP.1 ((sat _ w).mp hw))
  have spec z : M.mem z Y ↔ ∃ a, M.mem a x ∧ Fp_shift_d ω a z :=
    (image z).trans (exists_congr fun a => and_congr_right fun _ => sat a z)
  cases b
  · exact ⟨Y, fun z => (spec z).trans (by simp)⟩
  · obtain ⟨e, he, _⟩ := hω.1
    obtain ⟨y, hy⟩ := KP.exists_insert hKP Y e
    refine ⟨y, fun z => (hy z).trans ?_⟩
    simp only [true_and]
    exact ⟨fun hh => hh.elim (fun hz => Or.inr ((spec z).mp hz)) (fun hz => Or.inl (hz ▸ he)),
      fun hh => hh.elim (fun hz => Or.inr (hKP.1.eq_of_same_members z e (fun t => iff_of_false (hz t) (he t))))
        (fun hz => Or.inl ((spec z).mpr hz))⟩

theorem Fp_tag_d.marker_l (hE : Extensional M) {b : Bool} {ω x y e : M.Domain}
    (hω : M.IsInductive ω) (he : ∀ a, ¬ M.mem a e) (h : Fp_tag_d b ω x y) : M.mem e y ↔ b = true :=
  (h e).trans ⟨fun hh => hh.elim And.left (fun ⟨_, _, shift⟩ => (shift.not_empty_l hE hω he).elim),
    fun hb => Or.inl ⟨hb, he⟩⟩

/-- 标签同时唯一确定左右标志和原集合。 -/
theorem Fp_tag_d.injective_l (hE : Extensional M) {b c : Bool} {ω x y t : M.Domain}
    (hω : M.IsInductive ω) (ordinals : ∀ n, M.mem n ω → M.IsOrdinal n)
    (h : Fp_tag_d b ω x t) (k : Fp_tag_d c ω y t) : b = c ∧ x = y := by
  obtain ⟨e, he, _⟩ := hω.1
  have bits := (h.marker_l hE hω he).symm.trans (k.marker_l hE hω he)
  have eq : b = c := by cases b <;> cases c <;> simp_all
  subst c
  have sub {u v} (hu : Fp_tag_d b ω u t) (hv : Fp_tag_d b ω v t) : M.MemberSubset u v := by
    intro a ha
    obtain ⟨z, shift⟩ := fp_shift_exists_l hω a
    rcases (hv z).mp ((hu z).mpr (Or.inr ⟨a, ha, shift⟩)) with ⟨_, empty⟩ | ⟨a', ha', shift'⟩
    · exact (shift.not_empty_l hE hω empty).elim
    · exact (shift.injective_l hE hω ordinals shift').symm ▸ ha'
  exact ⟨rfl, hE.eq_of_same_members x y (fun a => ⟨sub h k a, sub k h a⟩)⟩

end YesMetaZFC.SetTheory
