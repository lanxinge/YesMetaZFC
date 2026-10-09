import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Closure

/-! # 平坦配对所用的自然数平移

沿用原 FlatPairing.isShift：自然数移到后继，其他集合保持不变。
有界正文用于传递秩层中的绝对性；原公式的语义不作更换。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Fp_shift_d (ω x y : M.Domain) : Prop :=
  (M.mem x ω ∧ M.SuccessorOf y x) ∨ (¬ M.mem x ω ∧ y = x)

def fp_shift0_m {d} (ω x y : Term d) : Formula 1 d :=
  .disj (.conj (.mem x ω) (KP.succ0_m y x)) (.conj (.neg (.mem x ω)) (Formula.extensionalEq y x))
derive_free_closed fp_shift0_m

theorem fp_shift0_delta_l {d} (ω x y : Term d) : (fp_shift0_m ω x y).IsDelta0 :=
  .disj (.conj (.mem _ _) (KP.succ0_delta_l ..)) (.conj (.neg (.mem _ _)) (.atom _ _ _))

theorem fp_shift0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω x y : Term d) :
    Formula.satisfies ρ (fp_shift0_m ω x y) ↔ Fp_shift_d (ω.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [fp_shift0_m, Fp_shift_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, KP.succ0_sat_l hE, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE]

theorem fp_shift_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω x y : Term d) :
    Formula.satisfies ρ (FlatPairing.isShift y x ω) ↔ Fp_shift_d (ω.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [FlatPairing.isShift, Fp_shift_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE]

theorem fp_shift_exists_l {ω : M.Domain} (hω : M.IsInductive ω) (x : M.Domain) :
    ∃ y, Fp_shift_d ω x y := by
  classical
  by_cases hx : M.mem x ω
  · obtain ⟨y, hy, _⟩ := hω.2 x hx
    exact ⟨y, Or.inl ⟨hx, hy⟩⟩
  · exact ⟨x, Or.inr ⟨hx, rfl⟩⟩

theorem Fp_shift_d.unique_l (hE : Extensional M) {ω x y z : M.Domain}
    (h : Fp_shift_d ω x y) (k : Fp_shift_d ω x z) : y = z := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, rfl⟩ <;> rcases k with ⟨hx', hz⟩ | ⟨hx', rfl⟩
  · exact Structure.SuccessorOf.eq hE hy hz
  · exact (hx' hx).elim
  · exact (hx hx').elim
  · rfl

theorem Fp_shift_d.natural_l (hE : Extensional M) {ω x y : M.Domain}
    (hω : M.IsInductive ω) (h : Fp_shift_d ω x y) : M.mem y ω ↔ M.mem x ω := by
  rcases h with ⟨hx, hy⟩ | ⟨_, rfl⟩
  · obtain ⟨z, hz, hzω⟩ := hω.2 x hx
    exact ⟨fun _ => hx, fun _ => Structure.SuccessorOf.eq hE hz hy ▸ hzω⟩
  · rfl

theorem Fp_shift_d.mem_l {ω x y T : M.Domain} (hT : M.TransitiveSet T)
    (hy : M.mem y T) (h : Fp_shift_d ω x y) : M.mem x T := by
  rcases h with ⟨_, succ⟩ | ⟨_, rfl⟩
  · exact hT y hy x succ.predecessor_mem
  · exact hy

/-- 平移没有零值，为左右标签保留一个可判别的位置。 -/
theorem Fp_shift_d.not_empty_l (hE : Extensional M) {ω x y : M.Domain}
    (hω : M.IsInductive ω) (h : Fp_shift_d ω x y) : ¬ (∀ z, ¬ M.mem z y) := by
  intro empty
  rcases h with ⟨_, hy⟩ | ⟨hx, rfl⟩
  · exact empty x hy.predecessor_mem
  · obtain ⟨e, he, heω⟩ := hω.1
    exact hx (hE.eq_of_same_members e y (fun z => iff_of_false (he z) (empty z)) ▸ heω)

theorem Fp_shift_d.injective_l (hE : Extensional M) {ω x u y : M.Domain}
    (hω : M.IsInductive ω) (ordinals : ∀ n, M.mem n ω → M.IsOrdinal n)
    (h : Fp_shift_d ω x y) (k : Fp_shift_d ω u y) : x = u := by
  have nat := (h.natural_l hE hω).symm.trans (k.natural_l hE hω)
  rcases h with ⟨hx, hy⟩ | ⟨hx, rfl⟩ <;> rcases k with ⟨hu, hy'⟩ | ⟨hu, he⟩
  · exact Structure.SuccessorOf.predecessor_eq hE (ordinals x hx) hy hy'
  · exact (hu (nat.mp hx)).elim
  · exact (hx (nat.mpr hu)).elim
  · exact he

end YesMetaZFC.SetTheory
