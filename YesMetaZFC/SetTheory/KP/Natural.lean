import YesMetaZFC.SetTheory.KP.Transitive
import YesMetaZFC.SetTheory.Ord.Natural

/-! # KPi 中的内部自然数

用遗传的“空或后继”条件作 Δ₀ 分离，再由公式成员归纳证明最小性。
这里的有限性由模型解释，允许非标准自然数。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

namespace KP

def succ0_m {n} (s x : Term n) : Formula 1 n :=
  .conj (.mem x s) (.conj (Formula.subset x s)
    (Formula.forallMem s (.disj (.mem .newest x.weaken) (Formula.extensionalEq .newest x.weaken))))
derive_free_closed succ0_m

theorem succ0_delta_l {n} (s x : Term n) : (succ0_m s x).IsDelta0 :=
  .conj (.mem _ _) (.conj (.atom _ _ _) (.forallMem _ (.disj (.mem _ _) (.atom _ _ _))))

theorem succ0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (s x : Term n) :
    Formula.satisfies ρ (succ0_m s x) ↔ M.SuccessorOf (s.eval ρ) (x.eval ρ) := by
  simp only [succ0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨hx, hs, h⟩ a
    exact ⟨fun ha => (h a ha).imp_right (fun (he : a = x.eval ρ) => he ▸ (fun _ => Iff.rfl)),
      fun ha => ha.elim (hs a) (fun he => (hE.eq_of_same_members _ _ he).symm ▸ hx)⟩
  · intro h
    exact ⟨h.predecessor_mem, fun a ha => (h a).mpr (Or.inl ha),
      fun a ha => ((h a).mp ha).imp_right (hE.eq_of_same_members _ _)⟩

def N0_base_d (x : M.Domain) : Prop :=
  (∀ a, ¬ M.mem a x) ∨ ∃ y, M.mem y x ∧ M.SuccessorOf x y

def n0_base_m {n} (x : Term n) : Formula 1 n :=
  .disj (Formula.forallMem x .falsum) (Formula.existsMem x (succ0_m x.weaken .newest))
derive_free_closed n0_base_m

theorem n0_base_delta_l {n} (x : Term n) : (n0_base_m x).IsDelta0 :=
  .disj (.forallMem _ .falsum) (.existsMem _ (succ0_delta_l ..))

theorem n0_base_sat_l (hE : Extensional M) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (n0_base_m x) ↔ N0_base_d (x.eval ρ) := by
  simp only [n0_base_m, N0_base_d, Formula.satisfies_disj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_falsum_iff, Formula.satisfies_existsMem_iff, succ0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def N0_d (x : M.Domain) : Prop := M.TransitiveSet x ∧ N0_base_d x ∧
  ∀ a, M.mem a x → M.TransitiveSet a ∧ N0_base_d a

def n0_m {n} (x : Term n) : Formula 1 n :=
  .conj (Formula.isTransitive x) (.conj (n0_base_m x)
    (Formula.forallMem x (.conj (Formula.isTransitive .newest) (n0_base_m .newest))))
derive_free_closed n0_m

theorem n0_delta_l {n} (x : Term n) : (n0_m x).IsDelta0 :=
  .conj (Formula.isTransitive_delta0 _) (.conj (n0_base_delta_l _)
    (.forallMem _ (.conj (Formula.isTransitive_delta0 _) (n0_base_delta_l _))))

theorem n0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (n0_m x) ↔ N0_d (x.eval ρ) := by
  simp only [n0_m, N0_d, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    n0_base_sat_l hE, Formula.satisfies_forallMem_iff, Definitional.Term.eval_newest]

theorem N0_d.mem_l {x y : M.Domain} (h : N0_d x) (hy : M.mem y x) : N0_d y :=
  ⟨(h.2.2 y hy).1, (h.2.2 y hy).2, fun a ha => h.2.2 a (h.1 y hy a ha)⟩

theorem n0_empty_l {x : M.Domain} (h : ∀ a, ¬ M.mem a x) : N0_d x :=
  ⟨fun a ha => (h a ha).elim, Or.inl h, fun a ha => (h a ha).elim⟩

theorem n0_succ_l (hE : Extensional M) {x s : M.Domain} (h : N0_d x) (hs : M.SuccessorOf s x) : N0_d s := by
  have split a : M.mem a s ↔ M.mem a x ∨ a = x :=
    (hs a).trans (or_congr_right ⟨hE.eq_of_same_members _ _, fun he => he ▸ (fun _ => Iff.rfl)⟩)
  refine ⟨?_, Or.inr ⟨x, hs.predecessor_mem, hs⟩, fun a ha => ?_⟩
  · intro a ha b hb
    exact (split b).mpr (Or.inl (((split a).mp ha).elim (fun ha => h.1 a ha b hb) (fun he => he ▸ hb)))
  · exact ((split a).mp ha).elim (h.2.2 a) (fun he => he.symm ▸ ⟨h.1, h.2.1⟩)

/-- 传递的序数集合是序数；最小元只使用集合正则。 -/
theorem ordinal_of_transitive_l (hKP : M.Models KP) {A : M.Domain} (hA : M.TransitiveSet A)
    (ho : ∀ a, M.mem a A → M.IsOrdinal a) : M.IsOrdinal A := by
  have cmp a ha b hb := Structure.IsOrdinal.trichotomy hKP.1 (ho a ha) (ho b hb)
    (difference_exists_d hKP) (intersection_exists_d hKP a b)
  refine ⟨hA, ⟨⟨fun a _ => mem_irrefl_d hKP a,
    fun a _ b _ c hc hab hbc => (ho c hc).transitive b hbc a hab, cmp⟩, ?_⟩⟩
  intro B hB hn
  obtain ⟨a, ha, hm⟩ := mem_minimal_exists_d hKP hn
  exact ⟨a, ha, fun b hb => (cmp a (hB a ha) b (hB b hb)).elim Or.inl
    (fun h => h.elim Or.inr (fun h => (hm b hb h).elim))⟩

end KP
namespace KPi

theorem n0_in_inductive_l (hM : M.Models KPi) {I x : M.Domain} (hI : M.IsInductive I)
    (hx : KP.N0_d x) : M.mem x I := by
  obtain ⟨hKP, hi⟩ := models_iff_l.mp hM
  let ρ : Env M 1 := ⟨fun _ => I, fun _ => I⟩
  let φ : UnarySchema 1 := { body := .imp (KP.n0_m .newest) (.mem .newest (.bound 1)) }
  have hφ a : φ.denote ρ a ↔ (KP.N0_d a → M.mem a I) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.n0_sat_l hKP.1, Formula.satisfies_mem_iff]
    rfl
  apply (hφ x).mp (hi φ ρ ?_ x) hx
  intro a ih
  apply (hφ a).mpr
  intro ha
  rcases ha.2.1 with he | ⟨b, hb, hs⟩
  · obtain ⟨e, he', heI⟩ := hI.1
    exact (hKP.1.eq_of_same_members e a (fun t => iff_of_false (he' t) (he t))) ▸ heI
  · obtain ⟨s, hs', hsI⟩ := hI.2 b ((hφ b).mp (ih b hb) (ha.mem_l hb))
    exact (Structure.SuccessorOf.eq hKP.1 hs' hs) ▸ hsI

theorem exists_omega_l (hM : M.Models KPi) : ∃ ω, M.IsOmega ω ∧ ∀ x, M.mem x ω ↔ KP.N0_d x := by
  let hKP := (models_iff_l.mp hM).1
  obtain ⟨I, hI⟩ := KP.exists_inductive hKP
  let φ : Delta0UnarySchema 0 := { body := KP.n0_m .newest, delta0 := KP.n0_delta_l _ }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => I⟩
  obtain ⟨ω, hω'⟩ := KP.separation_exists_d hKP φ ρ I
  have hω x : M.mem x ω ↔ KP.N0_d x := by
    rw [hω' x, show Formula.satisfies (ρ.push x) φ.body ↔ KP.N0_d x from KP.n0_sat_l hKP.1 _ _]
    exact ⟨And.right, fun h => ⟨n0_in_inductive_l hM hI h, h⟩⟩
  refine ⟨ω, ⟨⟨?_, ?_⟩, fun J hJ x hx => n0_in_inductive_l hM hJ ((hω x).mp hx)⟩, hω⟩
  · obtain ⟨e, he, _⟩ := hI.1
    exact ⟨e, he, (hω e).mpr (KP.n0_empty_l he)⟩
  · intro x hx
    obtain ⟨s, hs, _⟩ := hI.2 x (n0_in_inductive_l hM hI ((hω x).mp hx))
    exact ⟨s, hs, (hω s).mpr (KP.n0_succ_l hKP.1 ((hω x).mp hx) hs)⟩

theorem n0_ordinal_l (hM : M.Models KPi) {x : M.Domain} (hx : KP.N0_d x) : M.IsOrdinal x := by
  obtain ⟨hKP, hi⟩ := models_iff_l.mp hM
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => x⟩
  let φ : UnarySchema 0 := { body := .imp (KP.n0_m .newest) (Formula.isOrdinal .newest) }
  have hφ a : φ.denote ρ a ↔ (KP.N0_d a → M.IsOrdinal a) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.n0_sat_l hKP.1,
      Formula.satisfies_isOrdinal_iff, Definitional.Term.eval_newest]
  apply (hφ x).mp (hi φ ρ ?_ x) hx
  intro a ih
  exact (hφ a).mpr fun ha => KP.ordinal_of_transitive_l hKP ha.1
    (fun b hb => (hφ b).mp (ih b hb) (ha.mem_l hb))

end KPi
end YesMetaZFC.SetTheory
