import YesMetaZFC.SetTheory.Ord.Natural

/-! # 内部语法标签的有限序数码

固定构造符的标签由空集和有限次后继唯一确定。这里只编码宿主给出的有限标签；
公式长度、变量编号和递归指标仍是模型自身 ω 的元素，不要求它们外部标准。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Num_d : Nat → M.Domain → Prop
  | 0, x => ∀ y, ¬ M.mem y x
  | n+1, x => ∃ y, Num_d n y ∧ M.SuccessorOf x y

def num_m : (k : Nat) → {n : Nat} → Term n → Formula 1 n
  | 0, _, x => Formula.isEmpty x
  | k+1, _, x => .existsE (.conj (num_m k .newest) (Formula.isSuccessor x.weaken .newest))

@[simp] theorem num_closed_l (k : Nat) {n} (x : Term n) (hx : x.freeSupport = []) :
    (num_m k x).FreeClosed := by
  induction k generalizing n with
  | zero => exact Formula.isEmpty_freeClosed x hx
  | succ k ih =>
    simp only [num_m, Definitional.Formula.FreeClosed]
    exact ⟨ih .newest rfl, Formula.isSuccessor_freeClosed _ _ (by simpa using hx) rfl⟩

theorem num_sat_l (k : Nat) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (num_m k x) ↔ Num_d k (x.eval ρ) := by
  induction k generalizing n with
  | zero => exact Formula.satisfies_isEmpty_iff ρ x
  | succ k ih =>
    simp only [num_m, Num_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      ih, Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem num_exists_l (hKP : M.Models KP) (k : Nat) : ∃ x : M.Domain, Num_d k x := by
  induction k with
  | zero => exact KP.exists_empty hKP
  | succ k ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨y, hy⟩ := KP.exists_successor hKP x
    exact ⟨y, x, hx, hy⟩

theorem num_unique_l (hE : Extensional M) {k} {x y : M.Domain} (hx : Num_d k x) (hy : Num_d k y) : x = y := by
  induction k generalizing x y with
  | zero => exact hE.eq_of_same_members x y (fun a => ⟨fun h => (hx a h).elim, fun h => (hy a h).elim⟩)
  | succ k ih =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    have he := ih ha hb
    subst b
    exact hE.eq_of_same_members x y (fun a => (hxa a).trans (hyb a).symm)

theorem num_lt_l (hE : Extensional M) {k l x y} (hx : Num_d k x) (hy : Num_d l y)
    (h : k < l) : M.mem x y := by
  induction l generalizing y with
  | zero => omega
  | succ l ih =>
    obtain ⟨a, ha, hya⟩ := hy
    by_cases hk : k = l
    · subst k
      exact (num_unique_l hE ha hx) ▸ hya.predecessor_mem
    · exact (hya x).mpr (Or.inl (ih ha (by omega)))

theorem num_injective_l (hKP : M.Models KP) {k l} {x : M.Domain} (hk : Num_d k x) (hl : Num_d l x) : k = l := by
  apply Classical.byContradiction
  intro h
  have he : M.mem x x := by
    rcases Nat.lt_or_gt_of_ne h with h | h
    · exact num_lt_l hKP.1 hk hl h
    · exact num_lt_l hKP.1 hl hk h
  exact KP.mem_irrefl_d hKP x he

theorem num_mem_l (hE : Extensional M) {ω k x} (hω : M.IsOmega ω) (hx : Num_d k x) : M.mem x ω := by
  induction k generalizing x with
  | zero =>
    obtain ⟨e, he, heω⟩ := hω.1.1
    exact num_unique_l hE (k := 0) he hx ▸ heω
  | succ k ih =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨y, hya, hyω⟩ := hω.1.2 a (ih ha)
    have he := hE.eq_of_same_members y x (fun z => (hya z).trans (hxa z).symm)
    exact he ▸ hyω

end YesMetaZFC.SetTheory.Internal
