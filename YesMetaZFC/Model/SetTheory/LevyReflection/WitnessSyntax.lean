import YesMetaZFC.Model.SetTheory.LevyReflection.Parameters
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 全部有限参数下的见证界公式

用实际 ω 赋值图承载有限参数组，收集时只读取指定的有限坐标。见证界的定义
量化任意参数赋值；公式中的有限量词块精确实现这一量化。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def lr_and_m {d} : {k : Nat} → (Fin k → Formula 1 d) → Formula 1 d
  | 0, _ => .truth
  | k+1, f => .conj (f 0) (lr_and_m (fun i : Fin k => f i.succ))

@[simp] theorem lr_and_closed_l {d k} (f : Fin k → Formula 1 d) (h : ∀ i, (f i).FreeClosed) :
    (lr_and_m f).FreeClosed := by
  induction k with
  | zero => simp only [lr_and_m, Definitional.Formula.FreeClosed]
  | succ k ih =>
    simp only [lr_and_m, Definitional.Formula.FreeClosed]
    exact ⟨h 0, ih (fun i => f i.succ) (fun i => h i.succ)⟩

theorem lr_and_sat_l {d k} (ρ : Env M d) (f : Fin k → Formula 1 d) :
    Formula.satisfies ρ (lr_and_m f) ↔ ∀ i, Formula.satisfies ρ (f i) := by
  induction k with
  | zero => exact (Formula.satisfies_truth_iff ρ).trans ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | succ k ih =>
    rw [lr_and_m, Formula.satisfies_conj_iff, ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩

def Lr_bound_d {n} (φ : UnarySchema n) (X Y : M.Domain) : Prop :=
  ∀ ρ : Env M n, (∀ i, M.mem (ρ.bound i) X) → (∃ x, φ.denote ρ x) → ∃ x, M.mem x Y ∧ φ.denote ρ x

theorem Lr_bound_d.mono_l {n} {φ : UnarySchema n} {X Y A B} (h : Lr_bound_d φ X Y)
    (hA : M.MemberSubset A X) (hB : M.MemberSubset Y B) : Lr_bound_d φ A B := by
  intro ρ hρ hx
  obtain ⟨x, hxY, hx⟩ := h ρ (fun i => hA _ (hρ i)) hx
  exact ⟨x, hB x hxY, hx⟩

theorem lr_pred_sat_l {n d} (φ : UnarySchema n) (ρ : Env M d) (p : Fin n → M.Domain) (x : M.Domain) :
    Formula.satisfies ((lr_env_l ρ p).push x)
      (pred_m φ (fun i => (Term.bound ⟨i.val, by omega⟩ : Term (d+n)).weaken) .newest) ↔
        φ.denote ⟨p, ρ.free⟩ x := by
  have hh := pred_sat_l M φ ((lr_env_l ρ p).push x)
    (fun i => (Term.bound ⟨i.val, by omega⟩ : Term (d+n)).weaken) .newest
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at hh
  have he : (⟨fun i => (lr_env_l ρ p).bound ⟨i.val, by omega⟩,
      ((lr_env_l ρ p).push x).free⟩ : Env M n) = ⟨p, ρ.free⟩ := by
    rw [Env.mk.injEq]
    exact ⟨funext (lr_env_bound_l ρ p), lr_env_free_l ρ p⟩
  exact hh.trans (he ▸ Iff.rfl)

def lr_bound_m {n d} (φ : UnarySchema n) (X Y : Term d) : Formula 1 d :=
  let ψ := pred_m φ (fun i => (Term.bound ⟨i.val, by omega⟩ : Term (d+n)).weaken) .newest
  lr_all_m n X (.imp (.existsE ψ) (Formula.existsMem (lr_shift_l n Y) ψ))

@[simp] theorem lr_bound_closed_l {n d} (φ : UnarySchema n) (X Y : Term d)
    (hX : X.freeSupport = []) (hY : Y.freeSupport = []) : (lr_bound_m φ X Y).FreeClosed := by
  apply lr_all_closed_l _ _ _ hX
  simp -implicitDefEqProofs only [Definitional.Formula.FreeClosed, Formula.existsMem]
  exact ⟨pred_m_freeClosed _ _ _ (fun _ => rfl) rfl,
    ⟨⟨rfl, by simpa using hY⟩, pred_m_freeClosed _ _ _ (fun _ => rfl) rfl⟩⟩

theorem lr_bound_sat_l {n d} (φ : UnarySchema n) (ρ : Env M d) (X Y : Term d) :
    Formula.satisfies ρ (lr_bound_m φ X Y) ↔ Lr_bound_d φ (X.eval ρ) (Y.eval ρ) := by
  rw [lr_bound_m, lr_all_sat_l]
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
    lr_shift_sat_l, lr_pred_sat_l]
  constructor
  · intro h η hη hx
    have hc x := lr_env_congr_l φ.body φ.freeClosed (η.push x)
      ((⟨η.bound, ρ.free⟩ : Env M n).push x) (fun _ => rfl)
    obtain ⟨x, hxY, hx⟩ := h η.bound hη (hx.elim fun x hx => ⟨x, (hc x).mp hx⟩)
    exact ⟨x, hxY, (hc x).mpr hx⟩
  · exact fun h p hp => h ⟨p, ρ.free⟩ hp

def Lr_fiber_d {n} (φ : UnarySchema n) (v : Fin n → M.Domain) (X f Y : M.Domain) : Prop :=
  ∀ ρ : Env M n, (∀ i, M.mem (ρ.bound i) X) → (∀ i, M.PairMember I (v i) (ρ.bound i) f) →
    (∃ x, φ.denote ρ x) → ∃ x, M.mem x Y ∧ φ.denote ρ x

def lr_fiber_m {n d} (φ : UnarySchema n) (v : Fin n → Term d) (X f Y : Term d) : Formula 1 d :=
  let a : Fin n → Term (d+n) := fun i => .bound ⟨i.val, by omega⟩
  let ψ := pred_m φ (fun i => (a i).weaken) .newest
  lr_all_m n X (.imp
    (lr_and_m (fun i => Formula.orderedPairMem 𝒞 (lr_shift_l n (v i)) (a i) (lr_shift_l n f)))
    (.imp (.existsE ψ) (Formula.existsMem (lr_shift_l n Y) ψ)))

@[simp] theorem lr_fiber_closed_l {n d} (φ : UnarySchema n) (v : Fin n → Term d) (X f Y : Term d)
    (hv : ∀ i, (v i).freeSupport = []) (hX : X.freeSupport = []) (hf : f.freeSupport = [])
    (hY : Y.freeSupport = []) : (lr_fiber_m (𝒞 := 𝒞) φ v X f Y).FreeClosed := by
  apply lr_all_closed_l _ _ _ hX
  simp -implicitDefEqProofs only [Definitional.Formula.FreeClosed, Formula.existsMem]
  refine ⟨lr_and_closed_l _ (fun i => ?_), ?_, ?_⟩
  · exact Formula.orderedPairMem_freeClosed _ _ _ _ (by simpa using hv i) rfl (by simpa using hf)
  · exact pred_m_freeClosed _ _ _ (fun _ => rfl) rfl
  · exact ⟨⟨rfl, by simpa using hY⟩, pred_m_freeClosed _ _ _ (fun _ => rfl) rfl⟩

theorem lr_fiber_sat_l {n d} (φ : UnarySchema n) (ρ : Env M d) (v : Fin n → Term d) (X f Y : Term d) :
    Formula.satisfies ρ (lr_fiber_m (𝒞 := 𝒞) φ v X f Y) ↔
      Lr_fiber_d I φ (fun i => (v i).eval ρ) (X.eval ρ) (f.eval ρ) (Y.eval ρ) := by
  have he : Formula.satisfies ρ (lr_fiber_m (𝒞 := 𝒞) φ v X f Y) ↔
      ∀ p : Fin n → M.Domain, (∀ i, M.mem (p i) (X.eval ρ)) →
        (∀ i, M.PairMember I ((v i).eval ρ) (p i) (f.eval ρ)) →
          (∃ x, φ.denote ⟨p, ρ.free⟩ x) → ∃ x, M.mem x (Y.eval ρ) ∧ φ.denote ⟨p, ρ.free⟩ x := by
    rw [lr_fiber_m, lr_all_sat_l]
    simp only [Formula.satisfies_imp_iff, lr_and_sat_l, Formula.satisfies_orderedPairMem_iff I,
      lr_shift_sat_l, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff]
    simp only [Definitional.Term.eval, lr_env_bound_l]
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro hp
    apply imp_congr_right
    intro hf
    exact imp_congr (exists_congr (lr_pred_sat_l φ ρ p))
      (exists_congr fun x => and_congr Iff.rfl (lr_pred_sat_l φ ρ p x))
  refine he.trans ⟨?_, fun h p hp hf => h ⟨p, ρ.free⟩ hp hf⟩
  intro h η hη hf hx
  have hc x := lr_env_congr_l φ.body φ.freeClosed (η.push x) ((⟨η.bound, ρ.free⟩ : Env M n).push x) (fun _ => rfl)
  obtain ⟨x, hxY, hx⟩ := h η.bound hη hf (hx.elim fun x hx => ⟨x, (hc x).mp hx⟩)
  exact ⟨x, hxY, (hc x).mpr hx⟩

end YesMetaZFC.SetTheory
