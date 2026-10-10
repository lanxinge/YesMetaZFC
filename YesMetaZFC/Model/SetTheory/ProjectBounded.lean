import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Syntax
import YesMetaZFC.SetTheory.Definitional.Project

/-! # 成员满嵌入下原有界公式的绝对性

直接消费现有 Project 的 Δ₀ 分类。实际嵌入覆盖像集合的全部成员，所以有界
量词的见证可双向传递；不要求两边满足集合论公理，甚至不要求外延性。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

def image_env_l (e : M.Domain → N.Domain) {n} (ρ : Env M n) : Env N n :=
  ⟨fun i => e (ρ.bound i), fun i => e (ρ.free i)⟩

theorem image_env_push_l (e : M.Domain → N.Domain) {n} (ρ : Env M n) (x : M.Domain) :
    image_env_l e (ρ.push x) = (image_env_l e ρ).push (e x) := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩

theorem eval_image_env_l (e : M.Domain → N.Domain) {n} (ρ : Env M n) (t : Term n) :
    t.eval (image_env_l e ρ) = e (t.eval ρ) := by cases t <;> rfl

/-- 任意成员满单射保持并反射原 Δ₀ 公式，包含自由参数和非标准地模型。 -/
theorem delta0_image_l (e : M.Domain → N.Domain) (hi : Function.Injective e)
    (he : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {n} {φ : Formula 1 n} (hφ : φ.IsDelta0) (ρ : Env M n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l e ρ) φ := by
  have mem x a : M.mem x a ↔ N.mem (e x) (e a) :=
    ⟨fun h => (he a (e x)).mpr ⟨x, h, rfl⟩, fun h =>
      (he a (e x)).mp h |>.elim fun y hy => hi hy.2 ▸ hy.1⟩
  have sub a b : (∀ x, M.mem x a → M.mem x b) ↔ ∀ y, N.mem y (e a) → N.mem y (e b) := by
    constructor
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (he a y).mp hy
      exact (mem x b).mp (h x hx)
    · exact fun h x hx => (mem x b).mpr (h (e x) ((mem x a).mp hx))
  have ext a b : (∀ x, M.mem x a ↔ M.mem x b) ↔ ∀ y, N.mem y (e a) ↔ N.mem y (e b) := by
    constructor
    · intro h y
      exact ⟨(sub a b).mp (fun x => (h x).mp) y, (sub b a).mp (fun x => (h x).mpr) y⟩
    · intro h x
      exact ⟨(sub a b).mpr (fun y => (h y).mp) x, (sub b a).mpr (fun y => (h y).mpr) x⟩
  induction hφ with
  | falsum => simp only [Formula.satisfies_falsum_iff]
  | truth => simp only [Formula.satisfies_truth_iff]
  | mem s t => simp only [Formula.satisfies_mem_iff, eval_image_env_l]; exact mem _ _
  | atom r hr ts =>
    cases r with
    | extensionalEq => simp only [Formula.satisfies_atom_extensionalEq_iff, eval_image_env_l]; exact ext _ _
    | subset => simp only [Formula.satisfies_atom_subset_iff, eval_image_env_l]; exact sub _ _
  | neg h ih => simpa only [Formula.satisfies_neg_iff] using not_congr (ih ρ)
  | conj h k ih jh => simpa only [Formula.satisfies_conj_iff] using and_congr (ih ρ) (jh ρ)
  | disj h k ih jh => simpa only [Formula.satisfies_disj_iff] using or_congr (ih ρ) (jh ρ)
  | imp h k ih jh => simpa only [Formula.satisfies_imp_iff] using imp_congr (ih ρ) (jh ρ)
  | iff h k ih jh => simpa only [Formula.satisfies_iff_iff] using iff_congr (ih ρ) (jh ρ)
  | forallMem t h ih =>
    simp only [Formula.satisfies_forallMem_iff, eval_image_env_l]
    constructor
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (he (t.eval ρ) y).mp hy
      simpa only [image_env_push_l] using (ih (ρ.push x)).mp (h x hx)
    · intro h x hx
      apply (ih (ρ.push x)).mpr
      simpa only [image_env_push_l] using h (e x) ((mem x (t.eval ρ)).mp hx)
  | existsMem t h ih =>
    simp only [Formula.satisfies_existsMem_iff, eval_image_env_l]
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨e x, (mem x (t.eval ρ)).mp hx, by simpa only [image_env_push_l] using (ih (ρ.push x)).mp h⟩
    · rintro ⟨y, hy, h⟩
      obtain ⟨x, hx, rfl⟩ := (he (t.eval ρ) y).mp hy
      exact ⟨x, hx, (ih (ρ.push x)).mpr (by simpa only [image_env_push_l] using h)⟩

end YesMetaZFC.SetTheory
