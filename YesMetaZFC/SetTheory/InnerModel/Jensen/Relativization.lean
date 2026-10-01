import YesMetaZFC.SetTheory.InnerModel.Jensen.Model

/-! # 原公式在 J 中的解释与成员归纳

量词逐项限制到已定义的 J 类；定义原子通过成员满嵌入保持。
将内部归纳前提翻译回背景的实际公式，得到 J 自身的 KPi 实例。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def l_rel_m : {n : Nat} → Formula 1 n → Formula 1 n
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem s t => .mem s t
  | _, .atom r hr ts => .atom r hr ts
  | _, .neg φ => .neg (l_rel_m φ)
  | _, .conj φ ψ => .conj (l_rel_m φ) (l_rel_m ψ)
  | _, .disj φ ψ => .disj (l_rel_m φ) (l_rel_m ψ)
  | _, .imp φ ψ => .imp (l_rel_m φ) (l_rel_m ψ)
  | _, .iff φ ψ => .iff (l_rel_m φ) (l_rel_m ψ)
  | _, .forallE φ => .forallE (.imp (l_m .newest) (l_rel_m φ))
  | _, .existsE φ => .existsE (.conj (l_m .newest) (l_rel_m φ))

@[simp] theorem l_rel_closed_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) : (l_rel_m φ).FreeClosed := by
  induction φ <;> simp_all -implicitDefEqProofs [l_rel_m, Definitional.Formula.FreeClosed]

theorem l_rel_sat_l (hM : M.Models KPi) {n} (φ : Formula 1 n) (ρ : Env (l_model_l hM) n) :
    Formula.satisfies ρ φ ↔
      Formula.satisfies (image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ) (l_rel_m φ) := by
  induction φ with
  | falsum => simp only [l_rel_m, Formula.satisfies_falsum_iff]
  | truth => simp only [l_rel_m, Formula.satisfies_truth_iff]
  | mem s t => exact l_model_delta_l hM (.mem s t) ρ
  | atom r hr ts => exact l_model_delta_l hM (.atom r hr ts) ρ
  | neg φ ih => simpa only [l_rel_m, Formula.satisfies_neg_iff] using not_congr (ih ρ)
  | conj φ ψ ih jh => simpa only [l_rel_m, Formula.satisfies_conj_iff] using and_congr (ih ρ) (jh ρ)
  | disj φ ψ ih jh => simpa only [l_rel_m, Formula.satisfies_disj_iff] using or_congr (ih ρ) (jh ρ)
  | imp φ ψ ih jh => simpa only [l_rel_m, Formula.satisfies_imp_iff] using imp_congr (ih ρ) (jh ρ)
  | iff φ ψ ih jh => simpa only [l_rel_m, Formula.satisfies_iff_iff] using iff_congr (ih ρ) (jh ρ)
  | forallE φ ih =>
    simp only [l_rel_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      l_sat_l (KPi.models_iff_l.mp hM).1, Definitional.Term.eval_newest]
    have tr (x : (l_model_l hM).Domain) : Formula.satisfies (ρ.push x) φ ↔
        Formula.satisfies ((image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ).push x.val) (l_rel_m φ) := by
      have h := ih (ρ.push x)
      rw [image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ρ x] at h
      exact h
    exact ⟨fun h x hx => (tr ⟨x, hx⟩).mp (h ⟨x, hx⟩), fun h x => (tr x).mpr (h x.val x.property)⟩
  | existsE φ ih =>
    simp only [l_rel_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      l_sat_l (KPi.models_iff_l.mp hM).1, Definitional.Term.eval_newest]
    have tr (x : (l_model_l hM).Domain) : Formula.satisfies (ρ.push x) φ ↔
        Formula.satisfies ((image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ).push x.val) (l_rel_m φ) := by
      have h := ih (ρ.push x)
      rw [image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ρ x] at h
      exact h
    exact ⟨fun ⟨x, hx⟩ => ⟨x.val, x.property, (tr x).mp hx⟩,
      fun ⟨x, hx, hp⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mpr hp⟩⟩

theorem l_model_kpi_l (hM : M.Models KPi) : (l_model_l hM).Models KPi := by
  refine KPi.models_iff_l.mpr ⟨l_model_kp_l hM, ?_⟩
  intro n φ ρ step x
  let η := image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ
  let ψ : UnarySchema n := {
    body := .imp (l_m .newest) (l_rel_m φ.body)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, φ.freeClosed] }
  have hψ a : ψ.denote η a ↔ (L_d a → Formula.satisfies (η.push a) (l_rel_m φ.body)) := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_imp_iff,
      l_sat_l (KPi.models_iff_l.mp hM).1, Definitional.Term.eval_newest]
  have tr (z : (l_model_l hM).Domain) : φ.denote ρ z ↔ Formula.satisfies (η.push z.val) (l_rel_m φ.body) := by
    have h := l_rel_sat_l hM φ.body (ρ.push z)
    rw [image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ρ z] at h
    exact h
  apply (tr x).mpr
  apply (hψ x.val).mp ((KPi.models_iff_l.mp hM).2 ψ η ?_ x.val) x.property
  intro a ih
  apply (hψ a).mpr
  intro ha
  let z : (l_model_l hM).Domain := ⟨a, ha⟩
  exact (tr z).mp (step z (fun y hy => (tr y).mpr ((hψ y.val).mp (ih y.val hy) y.property)))

end YesMetaZFC.SetTheory.InnerModel
