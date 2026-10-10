import YesMetaZFC.Logic.Arithmetic.PA.Interpretation
import YesMetaZFC.Model.Arithmetic.Z2.Comprehension

/-! # 任意 Z₂ 模型的 PA 数域约化

保留整个内部数域；没有标准性、外部有限性或幂集假设。
先对任意结构证明翻译的逐项／逐公式语义，再消费实际 PA 公理像推导。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2
open Logic FirstOrder Logic.Arithmetic.PA.Translation
set_option autoImplicit false
universe u
local notation "σ₀" => Logic.Arithmetic.signature_m
local notation "τ" => Logic.Arithmetic.Z2.signature_m

abbrev carrier_l (ℳ : Structure.{0, 0, 0, u} τ) (_ : Logic.Arithmetic.sort_m) := num_l ℳ

def values_m {ℳ : Structure.{0, 0, 0, u} τ} {Γ : SortContext σ₀} :
    Values (carrier_l ℳ) Γ → Values ℳ.Carrier (context_m Γ)
  | .nil => .nil
  | .cons n a => .cons n (values_m a)

abbrev reduct_m (ℳ : Structure.{0, 0, 0, u} τ) : Structure.{0, 0, 0, u} σ₀ where
  Carrier := carrier_l ℳ
  nonempty _ := ℳ.nonempty Logic.Arithmetic.Z2.sort_m.num
  funcInterp
    | .zero, a => ℳ.funcInterp .zero (values_m a)
    | .succ, a => ℳ.funcInterp .succ (values_m a)
    | .add, a => ℳ.funcInterp .add (values_m a)
    | .mul, a => ℳ.funcInterp .mul (values_m a)
  relInterp r := nomatch r

variable {ℳ : Structure.{0, 0, 0, u} τ}

def environment_m {Γ Δ : SortContext σ₀} (η : Env ℳ (context_m Γ) (context_m Δ)) :
    Env (reduct_m ℳ) Γ Δ where
  boundVal v := η.boundVal (variable_m v)
  freeVal v := η.freeVal (variable_m v)

theorem environment_bound_m {Γ Δ : SortContext σ₀} (s : Logic.Arithmetic.sort_m)
    (η : Env ℳ (context_m Γ) (context_m Δ)) (n : num_l ℳ) :
    environment_m (Γ := s :: Γ) (η.pushBound n) = (environment_m η).pushBound n := by
  apply Env.ext
  · intro t v; cases v <;> rfl
  · intro t v; rfl

theorem environment_empty_m : environment_m (ℳ := ℳ) (Γ := []) (Δ := []) Env.empty = Env.empty := by
  apply Env.ext <;> intro s v <;> cases v

mutual
theorem term_eval_m {Γ Δ : SortContext σ₀} (η : Env ℳ (context_m Γ) (context_m Δ))
    {s : Logic.Arithmetic.sort_m} (t : Term σ₀ Γ Δ s) :
    (term_m t).eval η = t.eval (environment_m η) := by
  match t with
  | .bvar v | .fvar v => rfl
  | .app f a =>
    have h := arguments_eval_m η a
    cases f <;> exact congrArg _ h

theorem arguments_eval_m {Γ Δ Θ : SortContext σ₀} (η : Env ℳ (context_m Γ) (context_m Δ))
    (a : Arguments σ₀ Γ Δ Θ) :
    (arguments_m a).eval η = values_m (a.eval (environment_m η)) := by
  match a with
  | .nil => rfl
  | .cons t a =>
    exact congr (congrArg (Values.cons (Carrier := ℳ.Carrier) (sort := Logic.Arithmetic.Z2.sort_m.num))
      (term_eval_m η t)) (arguments_eval_m η a)
end

theorem formula_sat_m {Γ Δ : SortContext σ₀} (η : Env ℳ (context_m Γ) (context_m Δ))
    (φ : Formula σ₀ Γ Δ) :
    Formula.satisfies η (formula_m φ) ↔ Formula.satisfies (environment_m η) φ := by
  match φ with
  | .falsum | .truth => exact Iff.rfl
  | .rel r _ => exact nomatch r
  | .equal s t => simp only [formula_m, Formula.satisfies, term_eval_m]
  | .neg φ => exact not_congr (formula_sat_m η φ)
  | .conj φ ψ => exact and_congr (formula_sat_m η φ) (formula_sat_m η ψ)
  | .disj φ ψ => exact or_congr (formula_sat_m η φ) (formula_sat_m η ψ)
  | .imp φ ψ => exact imp_congr (formula_sat_m η φ) (formula_sat_m η ψ)
  | .iff φ ψ => exact iff_congr (formula_sat_m η φ) (formula_sat_m η ψ)
  | .forallE s φ =>
    apply forall_congr'
    intro n
    exact (formula_sat_m (Γ := s :: Γ) (Δ := Δ) (η.pushBound n) φ).trans
      (Iff.of_eq (congrArg (fun υ => Formula.satisfies υ φ)
        (environment_bound_m (Γ := Γ) (Δ := Δ) s η n)))
  | .existsE s φ =>
    apply exists_congr
    intro n
    exact (formula_sat_m (Γ := s :: Γ) (Δ := Δ) (η.pushBound n) φ).trans
      (Iff.of_eq (congrArg (fun υ => Formula.satisfies υ φ)
        (environment_bound_m (Γ := Γ) (Δ := Δ) s η n)))

/-- Z₂ 的任意模型在原内部数域上满足 PA 的全部公理与归纳模式。 -/
theorem reduct_models_m (hZ₂ : Theory.Models ℳ Logic.Arithmetic.Z2.theory_m) :
    Theory.Models (reduct_m ℳ) Logic.Arithmetic.PA.theory_m := by
  intro φ h
  have h₁ := (show Derives Logic.Arithmetic.Z2.theory_m [] (formula_m φ) from
    axiom_derives_m h).sound hZ₂ Env.empty (by intro ψ hψ; cases hψ)
  have h₂ := (formula_sat_m Env.empty φ).mp h₁
  rwa [environment_empty_m] at h₂

end YesMetaZFC.Model.Arithmetic.Z2
