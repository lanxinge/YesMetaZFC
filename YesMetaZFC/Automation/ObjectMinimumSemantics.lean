import YesMetaZFC.Automation.ObjectDiagonalRelation
import YesMetaZFC.Automation.ObjectHornSemantics

/-! # 标准输入处最小输出的任意模型语义

把标准正负实例提升到任意对象输出；不要求内部轨迹标准，也不要求原图全域函数性。
-/
namespace YesMetaZFC.Automation.ObjectMinimumSemantics
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding
open RelationalTranslation NaturalRosserSemantics
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe x

def ternary_m (R : FormulaTemplate.Binary) : FormulaTemplate.Ternary where
  body := R (.fvar .here) (.fvar (.there (.there .here)))

@[simp] theorem ternary_apply_m (R : FormulaTemplate.Binary) {bound free : SetContext}
    (input parameter output : SetTerm bound free) : ternary_m R input parameter output = R input output := by
  simp [ternary_m, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    FormulaTemplate.apply_two_substituteMapped, Term.substituteMapped, VariableSubstitution.cons]

def minimum_m (D : Delta0CodeDomain) (R : FormulaTemplate.Binary) : FormulaTemplate.Binary where
  body := ObjectMinimumRelation.template D (ternary_m R) (.fvar .here) (numₘ(0)) (.fvar (.there .here))

@[simp] theorem minimum_apply_m (D : Delta0CodeDomain) (R : FormulaTemplate.Binary)
    {bound free : SetContext} (input output : SetTerm bound free) :
    minimum_m D R input output = ObjectMinimumRelation.template D (ternary_m R) input (numₘ(0)) output := by
  simp [minimum_m, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

variable {T : SetTheory} (S : ObjectDiagonal.Support T) (R : FormulaTemplate.Binary)
  (f : Nat → Nat)
  (hp : ∀ n, Derives T [] (R (numₘ(n)) (numₘ(f n) : Code)))
  (hn : ∀ n k, f n ≠ k → Derives T [] (¬ₘ R (numₘ(n)) (numₘ(k) : Code)))

include hp hn

theorem positive_m (n : Nat) :
    Derives T [] (minimum_m S.core.code_domain R (numₘ(n)) (numₘ(f n) : Code)) := by
  rw [minimum_apply_m]
  apply ObjectMinimumRelation.positive S.core (ternary_m R) _ _ _ (S.numeral_domain _)
    (by simpa only [ternary_apply_m] using hp n)
  intro k hk
  simpa only [ternary_apply_m] using hn n k (Nat.ne_of_gt hk)

theorem unique_m {free : SetContext} {Γ : Context signature free} (n : Nat) (point : SetOpenTerm free)
    (h : Derives T Γ (minimum_m S.core.code_domain R (numₘ(n)) point)) :
    Derives T Γ (point ≐ₘ numₘ(f n)) := by
  rw [minimum_apply_m] at h
  apply ObjectMinimumRelation.unique S.core (ternary_m R) _ _ point _ h
    (ObjectRelationBinder.closed_three (ternary_m R) _ _ _ (by simpa only [ternary_apply_m] using hp n))
  intro k _ hk
  exact ObjectRelationBinder.closed_three_negative (ternary_m R) _ _ _
    (by simpa only [ternary_apply_m] using hn n k (Ne.symm hk))

abbrev number_m (𝒩 : Structure.{0,0,0,x} signature) (n : Nat) :=
  (numₘ(n) : Code).eval (Env.empty : Env 𝒩 [] [])

/-- 输入为标准数码值时，最小图在任意赋值下恰好等价于预定输出。 -/
theorem satisfies_m {𝒩 : Structure.{0,0,0,x} signature} (h𝒩 : Theory.Models 𝒩 T)
    {bound free : SetContext} (env : Env 𝒩 bound free) (input output : SetTerm bound free)
    (n : Nat) (hi : input.eval env = number_m 𝒩 n) :
    (minimum_m S.core.code_domain R input output).satisfies env ↔
      output.eval env = number_m 𝒩 (f n) := by
  let G := minimum_m S.core.code_domain R
  rw [binary_satisfies, hi]
  constructor
  · intro h
    let point : SetOpenTerm [SetSort.set] := .fvar .here
    let premise := G (numₘ(n)) point
    have hpoint : point.eval ((Env.empty : Env 𝒩 [] []).pushFree (sort := SetSort.set) (output.eval env)) = output.eval env := rfl
    have proof : Derives T [premise] (point ≐ₘ numₘ(f n)) :=
      unique_m S R f hp hn n point (FirstOrder.Derives.assumption List.mem_cons_self)
    have hv := proof.sound h𝒩 ((Env.empty : Env 𝒩 [] []).pushFree (output.eval env))
      (by
        intro φ hφ
        obtain rfl := List.mem_singleton.mp hφ
        exact (binary_satisfies G _ _ _).mpr (by
          simpa only [G, ObjectHornSemantics.numeral_eval, hpoint] using h))
    simpa only [Formula.satisfies, ObjectHornSemantics.numeral_eval, hpoint] using hv
  · intro h
    rw [h]
    have hv := (positive_m S R f hp hn n).sound h𝒩 (Env.empty : Env 𝒩 [] [])
      (by intro φ hφ; cases hφ)
    exact (binary_satisfies G _ _ _).mp hv

end YesMetaZFC.Automation.ObjectMinimumSemantics
