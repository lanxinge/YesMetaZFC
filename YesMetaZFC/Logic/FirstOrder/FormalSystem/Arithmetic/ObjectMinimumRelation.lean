import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLeastWitness

/-! # 三元关系按最后一个参数选取最小输出

前两个参数可携带输入及替换项。正文由固定模板生成，实例化自动穿过量词；
标准输入处的正负推导足以给出最小输出的存在及对象唯一性。
-/
namespace YesMetaZFC.Automation.ObjectMinimumRelation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def condition (D : Delta0CodeDomain) (R : FormulaTemplate.Ternary)
    {bound free : SetContext} (input parameter output : SetTerm bound free) : SetFormula bound free :=
  D.condition output ∧ₘ (R input parameter output ∧ₘ
    set_levy_bound.boundedForall output
      (¬ₘ R (input.weakenBound SetSort.set) (parameter.weakenBound SetSort.set) (.bvar .here)))

@[simp] theorem condition_substituteMapped (D : Delta0CodeDomain) (R : FormulaTemplate.Ternary)
    {sb sf tb tf : SetContext} (input parameter output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition D R input parameter output).substituteMapped bs fs =
      condition D R (input.substituteMapped bs fs) (parameter.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftBound]

def template (D : Delta0CodeDomain) (R : FormulaTemplate.Ternary) : FormulaTemplate.Ternary where
  body := condition D R (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

@[simp] theorem template_apply (D : Delta0CodeDomain) (R : FormulaTemplate.Ternary)
    {bound free : SetContext} (input parameter output : SetTerm bound free) :
    template D R input parameter output = condition D R input parameter output := by
  simp [template, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

@[simp] theorem body_at (R : FormulaTemplate.Ternary) {free : SetContext}
    (input parameter output : SetOpenTerm free) :
    (R (input.weakenBound SetSort.set) (parameter.weakenBound SetSort.set)
      (.bvar .here)).instantiateTop output = R input parameter output := by
  rw [FormulaTemplate.apply_three_instantiateTop_arguments,
    Term.instantiateTop_weakenBound, Term.instantiateTop_weakenBound]
  rfl

theorem positive {T : SetTheory} (C : Core T) (R : FormulaTemplate.Ternary)
    {free : SetContext} {Γ : Context signature free}
    (input parameter : SetOpenTerm free) (value : Nat)
    (hDomain : Derives T Γ (C.code_domain.condition (numₘ(value))))
    (hValue : Derives T Γ (R input parameter (numₘ(value))))
    (hEarlier : ∀ index, index < value → Derives T Γ (¬ₘ R input parameter (numₘ(index)))) :
    Derives T Γ (template C.code_domain R input parameter (numₘ(value))) := by
  rw [template_apply, condition]
  apply FirstOrder.Derives.conj_intro hDomain
  apply FirstOrder.Derives.conj_intro hValue
  apply bounded_forall_numeral_intro C.toFiniteCore
  intro index hIndex
  rw [Formula.instantiateTop_neg, body_at R input parameter (numₘ(index))]
  exact hEarlier index hIndex

theorem unique {T : SetTheory} (C : Core T) (R : FormulaTemplate.Ternary)
    {free : SetContext} {Γ : Context signature free}
    (input parameter point : SetOpenTerm free) (value : Nat)
    (hMinimum : Derives T Γ (template C.code_domain R input parameter point))
    (hValue : Derives T Γ (R input parameter (numₘ(value))))
    (hWrong : ∀ index, index ≤ value → index ≠ value → Derives T Γ (¬ₘ R input parameter (numₘ(index)))) :
    Derives T Γ (point ≐ₘ numₘ(value)) := by
  rw [template_apply, condition] at hMinimum
  have hDomain := FirstOrder.Derives.conj_elim_left hMinimum
  have hRest := FirstOrder.Derives.conj_elim_right hMinimum
  refine ObjectLeastWitness.unique C
    (R (input.weakenBound SetSort.set) (parameter.weakenBound SetSort.set) (.bvar .here)) value point
    hDomain ?_ (FirstOrder.Derives.conj_elim_right hRest) ?_ ?_
  · rw [body_at R input parameter point]
    exact FirstOrder.Derives.conj_elim_left hRest
  · rw [body_at R input parameter (numₘ(value))]
    exact hValue
  · intro index hIndex hNe
    rw [body_at R input parameter (numₘ(index))]
    exact hWrong index hIndex hNe

end YesMetaZFC.Automation.ObjectMinimumRelation
