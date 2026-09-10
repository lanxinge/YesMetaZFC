import YesMetaZFC.Automation.ObjectNumeralSyntaxSpecifications
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceNumeralSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceInduction

/-! # 非标准自然数也具有唯一的当前 AST 数码

归纳性质是明确的对象公式。先证明它在原模型与最终纯扩张中一致，
再以内部归纳同时得到存在与唯一性；外部有限 numeral 只是其特例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem uniqueOutput_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (input : SetTerm bound free) :
    (ObjectNumeralSyntax.uniqueOutputCondition input).satisfies env ↔
      ∃ output, mem 𝒩 output (w 𝒩) ∧ Graph 𝒩 (input.eval env) output ∧
        ∀ other, mem 𝒩 other (w 𝒩) → Graph 𝒩 (input.eval env) other → other = output := by
  simp only [ObjectNumeralSyntax.uniqueOutputCondition, Formula.satisfies_existsFreeTop,
    Formula.satisfies_forallFreeTop, Formula.satisfies, satisfies, Term.eval_weakenFree, and_imp]
  rfl

theorem uniqueOutput_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) :
    (ObjectNumeralSyntax.uniqueOutputCondition (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectNumeralSyntax.uniqueOutputCondition (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [uniqueOutput_satisfies, uniqueOutput_satisfies]
  change (∃ output, mem 𝒩 output (w 𝒩) ∧ Graph 𝒩 input output ∧ _) ↔
    (∃ output, mem 𝒩 output (w (canonical h𝒩)) ∧ Graph (canonical h𝒩) input output ∧ _)
  apply exists_congr
  intro output
  rw [← omega_agrees h𝒩]
  apply and_congr_right
  intro hOutput
  apply and_congr (agrees h𝒩 hInput hOutput)
  apply forall_congr'
  intro other
  apply imp_congr_right
  intro hOther
  exact imp_congr (agrees h𝒩 hInput hOther) Iff.rfl

/-- 总性与唯一性覆盖模型内部整个 ω。 -/
theorem exists_unique (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) :
    ∃ output, mem 𝒩 output (w 𝒩) ∧ Graph 𝒩 input output ∧
      ∀ other, mem 𝒩 other (w 𝒩) → Graph 𝒩 input other → other = output := by
  have hAll := PureSourceInduction.induction h𝒩
    (ObjectNumeralSyntax.uniqueOutputCondition (.fvar .here)) .nil
    (fun _ h => uniqueOutput_agrees h𝒩 h) (by
      apply (uniqueOutput_satisfies _ _).mpr
      exact ⟨numeral 𝒩 ObjectNumeralSyntax.zeroCode, numeral_natural h𝒩 _, zero h𝒩,
        fun _ hOther hGraph => (zero_iff h𝒩 hOther).mp hGraph⟩) (by
      intro number hNumber hProperty
      obtain ⟨output, hOutput, hGraph, hUnique⟩ := (uniqueOutput_satisfies _ _).mp hProperty
      apply (uniqueOutput_satisfies _ _).mpr
      refine ⟨next 𝒩 output, next_natural h𝒩 hOutput, successor h𝒩 hNumber hOutput hGraph, ?_⟩
      intro other hOther hGraphOther
      obtain ⟨previous, hp, hPrevious, hEqual⟩ := (successor_iff h𝒩 hNumber hOther).mp hGraphOther
      exact hEqual.trans (congrArg (next 𝒩) (hUnique previous hp hPrevious)))
  exact (uniqueOutput_satisfies _ _).mp (hAll input hInput)

theorem total (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) :
    ∃ output, mem 𝒩 output (w 𝒩) ∧ Graph 𝒩 input output := by
  obtain ⟨output, hOutput, hGraph, _⟩ := exists_unique h𝒩 hInput
  exact ⟨output, hOutput, hGraph⟩

theorem functional (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input first second : 𝒩.Carrier .set}
    (hInput : mem 𝒩 input (w 𝒩)) (hFirst : mem 𝒩 first (w 𝒩)) (hSecond : mem 𝒩 second (w 𝒩))
    (hGraphFirst : Graph 𝒩 input first) (hGraphSecond : Graph 𝒩 input second) : first = second := by
  obtain ⟨_, _, _, hUnique⟩ := exists_unique h𝒩 hInput
  exact (hUnique first hFirst hGraphFirst).trans (hUnique second hSecond hGraphSecond).symm

theorem standard_iff (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (number : Nat)
    {output : 𝒩.Carrier .set} (hOutput : mem 𝒩 output (w 𝒩)) :
    Graph 𝒩 (numeral 𝒩 number) output ↔ output = numeral 𝒩 (ObjectNumeralSyntax.value number) := by
  constructor
  · intro hGraph
    exact functional h𝒩 (numeral_natural h𝒩 number) hOutput
      (numeral_natural h𝒩 (ObjectNumeralSyntax.value number)) hGraph (standard_graph h𝒩 number)
  · rintro rfl
    exact standard_graph h𝒩 number

/-- 实际源理论中的闭句推导，不将数码总性当作新的假设。 -/
theorem totalUnique_derives : Derives intrinsic_zfc_theory [] ObjectNumeralSyntax.totalUnique := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  simp only [ObjectNumeralSyntax.totalUnique, Formula.TrueIn, Formula.satisfies_forallFreeTop,
    Formula.satisfies]
  intro input hInput
  exact (uniqueOutput_satisfies _ _).mpr (exists_unique h𝒩 hInput)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
