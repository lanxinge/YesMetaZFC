import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedNaturalProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicGraph
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectDiagonalFixedPoint

/-! # 原支撑理论上的具体 Rosser 不完备实例

公理及自然数码上的整树表示、有限比较和当前 quotation 的对角化均已给出具体实现。
唯一外部数学前提是原支撑理论的一致性；裸 ZFC 的支撑消去仍是独立任务。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedRosser
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 4096
attribute [local irreducible] ReducedNaturalProofPresentation.presentation

/-- 对角化消费已证明的算术、序列、幂集及后继链码域能力。 -/
def diagonalSupport : ObjectDiagonal.Support intrinsic_zfc_theory where
  certificate := intrinsic_zfc_certificate_core
  core := intrinsic_zfc_core
  sequences := intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
  power h := intrinsic_zfc_arithmetic_support.contains_function_predicate
    (relation_plane_theory_subset_function_predicate_theory
      (power_set_operator_theory_subset_relation_plane_theory h))
  infinity := intrinsic_zfc_arithmetic_support.contains_infinity
  numeral_domain := intrinsic_zfc_numeral_mem_code_domain

/-- 自然数证明图与已证明的 Rosser 有限比较装配。 -/
noncomputable def presentation : RosserPresentation intrinsic_zfc_theory intrinsic_zfc_theory where
  proof := ReducedNaturalProofPresentation.presentation
  core := intrinsic_zfc_core
  assembly := rosser_assembly_of_core intrinsic_zfc_core ReducedNaturalProofPresentation.presentation.graph
    intrinsic_zfc_numeral_mem_code_domain
  raw_subset h := h

/-- 自然数证明码使比较式在当前支撑语言中降为 Δ₀。 -/
theorem predicate_delta0 (formula : SetSentence) :
    Formula.IsDelta0 set_levy_bound (presentation.predicate_of formula) := by
  simpa only [RosserPresentation.predicate_of, RosserPresentation.predicate,
    rosser_predicate, RosserPresentation.graph, presentation,
    ReducedNaturalProofPresentation.presentation, NaturalProofPresentation.presentation] using
    NaturalProofPresentation.comparison_delta0 ReducedProofPresentation.presentation.graph
      intrinsic_zfc_core.code_domain (IntrinsicQuotation.quote formula)
      (IntrinsicQuotation.negation (IntrinsicQuotation.quote formula))

theorem predicate_exists_body (formula : SetSentence) :
    ∃ (body : SetFormula [SetSort.set] []), presentation.predicate_of formula = .existsE .set body :=
  ⟨_, rfl⟩

private def negativeComparison (G : Delta0ProofGraph) (D : Delta0CodeDomain)
    {bound free : SetContext} (code : SetTerm bound free) : SetFormula bound free :=
  ¬ₘ G.comparison D code (IntrinsicQuotation.negation code)

private theorem negativeComparison_substituteMapped (G : Delta0ProofGraph) (D : Delta0CodeDomain)
    {sb sf tb tf : SetContext} (code : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (negativeComparison G D code).substituteMapped bs fs =
      negativeComparison G D (code.substituteMapped bs fs) := by
  simp [negativeComparison, Delta0ProofGraph.comparison, Delta0ProofGraph.no_smaller,
    IntrinsicQuotation.negation, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftBound]

private def predicateTemplate (G : Delta0ProofGraph) (D : Delta0CodeDomain) : FormulaTemplate.Unary where
  body := negativeComparison G D (.fvar .here)

private theorem predicateTemplate_apply (G : Delta0ProofGraph) (D : Delta0CodeDomain)
    {bound free : SetContext} (code : SetTerm bound free) :
    predicateTemplate G D code = negativeComparison G D code := by
  simp [predicateTemplate, FormulaTemplate.apply_one, FormulaTemplate.instantiate,
    negativeComparison_substituteMapped, Term.substituteMapped, VariableSubstitution.cons]

/-- 与完整新证明图配套的具体 Rosser 句子。 -/
noncomputable def sentence : SetSentence :=
  ObjectDiagonal.fixedPoint intrinsic_zfc_core.code_domain
    (predicateTemplate presentation.graph intrinsic_zfc_core.code_domain)

/-- 通过通用固定点形状保留正文为不透明参数，供纯语言层级分析。 -/
theorem sentence_exists_body : ∃ (body : SetFormula [SetSort.set] []), sentence = .existsE .set body :=
  ⟨_, ObjectDiagonal.fixedPoint_shape _ _⟩

/-- 固定点等价已在原支撑理论内推导，不再作为待满足的假设。 -/
theorem fixed_point : Derives intrinsic_zfc_theory []
    (sentence ↔ₘ ¬ₘ presentation.predicate_of sentence) := by
  have h := ObjectDiagonal.fixedPoint_spec diagonalSupport
    (predicateTemplate presentation.graph intrinsic_zfc_core.code_domain)
  simpa only [predicateTemplate_apply, negativeComparison,
    RosserPresentation.predicate_of, RosserPresentation.predicate, rosser_predicate] using! h

/-- 当前固定点的 Δ₀ 代表；`fixed_point` 给出与原句子的普通推导等价。
分类包含 ω、幂集及编码函数，未断言纯隶属翻译或算术语言中的 Δ₀。 -/
noncomputable def delta0Sentence : SetSentence := ¬ₘ presentation.predicate_of sentence

theorem delta0Sentence_delta0 : Formula.IsDelta0 set_levy_bound delta0Sentence :=
  .neg (predicate_delta0 sentence)

/-- 只假定一致性，具体句子及其否定均不可在原支撑理论中推导。 -/
theorem independent
    (hConsistent : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    (¬ Derives intrinsic_zfc_theory [] sentence) ∧
      (¬ Derives intrinsic_zfc_theory [] (¬ₘ sentence)) :=
  rosser_incompleteness presentation fixed_point hConsistent

/-- 可证明等价将两侧不可证性传给支撑语言中的 Δ₀ 代表。 -/
theorem delta0Sentence_independent
    (hConsistent : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    (¬ Derives intrinsic_zfc_theory [] delta0Sentence) ∧
      (¬ Derives intrinsic_zfc_theory [] (¬ₘ delta0Sentence)) := by
  have hIndependent := independent hConsistent
  refine ⟨fun h => hIndependent.1 (Derives.iff_elim_right fixed_point h), ?_⟩
  intro h
  apply hIndependent.2
  apply Derives.neg_intro
  exact Derives.neg_elim
    (Derives.iff_elim_left fixed_point.context_weaken_cons
      (Derives.assumption List.mem_cons_self)) h.context_weaken_cons

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedRosser
