import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofHeaders
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceProjection
import YesMetaZFC.Automation.ObjectProofNodeSemantics

/-! # 当前证明节点的内部局部检查构造 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofLocalConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceHorn PureSourceHornConstruction PureSourceProjection PureSourceTraceComposition ReducedProofHeaders
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
open NaturalRosserSemantics hiding mem
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

private theorem containsPower {φ : SetSentence} (h : power_set_operator_theory φ) : intrinsic_zfc_theory φ :=
  intrinsic_zfc_arithmetic_support.contains_function_predicate
    (relation_plane_theory_subset_function_predicate_theory
      (power_set_operator_theory_subset_relation_plane_theory h))

def queryTest : ObjectProofNode.Kind → ObjectCheckedTrace.LocalTest intrinsic_zfc_theory :=
  ObjectProofNode.queryTest intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor containsPower
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedAxiomNumber.localTest

def Holds (condition : FormulaTemplate.Unary) (value : 𝒩.Carrier .set) : Prop :=
  condition.body.satisfies (templateEnv (.cons value .nil))

theorem syntax_satisfies (row : 𝒩.Carrier .set) :
    Holds (queryTest .syntax).condition row ↔ Witness (ObjectHorn.step ObjectFormulaSyntax.rules) row :=
  ObjectTrace.condition_satisfies _ (templateEnv (.cons row .nil) : Env 𝒩 [] [.set]) ωₘ (.fvar .here)

theorem transform_satisfies (row : 𝒩.Carrier .set) :
    Holds (queryTest .transform).condition row ↔ Witness (ObjectHorn.step ObjectSyntaxTransform.rules) row :=
  ObjectTrace.condition_satisfies _ (templateEnv (.cons row .nil) : Env 𝒩 [] [.set]) ωₘ (.fvar .here)

/-- 当前六类节点的局部语义，固定原支撑实例供所有内部构造复用。 -/
theorem node_local_satisfies (row : 𝒩.Carrier .set) :
    Holds ReducedProofPresentation.nodeTest.condition row ↔
      ∃ shape ∈ ObjectProofNode.shapes, ∃ values : Fin shape.arity → 𝒩.Carrier .set,
        (∀ i, mem 𝒩 (values i) (suc 𝒩 row)) ∧ row = exprValue 𝒩 values shape.head ∧
        ∀ query ∈ shape.queries, Holds (queryTest query.1).condition (exprValue 𝒩 values query.2) :=
  ObjectProofNode.localTest_satisfies intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    intrinsic_zfc_arithmetic_support.contains_successor containsPower
    intrinsic_zfc_arithmetic_support.contains_infinity ReducedAxiomNumber.localTest row

def quoteValue (𝒩 : Structure.{0,0,0,x} signature) (formula : SetSentence) : 𝒩.Carrier .set :=
  (IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] [])

theorem quote_numeral (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence) :
    quoteValue 𝒩 formula = numeral 𝒩 (IntrinsicQuotation.value formula) :=
  (IntrinsicQuotation.quote_evaluate intrinsic_zfc_certificate_core formula).semantically_entails 𝒩 h𝒩

theorem quote_imp (φ ψ : SetSentence) :
    quoteValue 𝒩 (Formula.imp φ ψ) = node 𝒩 7 [quoteValue 𝒩 φ, quoteValue 𝒩 ψ] :=
  node_eval (Env.empty : Env 𝒩 [] []) 7 [IntrinsicQuotation.quote φ, IntrinsicQuotation.quote ψ]

theorem node_numerals (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (tag : Nat) (fields : List Nat) :
    node 𝒩 tag (fields.map (numeral 𝒩)) = numeral 𝒩 (ObjectHorn.nodeValue tag fields) :=
  PureSourceHornConstruction.node_numerals h𝒩 tag fields

theorem test_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (test : ObjectCheckedTrace.LocalTest intrinsic_zfc_theory) (number : Nat)
    (hChecked : test.checked number = true) : Holds test.condition (numeral 𝒩 number) :=
  (unary_satisfies test.condition (Env.empty : Env 𝒩 [] []) (numₘ(number))).mp
    ((test.positive number hChecked).semantically_entails 𝒩 h𝒩)

theorem syntax_query (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence) :
    Holds (queryTest .syntax).condition (node 𝒩 4 [z 𝒩, z 𝒩, quoteValue 𝒩 formula]) := by
  rw [quote_numeral h𝒩 formula]
  have hNode := node_numerals h𝒩 4 [0,0,IntrinsicQuotation.value formula]
  change node 𝒩 4 [z 𝒩,z 𝒩,numeral 𝒩 (IntrinsicQuotation.value formula)] = _ at hNode
  rw [hNode]
  exact test_positive h𝒩 (queryTest .syntax) _ (ObjectFormulaSyntax.checked_encode formula)

theorem projection_of_witness {row : 𝒩.Carrier .set}
    (h : Witness (ObjectHorn.step ObjectProjection.rules) row) :
    Holds (queryTest .projection).condition row :=
  (ObjectTrace.condition_satisfies _ (templateEnv (.cons row .nil) : Env 𝒩 [] [.set])
    ωₘ (.fvar .here)).mpr h

theorem header_projection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {code conclusion : 𝒩.Carrier .set} (hConclusion : mem 𝒩 conclusion (w 𝒩))
    (hHeader : Header code conclusion) :
    Holds (queryTest .projection).condition (node 𝒩 2 [code, z 𝒩, z 𝒩]) ∧
      Holds (queryTest .projection).condition (node 𝒩 2 [code, numeral 𝒩 1, conclusion]) := by
  obtain ⟨tag, tail, hTail, rfl⟩ := hHeader
  have hFields : ∀ value ∈ z 𝒩 :: conclusion :: tail, mem 𝒩 value (w 𝒩) := by
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (omega_closed h𝒩).1
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hConclusion
    · exact hTail value hv
  exact ⟨projection_of_witness (field_node h𝒩 tag _ hFields 0 (by simp)),
    projection_of_witness (field_node h𝒩 tag _ hFields 1 (by simp))⟩

/-- MP 节点的结论参数允许任意内部公式码。 -/
def mpCodeOf (𝒩 : Structure.{0,0,0,x} signature) (premise implication conclusion : 𝒩.Carrier .set) : 𝒩.Carrier .set :=
  node 𝒩 2 [z 𝒩, conclusion, premise, implication]

def mpCode (𝒩 : Structure.{0,0,0,x} signature) (premise implication : 𝒩.Carrier .set)
    (conclusion : SetSentence) : 𝒩.Carrier .set :=
  mpCodeOf 𝒩 premise implication (quoteValue 𝒩 conclusion)

theorem mp_natural_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {premise implication conclusion : 𝒩.Carrier .set} (hp : mem 𝒩 premise (w 𝒩))
    (hi : mem 𝒩 implication (w 𝒩)) (hc : mem 𝒩 conclusion (w 𝒩)) :
    mem 𝒩 (mpCodeOf 𝒩 premise implication conclusion) (w 𝒩) :=
  node_natural h𝒩 2 (by simp [(omega_closed h𝒩).1, hc, hp, hi])

theorem mp_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {premise implication : 𝒩.Carrier .set} (hp : mem 𝒩 premise (w 𝒩))
    (hi : mem 𝒩 implication (w 𝒩)) (ψ : SetSentence) : mem 𝒩 (mpCode 𝒩 premise implication ψ) (w 𝒩) :=
  mp_natural_code h𝒩 hp hi (quotation_natural h𝒩 ψ)

/-- 六个局部查询均由真实语法或投影轨迹满足。 -/
theorem mp_local_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {φ ψ : 𝒩.Carrier .set} (hφ : mem 𝒩 φ (w 𝒩)) (hψ : mem 𝒩 ψ (w 𝒩))
    (hSyntaxφ : Holds (queryTest .syntax).condition (node 𝒩 4 [z 𝒩, z 𝒩, φ]))
    (hSyntaxψ : Holds (queryTest .syntax).condition (node 𝒩 4 [z 𝒩, z 𝒩, ψ]))
    {premise implication : 𝒩.Carrier .set} (hp : mem 𝒩 premise (w 𝒩))
    (hi : mem 𝒩 implication (w 𝒩))
    (hPremise : Header premise φ)
    (hImplication : Header implication (node 𝒩 7 [φ, ψ]))
    (hPremiseBound : mem 𝒩 φ (suc 𝒩 premise)) :
    Holds ReducedProofPresentation.nodeTest.condition (mpCodeOf 𝒩 premise implication ψ) := by
  let values : Fin 5 → 𝒩.Carrier .set :=
    fun i => [z 𝒩, ψ, premise, implication, φ][i]
  have hValues : ∀ i, mem 𝒩 (values i) (w 𝒩) := values_natural
    (fields := [z 𝒩, ψ, premise, implication, φ]) (by
      intro value hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact (omega_closed h𝒩).1
      · exact hψ
      · exact hp
      · exact hi
      · exact hφ)
  have hHead : mpCodeOf 𝒩 premise implication ψ = exprValue 𝒩 values ObjectProofNode.mpShape.head := by
    simp [mpCodeOf, values, expr_node, exprValue]
    rfl
  have hBound : ∀ i, mem 𝒩 (values i) (suc 𝒩 (mpCodeOf 𝒩 premise implication ψ)) := by
    intro i
    by_cases hMissing : i = 4
    · subst i
      have hChild := expr_bound h𝒩 hValues ObjectProofNode.mpShape.head
        (index := 2) (by decide +kernel)
      rw [← hHead] at hChild
      exact bound_trans h𝒩 (mp_natural_code h𝒩 hp hi hψ) hPremiseBound hChild
    · rw [hHead]
      exact expr_bound h𝒩 hValues ObjectProofNode.mpShape.head
        ((by decide +kernel : ∀ j : Fin 5, j ≠ 4 → j ∈ ObjectProofNode.mpShape.head.variables) i hMissing)
  have hpQueries := header_projection h𝒩 (hφ) hPremise
  have hiQueries := header_projection h𝒩 (node_natural h𝒩 7 (by simp [hφ, hψ])) hImplication
  apply (node_local_satisfies _).mpr
  refine ⟨ObjectProofNode.mpShape, (by simp [ObjectProofNode.shapes]), values, hBound, hHead, ?_⟩
  intro query hQuery
  simp only [ObjectProofNode.mpShape, List.mem_cons, List.not_mem_nil, or_false] at hQuery
  rcases hQuery with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [values, expr_node, exprValue] using! hSyntaxψ
  · simpa [values, expr_node, exprValue] using! hSyntaxφ
  · simpa [values, expr_node, exprValue] using! hpQueries.1
  · simpa [values, expr_node, exprValue] using! hpQueries.2
  · simpa [values, expr_node, exprValue] using! hiQueries.1
  · simpa [values, expr_node, exprValue] using! hiQueries.2

/-- 标准闭句的旧入口通过通用内部公式码构造实现。 -/
theorem mp_local (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (φ ψ : SetSentence)
    {premise implication : 𝒩.Carrier .set} (hp : mem 𝒩 premise (w 𝒩))
    (hi : mem 𝒩 implication (w 𝒩))
    (hPremise : Header premise (quoteValue 𝒩 φ))
    (hImplication : Header implication (quoteValue 𝒩 (Formula.imp φ ψ)))
    (hPremiseBound : mem 𝒩 (quoteValue 𝒩 φ) (suc 𝒩 premise)) :
    Holds ReducedProofPresentation.nodeTest.condition (mpCode 𝒩 premise implication ψ) := by
  rw [quote_imp] at hImplication
  exact mp_local_code h𝒩 (quotation_natural h𝒩 φ) (quotation_natural h𝒩 ψ)
    (syntax_query h𝒩 φ) (syntax_query h𝒩 ψ) hp hi hPremise hImplication hPremiseBound

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofLocalConstruction
