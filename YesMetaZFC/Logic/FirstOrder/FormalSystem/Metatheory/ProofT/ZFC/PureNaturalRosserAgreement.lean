import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.RosserDomainBoundary
import YesMetaZFC.Model.ZFC.Pure.PureSourceCoding
import YesMetaZFC.Automation.NaturalRosserSemantics

/-! # 当前 Rosser 对应的内部自然数归约

新比较式的见证及其全部更小码都属于模型内部 ω，旧后继码域在此冗余。
本模块把句子对应归约为当前完整对象证明图在内部自然数码上的真值对应。
具体行检查及充分条件的填入见 `PureSourceLocalTests`、`PureRosserComplete`。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalRosserAgreement
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.NaturalRosserSemantics hiding mem
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

/-- 原完整对象图在给定码及当前结论 quotation 值上的语义。 -/
def Proof (𝒩 : Structure.{0,0,0,x} signature) (code : 𝒩.Carrier .set)
    (formula : SetSentence) : Prop :=
  ReducedProofPresentation.presentation.graph.condition.body.satisfies
    (templateEnv (.cons code (.cons ((IntrinsicQuotation.quote formula).eval
      (Env.empty : Env 𝒩 [] [])) .nil)))

/-- 当前完整图的根行值，保留内部自然数输入而不转换成宿主 Nat。 -/
def root (𝒩 : Structure.{0,0,0,x} signature) (code : 𝒩.Carrier .set)
    (formula : SetSentence) : 𝒩.Carrier .set :=
  (IntrinsicQuotation.node 1 [(.fvar .here : SetOpenTerm [.set,.set]), .fvar (.there .here)]).eval
    (templateEnv (.cons code (.cons ((IntrinsicQuotation.quote formula).eval
      (Env.empty : Env 𝒩 [] [])) .nil)))

theorem root_value (code : 𝒩.Carrier .set) (formula : SetSentence) :
    root 𝒩 code formula = PureSourceCoding.node 𝒩 1
      [code, (IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] [])] :=
  PureSourceCoding.node_eval _ _ _

theorem root_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {code : 𝒩.Carrier .set} (hCode : mem 𝒩 code (w 𝒩)) (formula : SetSentence) :
    mem 𝒩 (root 𝒩 code formula) (w 𝒩) := by
  rw [root_value]
  apply PureSourceCoding.node_natural h𝒩
  intro field hField
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
  rcases hField with rfl | rfl
  · exact hCode
  · exact PureSourceCoding.quotation_natural h𝒩 formula

/-- 实际根节点在全部内部自然数输入上保持，不再作为行归约的额外前提。 -/
theorem root_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {code : 𝒩.Carrier .set} (hCode : mem 𝒩 code (w 𝒩)) (formula : SetSentence) :
    root 𝒩 code formula = root (canonical h𝒩) code formula := by
  rw [root_value, root_value]
  have hFields : ∀ field, field ∈ ([code, (IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] [])]) →
      mem 𝒩 field (w 𝒩) := by
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl
    · exact hCode
    · exact PureSourceCoding.quotation_natural h𝒩 formula
  exact (PureSourceCoding.node_agrees h𝒩 1 hFields).trans
    (congrArg (fun conclusion => PureSourceCoding.node (canonical h𝒩) 1 [code, conclusion])
      (quotation_agrees h𝒩 formula))

/-- 同时检查 Horn 连边与具体节点条件的实际行正文。 -/
def Row (𝒩 : Structure.{0,0,0,x} signature) (row trace : 𝒩.Carrier .set) : Prop :=
  (_root_.YesMetaZFC.Automation.ObjectCheckedTrace.step
    _root_.YesMetaZFC.Automation.ObjectProofTree.rules ReducedProofPresentation.rowTest.condition).body.satisfies
      (templateEnv (.cons row (.cons trace .nil)))

theorem proof_trace (code : 𝒩.Carrier .set) (formula : SetSentence) :
    Proof 𝒩 code formula ↔
      ∃ trace, mem 𝒩 trace (PureSourceBounds.powerset 𝒩 (w 𝒩)) ∧
        mem 𝒩 (root 𝒩 code formula) trace ∧
        ∀ row, mem 𝒩 row trace → Row 𝒩 row trace := by
  unfold Proof
  rw [ReducedProofPresentation.graph_condition]
  exact _root_.YesMetaZFC.Automation.ObjectTrace.condition_satisfies _ _ _ _

/-- 比较式的证明码量词精确落在内部自然数及其初始段上。 -/
theorem comparison_naturals (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence) :
    (ReducedRosser.presentation.predicate_of formula).TrueIn 𝒩 ↔
      ∃ code, mem 𝒩 code (w 𝒩) ∧ Proof 𝒩 code formula ∧
        ∀ smaller, mem 𝒩 smaller code → ¬ Proof 𝒩 smaller (¬ₘ formula) := by
  change ((_root_.YesMetaZFC.Automation.NaturalProofPresentation.graph
    ReducedProofPresentation.presentation.graph).comparison intrinsic_zfc_core.code_domain
      (IntrinsicQuotation.quote formula) (IntrinsicQuotation.negation (IntrinsicQuotation.quote formula))).TrueIn 𝒩 ↔ _
  rw [← IntrinsicQuotation.quote_negation]
  apply natural_comparison_satisfies
  · intro code hCode
    exact (unary_satisfies successor_code_domain
      (templateEnv (.cons code .nil) : Env 𝒩 [] [.set]) (.fvar .here)).mp
        (RosserDomainBoundary.natural_in_domain h𝒩 hCode)
  · intro code smaller hCode hSmaller
    exact member_natural h𝒩 hCode hSmaller

/-- 仅要求同一个结论在所有内部自然数证明码上的对应。 -/
def ProofAgreement (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence) : Prop :=
  ∀ code, mem 𝒩 code (w 𝒩) → (Proof 𝒩 code formula ↔ Proof (canonical h𝒩) code formula)

/-- 根编码已对应，原完整图现在只剩候选轨迹中的局部行对应。 -/
theorem proof_agreement_of_rows (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence)
    (hRow : ∀ trace, mem 𝒩 trace (PureSourceBounds.powerset 𝒩 (w 𝒩)) →
      ∀ row, mem 𝒩 row trace → mem 𝒩 row (w 𝒩) →
        (Row 𝒩 row trace ↔ Row (canonical h𝒩) row trace)) :
    ProofAgreement h𝒩 formula := by
  intro code hCode
  unfold Proof
  rw [ReducedProofPresentation.graph_condition]
  exact PureSourceBounds.trace_agrees h𝒩 _ _ _ _ (root_agrees h𝒩 hCode formula) hRow

theorem comparison_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence)
    (hPositive : ProofAgreement h𝒩 formula) (hNegative : ProofAgreement h𝒩 (¬ₘ formula)) :
    (ReducedRosser.presentation.predicate_of formula).TrueIn 𝒩 ↔
      (ReducedRosser.presentation.predicate_of formula).TrueIn (canonical h𝒩) := by
  refine (comparison_naturals h𝒩 formula).trans
    (Iff.trans ?_ (comparison_naturals (PureZFCModels.models (PureZFCModels.reduct_models h𝒩)) formula).symm)
  change (∃ code, mem 𝒩 code (w 𝒩) ∧ Proof 𝒩 code formula ∧
    ∀ smaller, mem 𝒩 smaller code → ¬ Proof 𝒩 smaller (¬ₘ formula)) ↔
    (∃ code, mem 𝒩 code (w (canonical h𝒩)) ∧ Proof (canonical h𝒩) code formula ∧
    ∀ smaller, mem 𝒩 smaller code → ¬ Proof (canonical h𝒩) smaller (¬ₘ formula))
  rw [← omega_agrees h𝒩]
  constructor
  · rintro ⟨code, hCode, hProof, hSmaller⟩
    exact ⟨code, hCode, (hPositive code hCode).mp hProof, fun smaller hLess hProof =>
      hSmaller smaller hLess ((hNegative smaller (member_natural h𝒩 hCode hLess)).mpr hProof)⟩
  · rintro ⟨code, hCode, hProof, hSmaller⟩
    exact ⟨code, hCode, (hPositive code hCode).mpr hProof, fun smaller hLess hProof =>
      hSmaller smaller hLess ((hNegative smaller (member_natural h𝒩 hCode hLess)).mp hProof)⟩

/-- 对当前句子及其否定补齐自然数证明图对应，即可填入实际纯 Rosser 合同。 -/
theorem agreement_of_natural_proofs
    (hProof : ∀ (𝒩 : Structure.{0,0,0,0} signature) (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory),
      ProofAgreement h𝒩 ReducedRosser.sentence ∧ ProofAgreement h𝒩 (¬ₘ ReducedRosser.sentence)) :
    PureRosser.Agreement := by
  apply PureRosser.agreement_iff_comparison.mpr
  intro 𝒩 h𝒩
  exact (PureRosser.translate_truth_iff (PureZFCModels.reduct_models h𝒩)
    (ReducedRosser.presentation.predicate_of ReducedRosser.sentence)).trans
      (comparison_agrees h𝒩 ReducedRosser.sentence (hProof 𝒩 h𝒩).1 (hProof 𝒩 h𝒩).2).symm

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalRosserAgreement
