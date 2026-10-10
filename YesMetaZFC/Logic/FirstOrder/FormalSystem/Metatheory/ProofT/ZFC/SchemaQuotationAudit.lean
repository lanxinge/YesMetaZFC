import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.RepresentationCongruence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NatEncode

/-!
# 三类公理模式的 quotation 边界审计

本模块对任意参数数目和模式体证明：旧 quotation 合并模式实例及其 Hilbert 化，
新 quotation 严格区分二者。分离和收集还给出真实自然数证明码上的接受/拒绝冲突，
从而排除旧 quotation 下的统一正负表示。这里不宣称已完成模式的对象检查图。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaQuotationAudit
open Nonlogical.BasicSetTheory QuineEncoding
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false

private def isHilbert {bound free : SetContext} : SetFormula bound free → Bool
  | .rel _ _ | .equal _ _ => true
  | .neg body | .forallE _ body => isHilbert body
  | .imp left right => isHilbert left && isHilbert right
  | _ => false

private theorem hilbertize_isHilbert {bound free : SetContext} (formula : SetFormula bound free) :
    isHilbert (Formula.hilbertize SetSort.set formula) = true := by
  induction formula <;>
    simp_all [isHilbert, Formula.hilbertize, Formula.hilbert_truth,
      Formula.hilbert_falsum, Formula.hilbert_conj, Formula.hilbert_iff]

private theorem forallClosure_isHilbert {n : Nat}
    (body : Project.Formula 1 n) (h : body.FreeClosed) :
    isHilbert (project_sentence (Project.Sentence.forallClosure body h)) =
      isHilbert (project_formula body h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hClosed : (_root_.YesMetaZFC.SetTheory.Definitional.Formula.forallE body).FreeClosed := by
        simpa [Formula.FreeClosed] using h
      have hStep : isHilbert (project_formula (.forallE body) hClosed) =
          isHilbert (project_formula body h) := by
        conv => lhs; arg 1; rw [project_formula.eq_def]
        rfl
      exact (ih (.forallE body) hClosed).trans hStep


private theorem ne_hilbertize_of_false (formula : SetSentence)
    (h : isHilbert formula = false) :
    formula ≠ Formula.hilbertize SetSort.set formula := by
  intro hEq
  have hCore := hilbertize_isHilbert formula
  rw [← hEq, h] at hCore
  contradiction

/-- 分离实例含原生存在量词，因而不等于其 Hilbert 化。 -/
theorem separation_ne_hilbertize {n : Nat} (schema : Project.UnarySchema n) :
    project_sentence (_root_.YesMetaZFC.SetTheory.Axioms.Schema.separation schema) ≠
      Formula.hilbertize SetSort.set
        (project_sentence (_root_.YesMetaZFC.SetTheory.Axioms.Schema.separation schema)) := by
  apply ne_hilbertize_of_false
  exact (forallClosure_isHilbert
    (_root_.YesMetaZFC.SetTheory.Axioms.Schema.separationCore schema) (by
      simp [_root_.YesMetaZFC.SetTheory.Axioms.Schema.separationCore,
        Formula.FreeClosed, schema.freeClosed])).trans (by
      simp only [_root_.YesMetaZFC.SetTheory.Axioms.Schema.separationCore,
        project_formula, isHilbert])

/-- 收集实例的像集存在量词保留在当前内在 AST 中。 -/
theorem collection_ne_hilbertize {n : Nat} (schema : Project.BinarySchema n) :
    project_sentence (_root_.YesMetaZFC.SetTheory.Axioms.Schema.collection schema) ≠
      Formula.hilbertize SetSort.set
        (project_sentence (_root_.YesMetaZFC.SetTheory.Axioms.Schema.collection schema)) := by
  apply ne_hilbertize_of_false
  exact (forallClosure_isHilbert
    (_root_.YesMetaZFC.SetTheory.Axioms.Schema.collectionCore schema) (by
      simp [_root_.YesMetaZFC.SetTheory.Axioms.Schema.collectionCore, Formula.FreeClosed,
        Project.Formula.forallMem, Project.Formula.existsMem,
        Project.Term.newest, schema.freeClosed])).trans (by
      simp only [_root_.YesMetaZFC.SetTheory.Axioms.Schema.collectionCore, project_formula, isHilbert, Bool.and_false])

/-- Jech 风格替换也有同一旧 quotation 冲突；此声明不把替换新增为 ZFC 原始公理。 -/
theorem replacement_ne_hilbertize {n : Nat} (schema : Project.BinarySchema n) :
    project_sentence (_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacement schema) ≠
      Formula.hilbertize SetSort.set
        (project_sentence (_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacement schema)) := by
  apply ne_hilbertize_of_false
  exact (forallClosure_isHilbert
    (_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacementCore schema) (by
      simp [_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacementCore, Formula.FreeClosed,
        Project.Formula.existsMem,
        Project.Term.newest, schema.freeClosed])).trans (by
      simp only [_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacementCore, project_formula, isHilbert, Bool.and_false])

/-- 新 quotation 在所有上述碰撞对上均保持严格区分。 -/
theorem intrinsic_quote_ne_hilbertize (formula : SetSentence)
    (h : formula ≠ Formula.hilbertize SetSort.set formula) :
    IntrinsicQuotation.quote formula ≠
      IntrinsicQuotation.quote (Formula.hilbertize SetSort.set formula) :=
  fun hQuote => h (IntrinsicQuotation.quote_injective hQuote)

def axiomCertificate (certificate : ZFCAxiomCertificate) : IntrinsicClosedProofCertificate :=
  ⟨_, ProofCertificate.theory_axiom (axioms := intrinsic_zfc_axiom_presentation)
    (Sum.inl certificate)⟩

/-- 真实公理证明码接受其原始结论，却拒绝不同 AST 的 Hilbert 化结论。 -/
theorem axiom_check_collision (certificate : ZFCAxiomCertificate)
    (hDifferent : (axiomCertificate certificate).conclusion ≠
      Formula.hilbertize SetSort.set (axiomCertificate certificate).conclusion) :
    let code := intrinsic_zfc_nat_encode (axiomCertificate certificate)
    let formula := (axiomCertificate certificate).conclusion
    intrinsic_zfc_nat_check code formula = true ∧
      intrinsic_zfc_nat_check code (Formula.hilbertize SetSort.set formula) = false := by
  dsimp only
  constructor
  · exact intrinsic_zfc_nat_check_encode _
  · apply Bool.eq_false_iff.mpr
    intro hChecked
    obtain ⟨decoded, hDecoded, hConclusion⟩ :=
      (intrinsic_zfc_nat_check_eq_true_iff _ _).mp hChecked
    rw [intrinsic_zfc_nat_decode_encode] at hDecoded
    cases Option.some.inj hDecoded
    exact hDifferent hConclusion

theorem separation_check_collision {n : Nat} (schema : Project.UnarySchema n) :
    let certificate := axiomCertificate (.separation schema)
    let code := intrinsic_zfc_nat_encode certificate
    intrinsic_zfc_nat_check code certificate.conclusion = true ∧
      intrinsic_zfc_nat_check code (Formula.hilbertize SetSort.set certificate.conclusion) = false :=
  axiom_check_collision (.separation schema) (separation_ne_hilbertize schema)

theorem collection_check_collision {n : Nat} (schema : Project.BinarySchema n) :
    let certificate := axiomCertificate (.collection schema)
    let code := intrinsic_zfc_nat_encode certificate
    intrinsic_zfc_nat_check code certificate.conclusion = true ∧
      intrinsic_zfc_nat_check code (Formula.hilbertize SetSort.set certificate.conclusion) = false :=
  axiom_check_collision (.collection schema) (collection_ne_hilbertize schema)

/-- 这是真正的不可表示结论，不以任何尚未完成的对象图为假设。 -/
theorem no_legacy_nat_representation
    (hConsistent : Derives.Consistent intrinsic_zfc_theory ([] : Context signature []))
    (condition : FormulaTemplate.Binary)
    (positive : ∀ n φ, intrinsic_zfc_nat_check n φ = true →
      Derives intrinsic_zfc_theory [] (condition (finite_numeral_term n) (QuineEncoding.quote φ)))
    (negative : ∀ n φ, intrinsic_zfc_nat_check n φ = false →
      Derives intrinsic_zfc_theory [] (.neg (condition (finite_numeral_term n) (QuineEncoding.quote φ)))) :
    False := by
  -- 先保留模式为变量，避免类型检查提前计算具体证明码的巨大自然数。
  suffices ∀ schema : Project.UnarySchema 0, False from this ⟨.truth, trivial⟩
  intro schema
  let certificate := axiomCertificate (.separation schema)
  let code := intrinsic_zfc_nat_encode certificate
  have hPair := separation_check_collision schema
  change intrinsic_zfc_nat_check code certificate.conclusion = true ∧
    intrinsic_zfc_nat_check code (Formula.hilbertize SetSort.set certificate.conclusion) = false at hPair
  generalize hFormula : certificate.conclusion = formula at hPair
  exact inconsistent_of_quote_collision (T := intrinsic_zfc_theory) (code := code)
    (left := formula) (right := Formula.hilbertize SetSort.set formula)
    condition (quote_hilbertize formula).symm
    (positive code formula hPair.1)
    (negative code (Formula.hilbertize SetSort.set formula) hPair.2) hConsistent

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaQuotationAudit
