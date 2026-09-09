import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredCertificateCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredWitness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofTerminal
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofSupport

/-!
# ProofT 内在 checked 证明码见证

本模块消费内在总证明码 body，并把其中的序列条件、坐标界和配对等式直接交给
结构化序列见证接口。这里不重新打开任何具名 free binder，也不复制旧的
`Admissible`、`freeSupport` 或 fresh 编号证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicCheckedWitness

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open StructuredCertificateCondition

set_option autoImplicit false

/-- 总证明码 body 的直接结构见证。 -/
theorem witness_sequences_of_code_body
    {T : SetTheory}
    (P : IntrinsicProofSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (number : Nat)
    (sequence certificates formulaCode certificateCode : SetOpenTerm free)
    (hBody :
      Γ ⊢ₘ[T]
        (((verifier.sequence_condition sequence certificates ∧ₘ
            proof_sequence_code_condition sequence formulaCode) ∧ₘ
          nat_sequence_code_condition certificates certificateCode) ∧ₘ
        ((proof_code_component_bound
            (numₘ(number)) formulaCode ∧ₘ
          proof_code_component_bound
            (numₘ(number)) certificateCode) ∧ₘ
          ((numₘ(number) ≐ₘ
              godel_pairₘ(formulaCode, certificateCode)) ∧ₘ
            proof_sequence_terminal_condition
              sequence (numₘ(number)))))) :
    Γ ⊢ₘ[T]
      (sequence ≐ₘ
          proof_sequence_graph_term
            (proof_sequence_decode (godel_unpair_value number).1)) ∧ₘ
        (certificates ≐ₘ
          nat_sequence_graph_term
            (nat_sequence_decode (godel_unpair_value number).2)) := by
  have hSequenceAndProof :=
    FirstOrder.Derives.conj_elim_left
      (FirstOrder.Derives.conj_elim_left hBody)
  have hProofCondition :=
    FirstOrder.Derives.conj_elim_right hSequenceAndProof
  have hCertificateCondition :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_left hBody)
  have hBounds :=
    FirstOrder.Derives.conj_elim_left
      (FirstOrder.Derives.conj_elim_right hBody)
  have hFormulaBound :=
    FirstOrder.Derives.conj_elim_left hBounds
  have hCertificateBound :=
    FirstOrder.Derives.conj_elim_right hBounds
  have hPairAndTerminal :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_right hBody)
  have hPair :=
    FirstOrder.Derives.conj_elim_left hPairAndTerminal
  exact StructuredWitness.witness_sequences
    P
    number sequence certificates formulaCode certificateCode
    hProofCondition hCertificateCondition
    hFormulaBound hCertificateBound hPair

/-! ## 总码外层见证消去 -/

/--
总证明码条件的外层有界存在消去。

该接口只展开总码的第一层序列见证；其余证书见证仍留在 case 分支中，避免下游
重复对齐 `code_condition` 的依赖上下文。`result` 不得依赖新引入的见证变量，
因此正好符合 Hilbert 存在消去的最弱调用形态。
-/
theorem code_condition_outer_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (proofCode conclusion : SetOpenTerm free)
    (result : SetOpenFormula free)
    (hCode : Γ ⊢ₘ[T] verifier.code_condition proofCode conclusion)
    (hCase :
      let proofCodeOne : SetTerm [SetSort.set] free :=
        proofCode.weakenBound SetSort.set
      let conclusionOne : SetTerm [SetSort.set] free :=
        conclusion.weakenBound SetSort.set
      let proofCodeTwo : SetTerm [SetSort.set, SetSort.set] free :=
        proofCodeOne.weakenBound SetSort.set
      let conclusionTwo : SetTerm [SetSort.set, SetSort.set] free :=
        conclusionOne.weakenBound SetSort.set
      let proofCodeThree : SetTerm
          [SetSort.set, SetSort.set, SetSort.set] free :=
        proofCodeTwo.weakenBound SetSort.set
      let conclusionThree : SetTerm
          [SetSort.set, SetSort.set, SetSort.set] free :=
        conclusionTwo.weakenBound SetSort.set
      let proofCodeFour : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        proofCodeThree.weakenBound SetSort.set
      let conclusionFour : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        conclusionThree.weakenBound SetSort.set
      let sequence : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there (.there (.there .here)))
      let certificates : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there (.there .here))
      let formulaCode : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there .here)
      let certificateCode : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar .here
      let body : SetFormula
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        code_condition_body verifier.as_object proofCodeFour conclusionFour
          sequence certificates formulaCode certificateCode verifier.logical_condition
      let bodyThree : SetFormula
          [SetSort.set, SetSort.set, SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (Sₘ(proofCodeThree)) body
      let bodyTwo : SetFormula
          [SetSort.set, SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (Sₘ(proofCodeTwo)) bodyThree
      let bodyOne : SetFormula [SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (seq₊_spaceₘ(ωₘ)) bodyTwo
      let opened : SetOpenFormula (SetSort.set :: free) :=
        Formula.openBoundTop (σ := signature) SetSort.set
          (bounded_exists_body
            (seq₊_spaceₘ(syntax_formula_code_set_term)) bodyOne)
      opened :: FreshVariable.extendContext SetSort.set Γ
        ⊢ₘ[T] result.weakenFree SetSort.set) :
    Γ ⊢ₘ[T] result := by
  apply bounded_exists_elim _ _ result ?_ hCase
  simpa [CheckedVerifier.code_condition,
    StructuredCertificateCondition.code_condition_apply, bounded_witness_closure,
    code_condition_plan] using hCode

/--
总证明码条件的前两层有界存在消去。

第二层使用 `openBoundLast` 保留第一层的 bound 槽，并把当前 `ω` 见证转入规范
free 槽；因此后续证明只需处理两个 checked 见证假设，不再复制替换组合细节。
-/
theorem code_condition_two_outer_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (proofCode conclusion : SetOpenTerm free)
    (result : SetOpenFormula free)
    (hCode : Γ ⊢ₘ[T] verifier.code_condition proofCode conclusion)
    (hCase :
      let proofCodeOne : SetTerm [SetSort.set] free :=
        proofCode.weakenBound SetSort.set
      let conclusionOne : SetTerm [SetSort.set] free :=
        conclusion.weakenBound SetSort.set
      let proofCodeTwo : SetTerm [SetSort.set, SetSort.set] free :=
        proofCodeOne.weakenBound SetSort.set
      let conclusionTwo : SetTerm [SetSort.set, SetSort.set] free :=
        conclusionOne.weakenBound SetSort.set
      let proofCodeThree : SetTerm
          [SetSort.set, SetSort.set, SetSort.set] free :=
        proofCodeTwo.weakenBound SetSort.set
      let conclusionThree : SetTerm
          [SetSort.set, SetSort.set, SetSort.set] free :=
        conclusionTwo.weakenBound SetSort.set
      let proofCodeFour : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        proofCodeThree.weakenBound SetSort.set
      let conclusionFour : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        conclusionThree.weakenBound SetSort.set
      let sequence : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there (.there (.there .here)))
      let certificates : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there (.there .here))
      let formulaCode : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there .here)
      let certificateCode : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar .here
      let body : SetFormula
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        code_condition_body verifier.as_object proofCodeFour conclusionFour
          sequence certificates formulaCode certificateCode verifier.logical_condition
      let bodyThree : SetFormula
          [SetSort.set, SetSort.set, SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (Sₘ(proofCodeThree)) body
      let bodyTwo : SetFormula
          [SetSort.set, SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (Sₘ(proofCodeTwo)) bodyThree
      let bodyOne : SetFormula [SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (seq₊_spaceₘ(ωₘ)) bodyTwo
      let openedOne : SetOpenFormula (SetSort.set :: free) :=
        Formula.openBoundTop (σ := signature) SetSort.set
          (bounded_exists_body
            (seq₊_spaceₘ(syntax_formula_code_set_term)) bodyOne)
      let contextOne : Context signature (SetSort.set :: free) :=
        openedOne :: FreshVariable.extendContext SetSort.set Γ
      let bodyTwoOpened : SetFormula [SetSort.set]
          (SetSort.set :: free) :=
        Formula.openBoundLast (σ := signature) [SetSort.set]
          SetSort.set bodyTwo
      let boundTwo : SetOpenTerm (SetSort.set :: free) :=
        Term.openBoundTop (σ := signature) SetSort.set
          (seq₊_spaceₘ(ωₘ) : SetTerm [SetSort.set] free)
      let openedTwo : SetOpenFormula (SetSort.set :: SetSort.set :: free) :=
        Formula.openBoundTop (σ := signature) SetSort.set
          (bounded_exists_body boundTwo bodyTwoOpened)
      openedTwo :: FreshVariable.extendContext SetSort.set contextOne
        ⊢ₘ[T] (result.weakenFree SetSort.set).weakenFree SetSort.set) :
    Γ ⊢ₘ[T] result := by
  extract_lets proofCodeOne conclusionOne proofCodeTwo conclusionTwo proofCodeThree conclusionThree
    proofCodeFour conclusionFour sequence certificates formulaCode certificateCode body bodyThree
    bodyTwo bodyOne openedOne contextOne bodyTwoOpened boundTwo openedTwo at hCase
  apply code_condition_outer_elim verifier proofCode conclusion result hCode
  change contextOne ⊢ₘ[T] result.weakenFree SetSort.set
  have hOpenedOne : contextOne ⊢ₘ[T] openedOne :=
    FirstOrder.Derives.assumption (by simp [contextOne])
  have hRest : contextOne ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set bodyOne :=
    FirstOrder.Derives.conj_elim_right hOpenedOne
  have hNext : contextOne ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound boundTwo bodyTwoOpened := by
    simpa only [bodyOne, boundTwo, bodyTwoOpened,
      Formula.openBoundTop_eq_openBoundLast, Term.openBoundTop_eq_openBoundLast,
      bounded_exists_openBoundLast] using hRest
  apply bounded_exists_elim
    boundTwo bodyTwoOpened (result.weakenFree SetSort.set) hNext
  exact hCase

/-!
总证明码条件的四层有界存在消去。

这里把序列、证书序列、公式码和证书码一次性打开；所有依赖界项都沿
`openBoundLast` 进入对应的 free 槽位，因此下游只处理实际四个见证假设。
-/
theorem code_condition_four_outer_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (proofCode conclusion : SetOpenTerm free)
    (result : SetOpenFormula free)
    (hCode : Γ ⊢ₘ[T] verifier.code_condition proofCode conclusion)
    (hCase :
      let proofCodeOne : SetTerm [SetSort.set] free :=
        proofCode.weakenBound SetSort.set
      let conclusionOne : SetTerm [SetSort.set] free :=
        conclusion.weakenBound SetSort.set
      let proofCodeTwo : SetTerm [SetSort.set, SetSort.set] free :=
        proofCodeOne.weakenBound SetSort.set
      let conclusionTwo : SetTerm [SetSort.set, SetSort.set] free :=
        conclusionOne.weakenBound SetSort.set
      let proofCodeThree : SetTerm
          [SetSort.set, SetSort.set, SetSort.set] free :=
        proofCodeTwo.weakenBound SetSort.set
      let conclusionThree : SetTerm
          [SetSort.set, SetSort.set, SetSort.set] free :=
        conclusionTwo.weakenBound SetSort.set
      let proofCodeFour : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        proofCodeThree.weakenBound SetSort.set
      let conclusionFour : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        conclusionThree.weakenBound SetSort.set
      let sequence : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there (.there (.there .here)))
      let certificates : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there (.there .here))
      let formulaCode : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar (.there .here)
      let certificateCode : SetTerm
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        .bvar .here
      let body : SetFormula
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
        code_condition_body verifier.as_object proofCodeFour conclusionFour
          sequence certificates formulaCode certificateCode verifier.logical_condition
      let bodyThree : SetFormula
          [SetSort.set, SetSort.set, SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (Sₘ(proofCodeThree)) body
      let bodyTwo : SetFormula
          [SetSort.set, SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (Sₘ(proofCodeTwo)) bodyThree
      let bodyOne : SetFormula [SetSort.set] free :=
        Formula.LevyBound.boundedExists set_levy_bound
          (seq₊_spaceₘ(ωₘ)) bodyTwo
      let openedOne : SetOpenFormula (SetSort.set :: free) :=
        Formula.openBoundTop (σ := signature) SetSort.set
          (bounded_exists_body
            (seq₊_spaceₘ(syntax_formula_code_set_term)) bodyOne)
      let contextOne : Context signature (SetSort.set :: free) :=
        openedOne :: FreshVariable.extendContext SetSort.set Γ
      let bodyTwoOpened : SetFormula [SetSort.set]
          (SetSort.set :: free) :=
        Formula.openBoundLast (σ := signature) [SetSort.set]
          SetSort.set bodyTwo
      let boundTwo : SetOpenTerm (SetSort.set :: free) :=
        Term.openBoundTop (σ := signature) SetSort.set
          (seq₊_spaceₘ(ωₘ) : SetTerm [SetSort.set] free)
      let openedTwo : SetOpenFormula (SetSort.set :: SetSort.set :: free) :=
        Formula.openBoundTop (σ := signature) SetSort.set
          (bounded_exists_body boundTwo bodyTwoOpened)
      let contextTwo : Context signature (SetSort.set :: SetSort.set :: free) :=
        openedTwo :: FreshVariable.extendContext SetSort.set contextOne
      let bodyThreeSequenceOpened : SetFormula
          [SetSort.set, SetSort.set] (SetSort.set :: free) :=
        Formula.openBoundLast (σ := signature)
          [SetSort.set, SetSort.set] SetSort.set bodyThree
      let bodyThreeOpened : SetFormula [SetSort.set]
          (SetSort.set :: SetSort.set :: free) :=
        Formula.openBoundLast (σ := signature)
          [SetSort.set] SetSort.set bodyThreeSequenceOpened
      let proofCodeTwoSequenceOpened : SetTerm [SetSort.set]
          (SetSort.set :: free) :=
        Term.openBoundLast (σ := signature)
          [SetSort.set] SetSort.set (Sₘ(proofCodeTwo))
      let boundThree : SetOpenTerm
          (SetSort.set :: SetSort.set :: free) :=
        Term.openBoundLast (σ := signature)
          [] SetSort.set proofCodeTwoSequenceOpened
      let openedThree : SetOpenFormula
          (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
        Formula.openBoundTop (σ := signature) SetSort.set
          (bounded_exists_body boundThree bodyThreeOpened)
      let contextThree : Context signature
          (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
        openedThree :: FreshVariable.extendContext SetSort.set contextTwo
      let bodySequenceOpened : SetFormula
          [SetSort.set, SetSort.set, SetSort.set] (SetSort.set :: free) :=
        Formula.openBoundLast (σ := signature)
          [SetSort.set, SetSort.set, SetSort.set] SetSort.set body
      let bodyCertificatesOpened : SetFormula
          [SetSort.set, SetSort.set]
          (SetSort.set :: SetSort.set :: free) :=
        Formula.openBoundLast (σ := signature)
          [SetSort.set, SetSort.set] SetSort.set bodySequenceOpened
      let bodyFormulaOpened : SetFormula [SetSort.set]
          (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
        Formula.openBoundLast (σ := signature)
          [SetSort.set] SetSort.set bodyCertificatesOpened
      let proofCodeThreeSequenceOpened : SetTerm
          [SetSort.set, SetSort.set] (SetSort.set :: free) :=
        Term.openBoundLast (σ := signature)
          [SetSort.set, SetSort.set] SetSort.set (Sₘ(proofCodeThree))
      let proofCodeThreeCertificatesOpened : SetTerm [SetSort.set]
          (SetSort.set :: SetSort.set :: free) :=
        Term.openBoundLast (σ := signature)
          [SetSort.set] SetSort.set proofCodeThreeSequenceOpened
      let boundFour : SetOpenTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: free) :=
        Term.openBoundLast (σ := signature)
          [] SetSort.set proofCodeThreeCertificatesOpened
      let openedFour : SetOpenFormula
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: free) :=
        Formula.openBoundTop (σ := signature) SetSort.set
          (bounded_exists_body boundFour bodyFormulaOpened)
      let contextFour : Context signature
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: free) :=
        openedFour :: FreshVariable.extendContext SetSort.set contextThree
      contextFour ⊢ₘ[T]
        (((result.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set) :
    Γ ⊢ₘ[T] result := by
  extract_lets proofCodeOne conclusionOne proofCodeTwo conclusionTwo proofCodeThree conclusionThree
    proofCodeFour conclusionFour sequence certificates formulaCode certificateCode body bodyThree
    bodyTwo bodyOne openedOne contextOne bodyTwoOpened boundTwo openedTwo contextTwo
    bodyThreeSequenceOpened bodyThreeOpened proofCodeTwoSequenceOpened boundThree openedThree
    contextThree bodySequenceOpened bodyCertificatesOpened bodyFormulaOpened
    proofCodeThreeSequenceOpened proofCodeThreeCertificatesOpened boundFour openedFour contextFour
    at hCase
  apply code_condition_two_outer_elim verifier proofCode conclusion result hCode
  change contextTwo ⊢ₘ[T] (result.weakenFree SetSort.set).weakenFree SetSort.set
  have hOpenedTwo : contextTwo ⊢ₘ[T] openedTwo :=
    FirstOrder.Derives.assumption (by simp [contextTwo])
  have hRestTwo : contextTwo ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set bodyTwoOpened :=
    FirstOrder.Derives.conj_elim_right hOpenedTwo
  have hNextThree : contextTwo ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound boundThree bodyThreeOpened := by
    simpa only [bodyTwoOpened, bodyThreeOpened, bodyThreeSequenceOpened, bodyTwo, bodyThree, boundThree, proofCodeTwoSequenceOpened,
      Formula.openBoundTop_eq_openBoundLast, bounded_exists_openBoundLast] using hRestTwo
  apply bounded_exists_elim
    boundThree bodyThreeOpened
      ((result.weakenFree SetSort.set).weakenFree SetSort.set) hNextThree
  have hOpenedThree : contextThree ⊢ₘ[T] openedThree :=
    FirstOrder.Derives.assumption (by simp [contextThree])
  have hRestThree : contextThree ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set bodyThreeOpened :=
    FirstOrder.Derives.conj_elim_right hOpenedThree
  have hNextFour : contextThree ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound boundFour bodyFormulaOpened := by
    simpa only [bodyThreeOpened, bodyThreeSequenceOpened, bodyFormulaOpened, bodyCertificatesOpened, bodySequenceOpened,
        bodyThree, boundFour, proofCodeThreeSequenceOpened, proofCodeThreeCertificatesOpened,
      Formula.openBoundTop_eq_openBoundLast, bounded_exists_openBoundLast] using hRestThree
  apply bounded_exists_elim
    boundFour bodyFormulaOpened
      (((result.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set)
      hNextFour
  exact hCase

/-! ## 证明行公式码承载 -/

theorem witness_row_formula_mem_of_code_body
    {T : SetTheory}
    (P : IntrinsicProofSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (number : Nat)
    (sequence certificates formulaCode certificateCode : SetOpenTerm free)
    (index : Nat)
    (hIndex : index <
      (proof_sequence_decode (godel_unpair_value number).1).length)
    (hBody :
      Γ ⊢ₘ[T]
        (((verifier.sequence_condition sequence certificates ∧ₘ
            proof_sequence_code_condition sequence formulaCode) ∧ₘ
          nat_sequence_code_condition certificates certificateCode) ∧ₘ
        ((proof_code_component_bound
            (numₘ(number)) formulaCode ∧ₘ
          proof_code_component_bound
            (numₘ(number)) certificateCode) ∧ₘ
          ((numₘ(number) ≐ₘ
              godel_pairₘ(formulaCode, certificateCode)) ∧ₘ
            proof_sequence_terminal_condition
              sequence (numₘ(number)))))) :
    Γ ⊢ₘ[T]
      nat_sequence_graph_term
        ((proof_sequence_decode (godel_unpair_value number).1)[index]'hIndex) ∈ₘ
        syntax_formula_code_set_term := by
  have hSequenceCondition :=
    FirstOrder.Derives.conj_elim_left
      (FirstOrder.Derives.conj_elim_left hBody)
  have hSequencePositive : Γ ⊢ₘ[T]
      sequence ∈ₘ seq₊_spaceₘ(syntax_formula_code_set_term) := by
    have hPrefix := FirstOrder.Derives.conj_elim_left hSequenceCondition
    have hPrefix' := FirstOrder.Derives.conj_elim_left hPrefix
    have hPrefix'' := FirstOrder.Derives.conj_elim_left hPrefix'
    have hMembers := FirstOrder.Derives.conj_elim_left hPrefix''
    have hMember := FirstOrder.Derives.conj_elim_left hMembers
    simpa [CheckedVerifier.sequence_condition,
      StructuredCertificateCondition.sequence_condition] using hMember
  have hSequences :=
    witness_sequences_of_code_body
      P verifier number sequence certificates formulaCode certificateCode hBody
  have hSequenceEquality := FirstOrder.Derives.conj_elim_left hSequences
  let rows : List (List Nat) :=
    proof_sequence_decode (godel_unpair_value number).1
  have hCanonicalPositive : Γ ⊢ₘ[T]
      proof_sequence_graph_term rows ∈ₘ
        seq₊_spaceₘ(syntax_formula_code_set_term) := by
    apply FirstOrder.Derives.iff_elim_left
      (membership_left_iff_of_equality
        sequence (proof_sequence_graph_term rows)
        (seq₊_spaceₘ(syntax_formula_code_set_term)) hSequenceEquality)
    exact hSequencePositive
  simpa [rows] using
    (row_syntax_formula_mem_of_graph
      P.row_support rows index hIndex hCanonicalPositive)

/-- 总证明码 body 的终端条件可直接归一到规范证明序列。 -/
theorem witness_terminal_of_code_body
    {T : SetTheory}
    (P : IntrinsicProofSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (number : Nat)
    (sequence certificates formulaCode certificateCode conclusion : SetOpenTerm free)
    (hBody :
      Γ ⊢ₘ[T]
        (((verifier.sequence_condition sequence certificates ∧ₘ
            proof_sequence_code_condition sequence formulaCode) ∧ₘ
          nat_sequence_code_condition certificates certificateCode) ∧ₘ
        ((proof_code_component_bound
            (numₘ(number)) formulaCode ∧ₘ
          proof_code_component_bound
            (numₘ(number)) certificateCode) ∧ₘ
          ((numₘ(number) ≐ₘ
              godel_pairₘ(formulaCode, certificateCode)) ∧ₘ
            proof_sequence_terminal_condition
              sequence (numₘ(number))))))
    (hConclusion :
      Γ ⊢ₘ[T] numₘ(number) ≐ₘ conclusion) :
    Γ ⊢ₘ[T]
      proof_sequence_terminal_condition
        (proof_sequence_graph_term
          (proof_sequence_decode (godel_unpair_value number).1))
        conclusion := by
  have hSequences :=
    witness_sequences_of_code_body
      P verifier number sequence certificates formulaCode certificateCode hBody
  have hSequence := FirstOrder.Derives.conj_elim_left hSequences
  have hPairAndTerminal :=
    FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_right hBody)
  have hTerminal := FirstOrder.Derives.conj_elim_right hPairAndTerminal
  have hCanonicalTerminal :=
    terminal_condition_of_sequence_eq
      sequence
      (proof_sequence_graph_term
        (proof_sequence_decode (godel_unpair_value number).1))
      (numₘ(number))
      hSequence hTerminal
  exact terminal_condition_of_conclusion_eq
    (proof_sequence_graph_term
      (proof_sequence_decode (godel_unpair_value number).1))
    (numₘ(number)) conclusion hConclusion hCanonicalTerminal

/-- 总证明码的终端不匹配直接推出对象层矛盾。 -/
theorem code_body_falsum_of_terminal_mismatch
    {T : SetTheory}
    (P : IntrinsicProofSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (number : Nat)
    (sequence certificates formulaCode certificateCode conclusion : SetOpenTerm free)
    (hBody :
      Γ ⊢ₘ[T]
        (((verifier.sequence_condition sequence certificates ∧ₘ
            proof_sequence_code_condition sequence formulaCode) ∧ₘ
          nat_sequence_code_condition certificates certificateCode) ∧ₘ
        ((proof_code_component_bound
            (numₘ(number)) formulaCode ∧ₘ
          proof_code_component_bound
            (numₘ(number)) certificateCode) ∧ₘ
          ((numₘ(number) ≐ₘ
              godel_pairₘ(formulaCode, certificateCode)) ∧ₘ
            proof_sequence_terminal_condition
              sequence (numₘ(number))))))
    (hConclusion :
      Γ ⊢ₘ[T] numₘ(number) ≐ₘ conclusion)
    (hMismatch :
      ∀ index,
        index < (proof_sequence_decode (godel_unpair_value number).1).length →
        (proof_sequence_decode (godel_unpair_value number).1).length = index + 1 →
        (conclusion ≐ₘ
            (proof_sequence_graph_term
              (proof_sequence_decode (godel_unpair_value number).1) ·ₘ
                numₘ(index))) :: Γ
          ⊢ₘ[T] Formula.falsum) :
    Γ ⊢ₘ[T] Formula.falsum := by
  let rows : List (List Nat) :=
    proof_sequence_decode (godel_unpair_value number).1
  let canonicalSequence : SetOpenTerm free :=
    proof_sequence_graph_term rows
  have hDomain : Γ ⊢ₘ[T]
      domₘ(canonicalSequence) ≐ₘ numₘ(rows.length) := by
    simpa [canonicalSequence] using
      (proof_sequence_graph_domain_eq
        (Γ := Γ)
        P.row_support.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport
        rows)
  have hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition canonicalSequence conclusion := by
    simpa [canonicalSequence, rows] using
      (witness_terminal_of_code_body
        P verifier number sequence certificates formulaCode certificateCode
          conclusion hBody hConclusion)
  apply terminal_falsum_of_domain_eq
    P.certificate_core.toFiniteCore canonicalSequence conclusion rows.length
    hDomain hTerminal
  intro index hIndex hLast
  simpa [canonicalSequence, rows] using
    (hMismatch index hIndex hLast)

/-- 总证明码的终端行值不匹配直接推出对象层矛盾。 -/
theorem code_body_falsum_of_row_mismatch
    {T : SetTheory}
    (P : IntrinsicProofSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (number : Nat)
    (sequence certificates formulaCode certificateCode conclusion : SetOpenTerm free)
    (hBody :
      Γ ⊢ₘ[T]
        (((verifier.sequence_condition sequence certificates ∧ₘ
            proof_sequence_code_condition sequence formulaCode) ∧ₘ
          nat_sequence_code_condition certificates certificateCode) ∧ₘ
        ((proof_code_component_bound
            (numₘ(number)) formulaCode ∧ₘ
          proof_code_component_bound
            (numₘ(number)) certificateCode) ∧ₘ
          ((numₘ(number) ≐ₘ
              godel_pairₘ(formulaCode, certificateCode)) ∧ₘ
            proof_sequence_terminal_condition
              sequence (numₘ(number))))))
    (hConclusion :
      Γ ⊢ₘ[T] numₘ(number) ≐ₘ conclusion)
    (hMismatch :
      ∀ (index : Nat)
        (hIndex : index < (proof_sequence_decode (godel_unpair_value number).1).length),
        (proof_sequence_decode (godel_unpair_value number).1).length = index + 1 →
        (conclusion ≐ₘ
            nat_sequence_graph_term
              ((proof_sequence_decode (godel_unpair_value number).1)[index]'hIndex)) :: Γ
          ⊢ₘ[T] Formula.falsum) :
    Γ ⊢ₘ[T] Formula.falsum := by
  let rows : List (List Nat) :=
    proof_sequence_decode (godel_unpair_value number).1
  let canonicalSequence : SetOpenTerm free :=
    proof_sequence_graph_term rows
  have hDomain : Γ ⊢ₘ[T]
      domₘ(canonicalSequence) ≐ₘ numₘ(rows.length) := by
    simpa [canonicalSequence] using
      (proof_sequence_graph_domain_eq
        (Γ := Γ)
        P.row_support.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport
        rows)
  have hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition canonicalSequence conclusion := by
    simpa [canonicalSequence, rows] using
      (witness_terminal_of_code_body
        P verifier number sequence certificates formulaCode certificateCode
          conclusion hBody hConclusion)
  apply terminal_falsum_of_proof_sequence_row_mismatch
    P.certificate_core.toFiniteCore
      P.row_support.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
      rows conclusion hDomain hTerminal
  intro index hIndex hLast
  simpa [rows] using (hMismatch index hIndex hLast)

/-- 总证明码的目标行列表不匹配直接推出对象层矛盾。 -/
theorem code_body_falsum_of_row_list_mismatch
    {T : SetTheory}
    (P : IntrinsicProofSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (number : Nat)
    (sequence certificates formulaCode certificateCode conclusion : SetOpenTerm free)
    (targetRow : List Nat)
    (hBody :
      Γ ⊢ₘ[T]
        (((verifier.sequence_condition sequence certificates ∧ₘ
            proof_sequence_code_condition sequence formulaCode) ∧ₘ
          nat_sequence_code_condition certificates certificateCode) ∧ₘ
        ((proof_code_component_bound
            (numₘ(number)) formulaCode ∧ₘ
          proof_code_component_bound
            (numₘ(number)) certificateCode) ∧ₘ
          ((numₘ(number) ≐ₘ
              godel_pairₘ(formulaCode, certificateCode)) ∧ₘ
            proof_sequence_terminal_condition
              sequence (numₘ(number))))))
    (hConclusion :
      Γ ⊢ₘ[T] numₘ(number) ≐ₘ conclusion)
    (hTargetConclusion :
      Γ ⊢ₘ[T]
        conclusion ≐ₘ nat_sequence_graph_term targetRow)
    (hMismatch :
      ∀ (index : Nat)
        (hIndex : index <
          (proof_sequence_decode (godel_unpair_value number).1).length),
        (proof_sequence_decode (godel_unpair_value number).1).length =
          index + 1 →
        targetRow ≠
          (proof_sequence_decode (godel_unpair_value number).1)[index]'hIndex) :
    Γ ⊢ₘ[T] Formula.falsum := by
  let rows : List (List Nat) :=
    proof_sequence_decode (godel_unpair_value number).1
  let canonicalSequence : SetOpenTerm free :=
    proof_sequence_graph_term rows
  have hDomain : Γ ⊢ₘ[T]
      domₘ(canonicalSequence) ≐ₘ numₘ(rows.length) := by
    simpa [canonicalSequence] using
      (proof_sequence_graph_domain_eq
        (Γ := Γ)
        P.row_support.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport
        rows)
  have hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition canonicalSequence conclusion := by
    simpa [canonicalSequence, rows] using
      (witness_terminal_of_code_body
        P verifier number sequence certificates formulaCode certificateCode
          conclusion hBody hConclusion)
  apply terminal_falsum_of_proof_sequence_list_mismatch
    P.certificate_core.toFiniteCore
      P.row_support.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
      rows targetRow conclusion
    hTargetConclusion hDomain hTerminal
  intro index hIndex hLast
  simpa [rows] using (hMismatch index hIndex hLast)

end IntrinsicCheckedWitness
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
