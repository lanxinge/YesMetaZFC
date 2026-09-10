import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralZeroReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedDerivability

/-! # 当前可证明性矩阵与 D3 的反射装配

矩阵由现有自然数证明图打开最外层 binder 得到。自然数 guard 的反射已经构造，
本层末尾定理参数化于原检查器正文反射；InternalVerificationReflection 填入该参数，
ReducedIntrospection 给出完整 D3。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x

noncomputable def proofMatrix (φ : SetSentence) : SetOpenFormula [.set] :=
  Formula.openBoundTop (σ := signature) (free := []) SetSort.set
    ((NaturalProofPresentation.graph ReducedProofPresentation.presentation.graph).condition
      (.bvar .here) ((IntrinsicQuotation.quote φ : SetOpenTerm []).weakenBound SetSort.set))

/-- 原始检查器正文；这里只去掉外层自然数 guard，检查器本身不变。 -/
noncomputable def verificationMatrix (φ : SetSentence) : SetOpenFormula [.set] :=
  Formula.openBoundTop (σ := signature) (free := []) SetSort.set
    (ReducedProofPresentation.presentation.graph.condition
      (.bvar .here) ((IntrinsicQuotation.quote φ : SetOpenTerm []).weakenBound SetSort.set))

private theorem naturalMatrix_split (graph : Delta0ProofGraph) (conclusion : SetTerm [.set] []) :
    Formula.openBoundTop SetSort.set ((NaturalProofPresentation.graph graph).condition (.bvar .here) conclusion) =
      .conj InternalNumeralReflection.naturalBody
        (Formula.openBoundTop SetSort.set (graph.condition (.bvar .here) conclusion)) := by
  change Formula.openBoundTop (σ := signature) (free := []) SetSort.set
    (NaturalProofPresentation.template graph (.bvar .here : SetTerm [.set] []) conclusion) = _
  rw [NaturalProofPresentation.template_apply]
  rfl

theorem proofMatrix_split (φ : SetSentence) :
    proofMatrix φ = .conj InternalNumeralReflection.naturalBody (verificationMatrix φ) :=
  naturalMatrix_split ReducedProofPresentation.presentation.graph _

/-- 重新封闭后逐字恢复当前普通可证明性句子。 -/
theorem proofMatrix_exists (φ : SetSentence) :
    (proofMatrix φ).existsFreeTop SetSort.set = provable φ := by
  rw [proofMatrix, Formula.existsFreeTop_openBoundTop]
  rfl

theorem proofMatrix_satisfies {𝒩 : Structure.{0,0,0,x} signature}
    (φ : SetSentence) (input : 𝒩.Carrier .set) :
    (proofMatrix φ).satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔
      mem 𝒩 input (w 𝒩) ∧ PureNaturalRosserAgreement.Proof 𝒩 input φ := by
  have h := Formula.satisfies_abstractFreeTop (Env.empty : Env 𝒩 [] []) input (proofMatrix φ)
  rw [show (proofMatrix φ).abstractFreeTop =
    (NaturalProofPresentation.graph ReducedProofPresentation.presentation.graph).condition
      (.bvar .here) ((IntrinsicQuotation.quote φ : SetOpenTerm []).weakenBound SetSort.set) from
        by unfold proofMatrix; exact Formula.abstractFreeTop_openBoundTop (σ := signature) (free := []) SetSort.set _] at h
  have hEnv : (Env.empty.pushFree input : Env 𝒩 [] [.set]) = templateEnv (.cons input .nil) := by
    rw [Env.mk.injEq]
    constructor
    · funext sort entry; cases entry
    · funext sort entry
      cases entry with
      | here => rfl
      | there previous => cases previous
  rw [hEnv] at h
  apply h.symm.trans
  rw [NaturalRosserSemantics.binary_satisfies, Term.eval_weakenBound]
  exact NaturalRosserSemantics.natural_graph_satisfies ReducedProofPresentation.presentation.graph input _

/-- 条件性装配：参数是实际矩阵在内部数码实例上的正反射。 -/
theorem introspection_of_matrix_reflection (φ : SetSentence)
    (hReflection : ∀ (𝒩 : Structure.{0,0,0,0} signature), Theory.Models 𝒩 intrinsic_zfc_theory →
      ∀ input, mem 𝒩 input (w 𝒩) →
        (proofMatrix φ).satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) →
        ∃ named proof, mem 𝒩 named (w 𝒩) ∧ PureSourceNumeralSyntax.Graph 𝒩 input named ∧
          mem 𝒩 proof (w 𝒩) ∧ CodeProof 𝒩 proof (PureSourceInstantiation.formula 𝒩 (fun _ => named) (proofMatrix φ))) :
    Derives intrinsic_zfc_theory [] (Formula.imp (provable φ) (provable (provable φ))) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  change (provable φ).TrueIn 𝒩 → (provable (provable φ)).TrueIn 𝒩
  intro hProvable
  obtain ⟨input, hInput, hProof⟩ := (provable_satisfies φ).mp hProvable
  obtain ⟨named, proof, hNamed, hGraph, hp, hDerives⟩ :=
    hReflection 𝒩 h𝒩 input hInput ((proofMatrix_satisfies φ input).mpr ⟨hInput, hProof⟩)
  have h := InternalNumeralProof.exists_introduction h𝒩 (proofMatrix φ) hInput hNamed hGraph hp hDerives
  rw [proofMatrix_exists] at h
  exact (provable_satisfies (provable φ)).mpr h

/-- 数码自然数判断已由内部归纳证明；矩阵装配只消费原检查器正文的证明。 -/
theorem matrix_of_verification {𝒩 : Structure.{0,0,0,x} signature}
    (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (φ : SetSentence)
    {input named : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hVerification : ProvableCode 𝒩 (PureSourceInstantiation.formula 𝒩 (fun _ => named) (verificationMatrix φ))) :
    ProvableCode 𝒩 (PureSourceInstantiation.formula 𝒩 (fun _ => named) (proofMatrix φ)) := by
  rw [proofMatrix_split]
  exact InternalNumeralProof.instance_conj_intro h𝒩 _ _ hInput hNamed hGraph
    (InternalNumeralReflection.natural h𝒩 hInput hNamed hGraph) hVerification

/-- D3 装配接口：自然数 guard 的反射已消去，消费实际检查器反射。 -/
theorem introspection_of_verification_reflection (φ : SetSentence)
    (hReflection : ∀ (𝒩 : Structure.{0,0,0,0} signature), Theory.Models 𝒩 intrinsic_zfc_theory →
      ∀ input, mem 𝒩 input (w 𝒩) →
        (verificationMatrix φ).satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) →
        ∃ named, mem 𝒩 named (w 𝒩) ∧ PureSourceNumeralSyntax.Graph 𝒩 input named ∧
          ProvableCode 𝒩 (PureSourceInstantiation.formula 𝒩 (fun _ => named) (verificationMatrix φ))) :
    Derives intrinsic_zfc_theory [] (.imp (provable φ) (provable (provable φ))) := by
  apply introspection_of_matrix_reflection φ
  intro 𝒩 h𝒩 input hInput hMatrix
  rw [proofMatrix_split, Formula.satisfies] at hMatrix
  obtain ⟨named, hNamed, hGraph, hVerification⟩ := hReflection 𝒩 h𝒩 input hInput hMatrix.2
  obtain ⟨proof, hp, hProof⟩ := matrix_of_verification h𝒩 φ hInput hNamed hGraph hVerification
  exact ⟨named, proof, hNamed, hGraph, hp, hProof⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProvability
