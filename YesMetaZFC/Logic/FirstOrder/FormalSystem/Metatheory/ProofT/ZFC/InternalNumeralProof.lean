import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourcePointInstantiation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceInstantiationSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofLogicalConstruction

/-! # 数码实例的内部证明到存在句子证明

全部语法和点实例化义务由已证明的构造消去。输入可以是非标准自然数；
本模块消费实例的内部证明，尚不从验证图真值产生该证明。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralProof
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceInstantiation PureSourceFormulaConstruction
open ReducedProofLocalConstruction ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem instance_wellFormed (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula [.set]) {input named : 𝒩.Carrier .set}
    (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named) :
    FormulaGraph (z 𝒩) (z 𝒩) (formula 𝒩 (fun _ => named) body) :=
  formula_wellFormed h𝒩 (fun _ => hNamed) (omega_closed h𝒩).1
    (fun depth _ _ => PureSourceNumeralSyntax.graph_term h𝒩
      (numeral_natural h𝒩 depth) (omega_closed h𝒩).1 hInput hNamed hGraph) body

/-- 数码图和实例证明足以构造当前证明图接受的存在句子证明。 -/
theorem exists_introduction (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula [.set]) {input named proof : 𝒩.Carrier .set}
    (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hProof : mem 𝒩 proof (w 𝒩)) (hDerives : CodeProof 𝒩 proof (formula 𝒩 (fun _ => named) body)) :
    ∃ result, mem 𝒩 result (w 𝒩) ∧
      PureNaturalRosserAgreement.Proof 𝒩 result (body.existsFreeTop SetSort.set) := by
  have hBody := formula_natural h𝒩 (original_natural h𝒩) body.abstractFreeTop
  rw [original_quote] at hBody
  obtain ⟨result, hResult, hDerives⟩ := ReducedProofLogicalConstruction.exists_introduction h𝒩
    hBody hNamed (formula_natural h𝒩 (fun _ => hNamed) body)
    ((syntax_satisfies _).mpr (original_wellFormed h𝒩 body.abstractFreeTop))
    ((syntax_satisfies _).mpr (PureSourceNumeralSyntax.graph_closedTerm h𝒩 hInput hNamed hGraph))
    ((syntax_satisfies _).mpr (instance_wellFormed h𝒩 body hInput hNamed hGraph))
    (unary_point h𝒩 body hNamed) hProof hDerives
  refine ⟨result, hResult, (codeProof_quotation _ _).mp ?_⟩
  rw [← original_quote]
  change CodeProof 𝒩 result (node 𝒩 10 [formula 𝒩 (originalValues 𝒩) body.abstractFreeTop])
  rw [original_quote]
  exact hDerives

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralProof
