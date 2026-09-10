import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalCodingEvaluation

/-! # 既定结构 quotation 的求值证明

保留原 quotation 的节点、字段顺序和树结构，不把巨大编码展开为宿主数码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

mutual
theorem tree_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values) :
    (input : NatPacket.Tree) → TermEvaluates (Env.empty : Env 𝒩 [] []) values (IntrinsicQuotation.tree input)
  | .node tag fields => node_term_evaluation h𝒩 Env.empty values hv tag _ (forest_term_evaluation h𝒩 values hv fields)

theorem forest_term_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values) :
    (inputs : List NatPacket.Tree) → ∀ field ∈ IntrinsicQuotation.forest inputs,
      TermEvaluates (Env.empty : Env 𝒩 [] []) values field
  | .nil, _, h => by cases h
  | head :: tail, field, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact tree_term_evaluation h𝒩 values hv head
    · exact forest_term_evaluation h𝒩 values hv tail field h
end

/-- 闭 quotation 不依赖自由槽位，公共入口统一填入合法的零数码。 -/
theorem quotation_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free : SetContext} (input : SetFormula bound free) :
    TermEvaluates (Env.empty : Env 𝒩 [] []) (fun _ => numeral 𝒩 ObjectNumeralSyntax.zeroCode) (IntrinsicQuotation.quote input) :=
  tree_term_evaluation h𝒩 _ (fun _ => ⟨numeral_natural h𝒩 _, z 𝒩, (omega_closed h𝒩).1, PureSourceNumeralSyntax.zero h𝒩⟩)
    (SyntaxEncode.formula input)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
