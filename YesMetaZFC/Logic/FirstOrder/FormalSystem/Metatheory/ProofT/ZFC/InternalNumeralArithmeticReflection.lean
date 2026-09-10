import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralReflection

/-! # 内部数码的基础算术反射

直接构造任意内部自然数的数码属于 ω 的证明。后继步骤采用实际源定理的
内部特化及 MP；归纳性质由可分离对象公式给出。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def naturalBody : SetOpenFormula [.set] := (.fvar .here) ∈ₘ ωₘ
def successorNaturalBody : SetOpenFormula [.set] := Sₘ(.fvar .here) ∈ₘ ωₘ

theorem natural_zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => numeral 𝒩 ObjectNumeralSyntax.zeroCode) naturalBody) := by
  have h := of_derives h𝒩 (Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_infinity
    (infinity_zero_mem_omega (free := []) (Γ := [])))
  rw [← original_quote] at h
  have hZero := tree_numeral h𝒩 (SyntaxEncode.term (numₘ(0) : SetOpenTerm []))
  change node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []] =
    numeral 𝒩 ObjectNumeralSyntax.zeroCode at hZero
  change ProvableCode 𝒩 (node 𝒩 2 [(node 𝒩 RelationSymbol.membership.ctorIdx []),
    (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]), (node 𝒩 2 [node 𝒩 FunctionSymbol.omega.ctorIdx []])]) at h
  rw [hZero] at h
  exact h

theorem natural_successor (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input named : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hProof : ProvableCode 𝒩 (formula 𝒩 (fun _ => named) naturalBody)) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => PureSourceNumeralSyntax.next 𝒩 named) naturalBody) := by
  have hStep : Derives intrinsic_zfc_theory [] (.imp naturalBody successorNaturalBody) :=
    Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_infinity
      (Derives.imp_intro (infinity_successor_mem_omega (.fvar .here)
        (Derives.assumption (List.mem_cons_self ..))))
  have h := instance_modus_ponens h𝒩 naturalBody successorNaturalBody hInput hNamed hGraph hProof
    (specialize h𝒩 _ hStep hInput hNamed hGraph)
  have hSymbol := tree_numeral h𝒩 (NatPacket.leaf FunctionSymbol.successor.ctorIdx)
  change node 𝒩 FunctionSymbol.successor.ctorIdx [] = numeral 𝒩 ObjectNumeralSyntax.successorSymbol at hSymbol
  change ProvableCode 𝒩 (node 𝒩 2 [(node 𝒩 RelationSymbol.membership.ctorIdx []),
    (node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), named]), (node 𝒩 2 [node 𝒩 FunctionSymbol.omega.ctorIdx []])]) at h
  rw [hSymbol] at h
  exact h

/-- 任意内部数码（包括非标准数码）的自然数判断有当前证明谓词接受的证明。 -/
theorem natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input named : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) naturalBody) :=
  numeral_induction h𝒩 naturalBody (natural_zero h𝒩)
    (fun _ _ hi hn hg hp => natural_successor h𝒩 hi hn hg hp) hInput hNamed hGraph

/-- 消去源定理的自然数前提，生成每个内部数码实例的证明。 -/
theorem of_natural_derives (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula [.set]) (hDerives : Derives intrinsic_zfc_theory [] (.imp naturalBody body))
    {input named : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) body) :=
  instance_modus_ponens h𝒩 naturalBody body hInput hNamed hGraph
    (natural h𝒩 hInput hNamed hGraph) (specialize h𝒩 _ hDerives hInput hNamed hGraph)

/-- 上述统一构造本身可由源理论证明，不留下反射假设。 -/
theorem onNaturals_derives (body : SetOpenFormula [.set])
    (hDerives : Derives intrinsic_zfc_theory [] (.imp naturalBody body)) :
    Derives intrinsic_zfc_theory []
      (ObjectNumeralReflection.onNaturals ReducedProofPresentation.presentation.graph body) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  rw [Formula.TrueIn, ObjectNumeralReflection.onNaturals, Formula.satisfies_forallFreeTop]
  intro input
  change mem 𝒩 input (w 𝒩) → _
  intro hInput
  apply (atNumber_satisfies _ _ _).mpr
  intro named hNamed hGraph
  exact of_natural_derives h𝒩 body hDerives hInput hNamed hGraph

/-- 每个内部数码可证明属于 ω 的闭句子版本。 -/
theorem natural_derives : Derives intrinsic_zfc_theory []
    (ObjectNumeralReflection.onNaturals ReducedProofPresentation.presentation.graph naturalBody) :=
  onNaturals_derives naturalBody (Derives.imp_intro (Derives.assumption (List.mem_cons_self ..)))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
