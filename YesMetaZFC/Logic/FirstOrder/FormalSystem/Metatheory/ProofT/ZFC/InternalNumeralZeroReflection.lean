import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralArithmeticReflection

/-! # 内部数码的零测试反射

零相等与不等两个分支均构造实际证明码。非零分支只反演数码图根行，
不对外部可能非良基的自然数使用递归。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def zeroBody : SetOpenFormula [.set] := (.fvar .here) ≐ₘ ∅ₘ
def successorNonzeroBody : SetOpenFormula [.set] := ¬ₘ (Sₘ(.fvar .here) ≐ₘ ∅ₘ)

theorem zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input named : 𝒩.Carrier .set} (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named) (hZero : input = z 𝒩) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) zeroBody) := by
  subst input
  rw [(PureSourceNumeralSyntax.zero_iff h𝒩 hNamed).mp hGraph]
  have h := of_derives h𝒩 (Metatheory.Derives.equality_refl (∅ₘ : SetOpenTerm []))
  rw [← original_quote] at h
  have hCode := tree_numeral h𝒩 (SyntaxEncode.term (numₘ(0) : SetOpenTerm []))
  change node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []] =
    numeral 𝒩 ObjectNumeralSyntax.zeroCode at hCode
  change ProvableCode 𝒩 (node 𝒩 3 [(node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]),
    (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []])]) at h
  change ProvableCode 𝒩 (node 𝒩 3 [numeral 𝒩 ObjectNumeralSyntax.zeroCode,
    (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []])])
  rw [← hCode]
  exact h

theorem successor_nonzero_derives : Derives intrinsic_zfc_theory [] successorNonzeroBody :=
  Derives.imp_elim
    (Derives.theory_weaken intrinsic_zfc_arithmetic_support.toArithmeticSupport.contains_empty_set
      (member_implies_set_nonempty (.fvar .here) Sₘ(.fvar .here)))
    (Derives.theory_weaken intrinsic_zfc_arithmetic_support.toArithmeticSupport.contains_successor
      (mem_successor_self (.fvar .here)))

theorem nonzero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input named : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named) (hNonzero : input ≠ z 𝒩) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) (.neg zeroBody)) := by
  rcases PureSourceNumeralSyntax.cases_graph h𝒩 hInput hNamed hGraph with hZero | hSuccessor
  · exact False.elim (hNonzero hZero.1)
  obtain ⟨predecessor, previous, hp, hv, _, rfl, hPrevious⟩ := hSuccessor
  have h := specialize h𝒩 successorNonzeroBody successor_nonzero_derives hp hv hPrevious
  have hSymbol := tree_numeral h𝒩 (NatPacket.leaf FunctionSymbol.successor.ctorIdx)
  change node 𝒩 FunctionSymbol.successor.ctorIdx [] = numeral 𝒩 ObjectNumeralSyntax.successorSymbol at hSymbol
  change ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3
    [(node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), previous]),
      (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []])]]) at h
  rw [hSymbol] at h
  exact h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
