import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralZeroReflection

/-! # 两个内部数码的等式证明构造

任意有限参数特化用于对称性和后继单射性。数值相等时使用数码图唯一性，
不相等的后继步骤则消费前驱不等式的实际内部证明。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def equalityBody : SetOpenFormula [.set,.set] := (.fvar .here) ≐ₘ (.fvar (.there .here))
def reverseEqualityBody : SetOpenFormula [.set,.set] := (.fvar (.there .here)) ≐ₘ (.fvar .here)
def successorEqualityBody : SetOpenFormula [.set,.set] := Sₘ(.fvar .here) ≐ₘ Sₘ(.fvar (.there .here))
def firstNaturalBody : SetOpenFormula [.set,.set] := (.fvar .here) ∈ₘ ωₘ

theorem pair_numeralValues {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second) :
    NumeralValues 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) :=
  numeralValues_prepend (fun _ => ⟨hs, right, hr, hSecond⟩) hl hf hFirst

/-- 相等的内部数值生成其两个数码之间的等式证明。 -/
theorem equal (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hEqual : left = right) : ProvableCode 𝒩 (node 𝒩 3 [first, second]) := by
  subst right
  rw [← PureSourceNumeralSyntax.functional h𝒩 hl hf hs hFirst hSecond]
  exact specialize h𝒩 ((.fvar .here : SetOpenTerm [.set]) ≐ₘ (.fvar .here))
    (Metatheory.Derives.equality_refl _) hl hf hFirst

theorem inequality_symmetry_derives : Derives intrinsic_zfc_theory []
    (.imp (.neg equalityBody) (.neg reverseEqualityBody)) := by
  apply Derives.imp_intro
  apply Derives.neg_intro
  have hEq : Derives intrinsic_zfc_theory [reverseEqualityBody, .neg equalityBody] reverseEqualityBody :=
    Derives.assumption (List.mem_cons_self ..)
  have hNeg : Derives intrinsic_zfc_theory [reverseEqualityBody, .neg equalityBody] (.neg equalityBody) :=
    Derives.assumption (by simp)
  exact Derives.neg_elim (Metatheory.Derives.equality_symm hEq) hNeg

theorem inequality_symmetry (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hProof : ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [first, second]])) :
    ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [second, first]]) := by
  have hValues := pair_numeralValues hl hr hf hs hFirst hSecond
  exact values_modus_ponens (values := ObjectCodeInstantiation.prepend first (fun _ => second))
    h𝒩 (.neg equalityBody) (.neg reverseEqualityBody) hValues hProof
    (specialize_values h𝒩 _ inequality_symmetry_derives hValues)

theorem successor_inequality_derives : Derives intrinsic_zfc_theory []
    (.imp firstNaturalBody (.imp (.neg equalityBody) (.neg successorEqualityBody))) := by
  have hClosed : Derives intrinsic_zfc_theory []
      (((Formula.imp firstNaturalBody (.imp (.neg equalityBody) (.neg successorEqualityBody))).forallFreeTop SetSort.set).forallFreeTop SetSort.set) := by
    apply Completeness.strong_completeness PureRosserSchedule.source
    intro 𝒩 h𝒩
    simp only [Formula.TrueIn, Formula.satisfies_forallFreeTop, Formula.satisfies]
    intro right left
    change mem 𝒩 left (w 𝒩) → left ≠ right → suc 𝒩 left ≠ suc 𝒩 right
    intro hl hne heq
    exact hne (PureSourceCodingInversion.successor_injective h𝒩 hl heq)
  exact Derives.forall_elim_newest (Γ := []) (Derives.forall_elim_newest (Γ := []) hClosed)

theorem successor_inequality (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hProof : ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [first, second]])) :
    ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [PureSourceNumeralSyntax.next 𝒩 first, PureSourceNumeralSyntax.next 𝒩 second]]) := by
  have hValues := pair_numeralValues hl hr hf hs hFirst hSecond
  have hNat : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) firstNaturalBody) :=
    natural h𝒩 hl hf hFirst
  have h := values_modus_ponens (values := ObjectCodeInstantiation.prepend first (fun _ => second))
    h𝒩 (.neg equalityBody) (.neg successorEqualityBody) hValues hProof
    (values_modus_ponens (values := ObjectCodeInstantiation.prepend first (fun _ => second))
      h𝒩 firstNaturalBody (.imp (.neg equalityBody) (.neg successorEqualityBody)) hValues hNat
      (specialize_values h𝒩 _ successor_inequality_derives hValues))
  have hSymbol : node 𝒩 FunctionSymbol.successor.ctorIdx [] = numeral 𝒩 ObjectNumeralSyntax.successorSymbol :=
    PureSourceHornConstruction.node_numerals h𝒩 _ []
  change ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3
    [(node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), first]),
     (node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), second])]]) at h
  rw [hSymbol] at h
  exact h

/-- 零测试的既有负反射可与任意合法的零数码配对。 -/
theorem nonzero_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input named zeroNamed : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩)) (hz : mem 𝒩 zeroNamed (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named) (hZero : PureSourceNumeralSyntax.Graph 𝒩 (z 𝒩) zeroNamed)
    (hne : input ≠ z 𝒩) : ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [named, zeroNamed]]) := by
  have h := nonzero h𝒩 hi hn hg hne
  rw [(PureSourceNumeralSyntax.zero_iff h𝒩 hz).mp hZero]
  have hCode := tree_numeral h𝒩 (SyntaxEncode.term (numₘ(0) : SetOpenTerm []))
  change node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []] = numeral 𝒩 ObjectNumeralSyntax.zeroCode at hCode
  change ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [named, node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]]]) at h
  rwa [hCode] at h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
