import YesMetaZFC.Automation.ObjectNumeralOrder
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralQuantifiers

/-! # 隶属空集及隶属后继的实际数码证明构造 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity PureSourceNumerals
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

abbrev orderBody := ObjectNumeralOrder.body
def successorOrderBody : SetOpenFormula [.set,.set] := (.fvar .here) ∈ₘ Sₘ(.fvar (.there .here))
def orderCode (𝒩 : Structure.{0,0,0,x} signature) (first second : 𝒩.Carrier .set) :=
  formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) orderBody

theorem successor_symbol (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    node 𝒩 FunctionSymbol.successor.ctorIdx [] = numeral 𝒩 ObjectNumeralSyntax.successorSymbol :=
  PureSourceHornConstruction.node_numerals h𝒩 _ []

theorem order_zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left first second : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first)
    (hSecond : PureSourceNumeralSyntax.Graph 𝒩 (z 𝒩) second) :
    ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first second]) := by
  have hRule : Derives intrinsic_zfc_theory [] (¬ₘ ((.fvar .here : SetOpenTerm [.set]) ∈ₘ ∅ₘ)) := by
    apply source_complete
    intro 𝒩 h𝒩 env
    exact empty_spec h𝒩 _
  have h := specialize h𝒩 _ hRule hl hf hFirst
  have hZero := tree_numeral h𝒩 (SyntaxEncode.term (numₘ(0) : SetOpenTerm []))
  change node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []] = numeral 𝒩 ObjectNumeralSyntax.zeroCode at hZero
  change ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []])]) at h
  rw [hZero] at h
  rwa [(PureSourceNumeralSyntax.zero_iff h𝒩 hs).mp hSecond]

theorem order_successor_derives : Derives intrinsic_zfc_theory []
    (.imp (.disj orderBody equalityBody) successorOrderBody) := by
  apply source_complete
  intro 𝒩 h𝒩 env
  exact (successor_spec h𝒩 _ _).mpr

theorem not_order_successor_derives : Derives intrinsic_zfc_theory []
    (.imp (.neg orderBody) (.imp (.neg equalityBody) (.neg successorOrderBody))) := by
  apply source_complete
  intro 𝒩 h𝒩 env hm he hs
  exact ((successor_spec h𝒩 _ _).mp hs).elim hm he

/-- 正后继步允许已有的严格序证明或等式证明。 -/
theorem order_successor (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hProof : ProvableCode 𝒩 (orderCode 𝒩 first second) ∨ ProvableCode 𝒩 (node 𝒩 3 [first, second])) :
    ProvableCode 𝒩 (orderCode 𝒩 first (PureSourceNumeralSyntax.next 𝒩 second)) := by
  let values := ObjectCodeInstantiation.prepend first (fun _ => second)
  have hv := pair_numeralValues hl hr hf hs hFirst hSecond
  have hOr : ProvableCode 𝒩 (formula 𝒩 values (.disj orderBody equalityBody)) := by
    rcases hProof with h | h
    · exact values_modus_ponens (values := values) h𝒩 orderBody (.disj orderBody equalityBody) hv h (specialize_values h𝒩 _
        (source_complete (.imp orderBody (.disj orderBody equalityBody)) (fun _ _ _ h => Or.inl h)) hv)
    · exact values_modus_ponens (values := values) h𝒩 equalityBody (.disj orderBody equalityBody) hv h (specialize_values h𝒩 _
        (source_complete (.imp equalityBody (.disj orderBody equalityBody)) (fun _ _ _ h => Or.inr h)) hv)
  have h := values_modus_ponens (values := values) h𝒩 _ _ hv hOr
    (specialize_values h𝒩 _ order_successor_derives hv)
  change ProvableCode 𝒩 (orderCode 𝒩 first (node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), second])) at h
  rwa [successor_symbol h𝒩] at h

theorem not_order_successor (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hOrder : ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first second]))
    (hEqual : ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [first, second]])) :
    ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first (PureSourceNumeralSyntax.next 𝒩 second)]) := by
  let values := ObjectCodeInstantiation.prepend first (fun _ => second)
  have hv := pair_numeralValues hl hr hf hs hFirst hSecond
  have h := values_modus_ponens (values := values) h𝒩 (.neg equalityBody) (.neg successorOrderBody) hv hEqual
    (values_modus_ponens (values := values) h𝒩 (.neg orderBody) _ hv hOrder
      (specialize_values h𝒩 _ not_order_successor_derives hv))
  change ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first (node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), second])]) at h
  rwa [successor_symbol h𝒩] at h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
