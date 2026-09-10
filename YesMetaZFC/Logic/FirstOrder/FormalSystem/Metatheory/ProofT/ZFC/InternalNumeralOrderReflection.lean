import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralOrderRules

/-! # 任意内部自然数严格序的正负反射

按右参数作可分离公式归纳。后继展开为严格序或等式；负方向同时消费已有的
不等式反射。整个构造保留原证明图，并覆盖非标准模型。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity PureSourceNumerals
open PureSourceInstantiation ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 30000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem orderAt_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (left right : SetTerm bound free) :
    (ObjectNumeralOrder.atPair ReducedProofPresentation.presentation.graph left right).satisfies env ↔
      ∀ first, mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (left.eval env) first →
      ∀ second, mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second →
        (mem 𝒩 (left.eval env) (right.eval env) → ProvableCode 𝒩 (orderCode 𝒩 first second)) ∧
        (¬ mem 𝒩 (left.eval env) (right.eval env) → ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first second])) := by
  simp only [ObjectNumeralOrder.atPair, forallNumeral_satisfies, signed_satisfies, membership_satisfies,
    formula_eval, Term.eval_weakenFree, ObjectNumeralReflection.map_prepend, orderCode]
  rfl

theorem orderAll_satisfies {bound free : SetContext} (env : Env 𝒩 bound free) (right : SetTerm bound free) :
    (ObjectNumeralOrder.atRight ReducedProofPresentation.presentation.graph right).satisfies env ↔
      ∀ left, mem 𝒩 left (w 𝒩) →
      ∀ first, mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 left first →
      ∀ second, mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second →
        (mem 𝒩 left (right.eval env) → ProvableCode 𝒩 (orderCode 𝒩 first second)) ∧
        (¬ mem 𝒩 left (right.eval env) → ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first second])) := by
  simp only [ObjectNumeralOrder.atRight, forallNatural_satisfies, orderAt_satisfies, Term.eval_weakenFree]
  rfl

theorem orderAll_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {right : 𝒩.Carrier .set} (hr : mem 𝒩 right (w 𝒩)) :
    (ObjectNumeralOrder.atRight ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons right .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectNumeralOrder.atRight ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons right .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [orderAll_satisfies, orderAll_satisfies]
  apply forall_congr'; intro left
  change (mem 𝒩 left (w 𝒩) → _) ↔ (mem 𝒩 left (w (canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro hl
  apply forall_congr'; intro first
  apply imp_congr_right; intro hf
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hl hf)
  apply forall_congr'; intro second
  apply imp_congr_right; intro hs
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hr hs)
  have hv : ∀ i, mem 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second) i) (w 𝒩) := by
    intro i; cases i <;> assumption
  have hc := formula_agrees h𝒩 hv orderBody
  have hn := formula_natural h𝒩 hv orderBody
  change orderCode 𝒩 first second = orderCode (canonical h𝒩) first second at hc
  change mem 𝒩 (orderCode 𝒩 first second) (w 𝒩) at hn
  have hneg : node 𝒩 4 [orderCode 𝒩 first second] = node (canonical h𝒩) 4 [orderCode (canonical h𝒩) first second] := by
    rw [node_agrees h𝒩 4 (by simp [hn]), hc]; rfl
  have hPos := (PureSourceLocalTests.provableCode_agreement h𝒩 hn).trans
    (iff_of_eq (congrArg (fun code : 𝒩.Carrier .set => ProvableCode (canonical h𝒩) code) hc))
  have hNeg := (PureSourceLocalTests.provableCode_agreement h𝒩 (node_natural h𝒩 4 (by simp [hn]))).trans
    (iff_of_eq (congrArg (fun code : 𝒩.Carrier .set => ProvableCode (canonical h𝒩) code) hneg))
  exact and_congr (imp_congr Iff.rfl hPos) (imp_congr Iff.rfl hNeg)

/-- 严格序及其否定均有原证明谓词接受的数码实例证明。 -/
theorem order (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second) :
    (mem 𝒩 left right → ProvableCode 𝒩 (orderCode 𝒩 first second)) ∧
    (¬ mem 𝒩 left right → ProvableCode 𝒩 (node 𝒩 4 [orderCode 𝒩 first second])) := by
  have hAll := PureSourceInduction.induction h𝒩
    (ObjectNumeralOrder.atRight ReducedProofPresentation.presentation.graph (.fvar .here)) .nil
    (fun _ h => orderAll_agrees h𝒩 h) (by
      apply (orderAll_satisfies _ _).mpr
      intro left hl first hf hFirst second hs hSecond
      exact ⟨fun h => False.elim (empty_spec h𝒩 left h), fun _ => order_zero h𝒩 hl hf hs hFirst hSecond⟩) (by
      intro right hr hProperty
      apply (orderAll_satisfies _ _).mpr
      intro left hl first hf hFirst second hs hSecond
      obtain ⟨previous, hp, hPrevious, rfl⟩ := (PureSourceNumeralSyntax.successor_iff h𝒩 hr hs).mp hSecond
      have ih := (orderAll_satisfies _ _).mp hProperty left hl first hf hFirst previous hp hPrevious
      constructor
      · intro h
        apply order_successor h𝒩 hl hr hf hp hFirst hPrevious
        rcases (successor_spec h𝒩 right left).mp h with h | h
        · exact Or.inl (ih.1 h)
        · exact Or.inr (equal h𝒩 hl hf hp hFirst hPrevious h)
      · intro h
        have hm : ¬ mem 𝒩 left right := fun hm => h ((successor_spec h𝒩 right left).mpr (Or.inl hm))
        have he : left ≠ right := fun he => h ((successor_spec h𝒩 right left).mpr (Or.inr he))
        exact not_order_successor h𝒩 hl hr hf hp hFirst hPrevious (ih.2 hm)
          (unequal h𝒩 hl hr hf hp hFirst hPrevious he))
  exact (orderAll_satisfies _ _).mp (hAll right hr) left hl first hf hFirst second hs hSecond

/-- 自然数的非严格序按既定表示 x∈S(y) 反射，包含其否定。 -/
theorem weak_order (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second) :
    (mem 𝒩 left (suc 𝒩 right) → ProvableCode 𝒩
      (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) successorOrderBody)) ∧
    (¬ mem 𝒩 left (suc 𝒩 right) → ProvableCode 𝒩
      (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) (.neg successorOrderBody))) := by
  have h := order h𝒩 hl ((omega_closed h𝒩).2 right hr) hf (PureSourceNumeralSyntax.next_natural h𝒩 hs)
    hFirst (PureSourceNumeralSyntax.successor h𝒩 hr hs hSecond)
  have hShape : formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) successorOrderBody =
      orderCode 𝒩 first (PureSourceNumeralSyntax.next 𝒩 second) := by
    change orderCode 𝒩 first (node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), second]) = _
    rw [successor_symbol h𝒩]; rfl
  change (_ → ProvableCode 𝒩 _) ∧ (_ → ProvableCode 𝒩 (node 𝒩 4 [formula 𝒩 _ successorOrderBody]))
  rw [hShape]
  exact h

theorem order_derives : Derives intrinsic_zfc_theory []
    (ObjectNumeralReflection.forallNatural
      (ObjectNumeralOrder.atRight ReducedProofPresentation.presentation.graph (.fvar .here)) : SetSentence) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  apply (forallNatural_satisfies _ _).mpr
  intro right hr
  apply (orderAll_satisfies _ _).mpr
  intro left hl first hf hFirst second hs hSecond
  exact order h𝒩 hl hr hf hs hFirst hSecond

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
