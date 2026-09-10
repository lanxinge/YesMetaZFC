import YesMetaZFC.Automation.ObjectNumeralComparison
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralEqualityRules

/-! # 任意两个内部自然数的相等与不等反射

不等反射对第一个数作内部归纳，归纳性质全称量化第二个内部自然数及两个数码。
其实际对象公式先与最终纯扩张对应，再使用分离归纳；不需要外部良基性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity PureSourceNumerals
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem unequalAt_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (left right : SetTerm bound free) :
    (ObjectNumeralComparison.unequalAt ReducedProofPresentation.presentation.graph left right).satisfies env ↔
      ∀ first second, mem 𝒩 first (w 𝒩) → mem 𝒩 second (w 𝒩) →
        PureSourceNumeralSyntax.Graph 𝒩 (left.eval env) first → PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second →
        left.eval env ≠ right.eval env → ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [first, second]]) := by
  simp only [ObjectNumeralComparison.unequalAt, Formula.satisfies_forallFreeTop, Formula.satisfies,
    PureSourceNumeralSyntax.satisfies, provableCode_satisfies, node_eval, List.map_cons, List.map_nil,
    Term.eval_weakenFree, and_imp]
  rfl

theorem unequalAll_satisfies {bound free : SetContext} (env : Env 𝒩 bound free) (left : SetTerm bound free) :
    (ObjectNumeralComparison.unequalAll ReducedProofPresentation.presentation.graph left).satisfies env ↔
      ∀ right, mem 𝒩 right (w 𝒩) → ∀ first second, mem 𝒩 first (w 𝒩) → mem 𝒩 second (w 𝒩) →
        PureSourceNumeralSyntax.Graph 𝒩 (left.eval env) first → PureSourceNumeralSyntax.Graph 𝒩 right second →
        left.eval env ≠ right → ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [first, second]]) := by
  simp only [ObjectNumeralComparison.unequalAll, Formula.satisfies_forallFreeTop, Formula.satisfies,
    unequalAt_satisfies, Term.eval_weakenFree]
  rfl

theorem unequalAll_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left : 𝒩.Carrier .set} (hl : mem 𝒩 left (w 𝒩)) :
    (ObjectNumeralComparison.unequalAll ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons left .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectNumeralComparison.unequalAll ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons left .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [unequalAll_satisfies, unequalAll_satisfies]
  apply forall_congr'; intro right
  change (mem 𝒩 right (w 𝒩) → _) ↔ (mem 𝒩 right (w (canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro hr
  apply forall_congr'; intro first
  apply forall_congr'; intro second
  change (mem 𝒩 first (w 𝒩) → mem 𝒩 second (w 𝒩) → _) ↔
    (mem 𝒩 first (w 𝒩) → mem 𝒩 second (w 𝒩) → _)
  apply imp_congr_right; intro hf
  apply imp_congr_right; intro hs
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hl hf)
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hr hs)
  apply imp_congr_right; intro _
  have hEq : node 𝒩 3 [first, second] = node (canonical h𝒩) 3 [first, second] :=
    node_agrees h𝒩 3 (by simp [hf, hs])
  have hEqNat := node_natural h𝒩 3 (fields := [first, second]) (by simp [hf, hs])
  have hNeg : node 𝒩 4 [node 𝒩 3 [first, second]] = node (canonical h𝒩) 4 [node (canonical h𝒩) 3 [first, second]] := by
    rw [node_agrees h𝒩 4 (fields := [node 𝒩 3 [first, second]]) (by simp [hEqNat]), hEq]; rfl
  rw [← hNeg]
  exact PureSourceLocalTests.provableCode_agreement h𝒩 (node_natural h𝒩 4 (by simp [hEqNat]))

/-- 不同的内部自然数，其数码之间的不等式具有当前证明图接受的证明。 -/
theorem unequal (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right first second : 𝒩.Carrier .set}
    (hl : mem 𝒩 left (w 𝒩)) (hr : mem 𝒩 right (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 left first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 right second)
    (hUnequal : left ≠ right) : ProvableCode 𝒩 (node 𝒩 4 [node 𝒩 3 [first, second]]) := by
  have hAll := PureSourceInduction.induction h𝒩
    (ObjectNumeralComparison.unequalAll ReducedProofPresentation.presentation.graph (.fvar .here)) .nil
    (fun _ h => unequalAll_agrees h𝒩 h) (by
      apply (unequalAll_satisfies _ _).mpr
      intro right hr first second hf hs hFirst hSecond hne
      have h := nonzero_code h𝒩 hr hs hf hSecond hFirst (fun heq => hne heq.symm)
      exact inequality_symmetry h𝒩 hr (omega_closed h𝒩).1 hs hf hSecond hFirst h) (by
      intro left hl hProperty
      apply (unequalAll_satisfies _ _).mpr
      intro right hr first second hf hs hFirst hSecond hne
      obtain ⟨previous, hp, hPrevious, rfl⟩ := (PureSourceNumeralSyntax.successor_iff h𝒩 hl hf).mp hFirst
      rcases PureSourceNumeralSyntax.cases_graph h𝒩 hr hs hSecond with hZero | hSucc
      · rw [hZero.1] at hSecond hne
        exact nonzero_code h𝒩 ((omega_closed h𝒩).2 left hl)
          (PureSourceNumeralSyntax.next_natural h𝒩 hp) hs
          (PureSourceNumeralSyntax.successor h𝒩 hl hp hPrevious) hSecond hne
      · obtain ⟨predecessor, other, hPred, ho, hRight, rfl, hOther⟩ := hSucc
        have hDifferent : left ≠ predecessor := by
          intro heq
          apply hne
          rw [heq, hRight]; rfl
        have hPreviousProof := (unequalAll_satisfies _ _).mp hProperty
          predecessor hPred previous other hp ho hPrevious hOther hDifferent
        exact successor_inequality h𝒩 hl hPred hp ho hPrevious hOther hPreviousProof)
  exact (unequalAll_satisfies _ _).mp (hAll left hl) right hr first second hf hs hFirst hSecond hUnequal

/-- 统一不等式反射的实际对象闭句推导。 -/
theorem unequal_derives : Derives intrinsic_zfc_theory []
    ((((.fvar .here : SetOpenTerm [.set]) ∈ₘ ωₘ) ⟶ₘ
      ObjectNumeralComparison.unequalAll ReducedProofPresentation.presentation.graph (.fvar .here)).forallFreeTop SetSort.set) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  rw [Formula.TrueIn, Formula.satisfies_forallFreeTop]
  intro left
  change mem 𝒩 left (w 𝒩) → _
  intro hl
  apply (unequalAll_satisfies _ _).mpr
  intro right hr first second hf hs hFirst hSecond hne
  exact unequal h𝒩 hl hr hf hs hFirst hSecond hne

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
