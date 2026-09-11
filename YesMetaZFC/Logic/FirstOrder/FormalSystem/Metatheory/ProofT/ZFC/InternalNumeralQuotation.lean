import YesMetaZFC.Model.ZFC.Pure.PureSourceNumeralTotality
import YesMetaZFC.Model.ZFC.Pure.PureSourceTermConstruction

/-! # 任意内部自然数的唯一合法闭项数码

证书进入当前逻辑公理检查器使用的完整语法图。这里完成数码命名与良构性，
尚未构造可证明性断言的内部证明，不将本结果称为第三可导性条件。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open PureSourceHorn PureSourceHornConstruction PureSourceTermConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def ClosedTerm (𝒩 : Structure.{0,0,0,x} signature) (output : 𝒩.Carrier .set) : Prop :=
  TermGraph ObjectFormulaSyntax.rules (z 𝒩) (z 𝒩) output

theorem closedTerm_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (output : SetTerm bound free) :
    (ObjectNumeralSyntax.closedTermCondition output).satisfies env ↔ ClosedTerm 𝒩 (output.eval env) := by
  simp only [ObjectNumeralSyntax.closedTermCondition, ObjectHorn.condition, ObjectTrace.condition_satisfies,
    node_eval, List.map_cons, List.map_nil, numeral_eval]
  rfl

private theorem syntax_support : Supports ObjectFormulaSyntax.rules :=
  fun _ h => List.mem_append_left _ h

theorem zero_term (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩)) :
    TermGraph ObjectFormulaSyntax.rules bound free (numeral 𝒩 ObjectNumeralSyntax.zeroCode) := by
  have h := application h𝒩 syntax_support hBound hFree
    .emptySet [] (by intro field hf; cases hf)
    (arguments_nil h𝒩 syntax_support hBound hFree)
  have hSymbol : node 𝒩 FunctionSymbol.emptySet.ctorIdx [] =
      numeral 𝒩 (ObjectHorn.nodeValue FunctionSymbol.emptySet.ctorIdx []) := node_numerals h𝒩 _ []
  rw [hSymbol] at h
  have hCode := node_numerals h𝒩 2 [ObjectHorn.nodeValue FunctionSymbol.emptySet.ctorIdx []]
  change node 𝒩 2 [numeral 𝒩 (ObjectHorn.nodeValue FunctionSymbol.emptySet.ctorIdx [])] =
    numeral 𝒩 ObjectNumeralSyntax.zeroCode at hCode
  rw [hCode] at h
  exact h

theorem successor_term (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    {output : 𝒩.Carrier .set} (hOutput : mem 𝒩 output (w 𝒩)) (hTerm : TermGraph ObjectFormulaSyntax.rules bound free output) :
    TermGraph ObjectFormulaSyntax.rules bound free (next 𝒩 output) := by
  have hArgs := arguments_list h𝒩 syntax_support hBound hFree
    [output] (by simpa only [List.mem_singleton, forall_eq] using! hOutput)
    (by simpa only [List.mem_singleton, forall_eq] using! hTerm)
  have h := application h𝒩 syntax_support hBound hFree .successor [output]
    (by simpa only [List.mem_singleton, forall_eq] using! hOutput) hArgs
  have hSymbol : node 𝒩 FunctionSymbol.successor.ctorIdx [] =
      numeral 𝒩 ObjectNumeralSyntax.successorSymbol := node_numerals h𝒩 _ []
  rw [hSymbol] at h
  exact h

theorem zero_closedTerm (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    ClosedTerm 𝒩 (numeral 𝒩 ObjectNumeralSyntax.zeroCode) :=
  zero_term h𝒩 (omega_closed h𝒩).1 (omega_closed h𝒩).1

theorem successor_closedTerm (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {output : 𝒩.Carrier .set} (hOutput : mem 𝒩 output (w 𝒩)) (hTerm : ClosedTerm 𝒩 output) :
    ClosedTerm 𝒩 (next 𝒩 output) :=
  successor_term h𝒩 (omega_closed h𝒩).1 (omega_closed h𝒩).1 hOutput hTerm

theorem closedTerm_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {output : 𝒩.Carrier .set} (hOutput : mem 𝒩 output (w 𝒩)) :
    ClosedTerm 𝒩 output ↔ ClosedTerm (canonical h𝒩) output := by
  have h := term_agrees h𝒩 ObjectFormulaSyntax.rules (omega_closed h𝒩).1 (omega_closed h𝒩).1 hOutput
  simpa only [ClosedTerm, empty_agrees h𝒩] using! h

theorem wellFormedAt_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (input b f : SetTerm bound free) :
    (ObjectNumeralSyntax.wellFormedAtCondition input b f).satisfies env ↔
      ∀ output, mem 𝒩 output (w 𝒩) → Graph 𝒩 (input.eval env) output →
        TermGraph ObjectFormulaSyntax.rules (b.eval env) (f.eval env) output := by
  simp only [ObjectNumeralSyntax.wellFormedAtCondition, Formula.satisfies_forallFreeTop,
    Formula.satisfies, satisfies, term_satisfies, Term.eval_weakenFree, and_imp]
  rfl

theorem wellFormed_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (input : SetTerm bound free) :
    (ObjectNumeralSyntax.wellFormedCondition input).satisfies env ↔
      ∀ output, mem 𝒩 output (w 𝒩) → Graph 𝒩 (input.eval env) output → ClosedTerm 𝒩 output := by
  simp only [ObjectNumeralSyntax.wellFormedCondition, Formula.satisfies_forallFreeTop,
    Formula.satisfies, satisfies, closedTerm_satisfies, Term.eval_weakenFree, and_imp]
  rfl

/-- 用带上下文参数的实际对象公式归纳，数码在所有内部上下文长度下均合法。 -/
theorem graph_term (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free input output : 𝒩.Carrier .set}
    (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (hInput : mem 𝒩 input (w 𝒩)) (hOutput : mem 𝒩 output (w 𝒩)) (hGraph : Graph 𝒩 input output) :
    TermGraph ObjectFormulaSyntax.rules bound free output := by
  have hAll := PureSourceInduction.induction h𝒩
    (ObjectNumeralSyntax.wellFormedAtCondition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))
    (.cons bound (.cons free .nil)) (by
      intro input hInput
      rw [wellFormedAt_satisfies, wellFormedAt_satisfies]
      apply forall_congr'
      intro output
      change (mem 𝒩 output (w 𝒩) → _) ↔ (mem 𝒩 output (w (canonical h𝒩)) → _)
      rw [← omega_agrees h𝒩]
      apply imp_congr_right
      intro hOutput
      exact imp_congr (agrees h𝒩 hInput hOutput) (term_agrees h𝒩 ObjectFormulaSyntax.rules hBound hFree hOutput)) (by
      apply (wellFormedAt_satisfies _ _ _ _).mpr
      intro output hOutput hGraph
      have hEqual := (zero_iff h𝒩 hOutput).mp hGraph
      exact hEqual.symm ▸ zero_term h𝒩 hBound hFree) (by
      intro input hInput hProperty
      apply (wellFormedAt_satisfies _ _ _ _).mpr
      intro output hOutput hGraph
      obtain ⟨previous, hp, hPrevious, rfl⟩ := (successor_iff h𝒩 hInput hOutput).mp hGraph
      exact successor_term h𝒩 hBound hFree hp ((wellFormedAt_satisfies _ _ _ _).mp hProperty previous hp hPrevious))
  exact (wellFormedAt_satisfies _ _ _ _).mp (hAll input hInput) output hOutput hGraph

/-- 数码图的所有自然数输出均通过实际闭项语法检查，包括非标准输出。 -/
theorem graph_closedTerm (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩))
    (hOutput : mem 𝒩 output (w 𝒩)) (hGraph : Graph 𝒩 input output) : ClosedTerm 𝒩 output :=
  graph_term h𝒩 (omega_closed h𝒩).1 (omega_closed h𝒩).1 hInput hOutput hGraph

theorem wellFormed_derives : Derives intrinsic_zfc_theory [] ObjectNumeralSyntax.wellFormed := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  simp only [ObjectNumeralSyntax.wellFormed, Formula.TrueIn, Formula.satisfies_forallFreeTop,
    Formula.satisfies]
  intro input hInput
  exact (wellFormed_satisfies _ _).mpr (fun _ hOutput hGraph => graph_closedTerm h𝒩 hInput hOutput hGraph)

/-- 为后续内部证明构造提供同一个唯一数码及其闭项证书。 -/
theorem quotation_exists_unique (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) :
    ∃ output, mem 𝒩 output (w 𝒩) ∧ Graph 𝒩 input output ∧ ClosedTerm 𝒩 output ∧
      ∀ other, mem 𝒩 other (w 𝒩) → Graph 𝒩 input other → other = output := by
  obtain ⟨output, hOutput, hGraph, hUnique⟩ := exists_unique h𝒩 hInput
  exact ⟨output, hOutput, hGraph, graph_closedTerm h𝒩 hInput hOutput hGraph, hUnique⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
