import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureNumeralFormula
import YesMetaZFC.Automation.ObjectMinimumSemantics

/-! # 最终纯公式的自编码图

输入为绑定正文码 n，输出为 ∃x(Nₙ(x) ∧ 正文) 的完整 AST 码。
递推图的最小见证排除任意模型中的伪输出，之后才消去支撑符号。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureDiagonalGraph
open Nonlogical.BasicSetTheory PureOpenTransfer PureQuotation
open _root_.YesMetaZFC.Automation ObjectHorn RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureCompletedStage.interpretation
universe x

def numeralGraph_m : FormulaTemplate.Binary where
  body := ObjectExpressionIteration.condition_m zeroCode_m numeralStep_m (.fvar .here) (.fvar (.there .here))

@[simp] theorem numeralGraph_apply_m {bound free : SetContext} (input output : SetTerm bound free) :
    numeralGraph_m input output = ObjectExpressionIteration.condition_m zeroCode_m numeralStep_m input output := by
  simp [numeralGraph_m, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem numeral_positive_m (n : Nat) :
    Derives intrinsic_zfc_theory [] (numeralGraph_m (numₘ(n)) (numₘ(numeralCode_m n) : SetTerm [] [])) := by
  rw [numeralGraph_apply_m]
  exact ObjectExpressionIteration.positive_m ReducedRosser.diagonalSupport.certificate
    ReducedRosser.diagonalSupport.sequences ReducedRosser.diagonalSupport.power
    ReducedRosser.diagonalSupport.infinity zeroCode_m numeralStep_m numeralStep_variable_m n

theorem numeral_negative_m (n k : Nat) (h : numeralCode_m n ≠ k) :
    Derives intrinsic_zfc_theory [] (.neg (numeralGraph_m (numₘ(n)) (numₘ(k) : SetTerm [] []))) := by
  rw [numeralGraph_apply_m]
  exact ObjectExpressionIteration.negative_m ReducedRosser.diagonalSupport.certificate
    ReducedRosser.diagonalSupport.sequences.toArithmeticSupport zeroCode_m numeralStep_m numeralStep_variable_m n k h

def outputExpr_m : Expr 2 := .node (.literal 10) [.node (.literal 5) [.var 1, .var 0]]

def condition_m {bound free : SetContext} (input output : SetTerm bound free) : SetFormula bound free :=
  .existsE SetSort.set (.conj
    (ObjectMinimumSemantics.minimum_m ReducedRosser.diagonalSupport.core.code_domain numeralGraph_m
      (input.weakenBound SetSort.set) (.bvar .here))
    (.equal (output.weakenBound SetSort.set)
      (outputExpr_m.term (fun i : Fin 2 => [input.weakenBound SetSort.set, .bvar .here][i]))))

@[simp] theorem condition_substituteMapped_m {sb sf tb tf : SetContext} (input output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition_m input output).substituteMapped bs fs =
      condition_m (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp only [condition_m, Formula.substituteMapped, FormulaTemplate.apply_two_substituteMapped,
    Term.substituteMapped_weakenBound, Expr.term_substituteMapped]
  congr 4
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simp
  · rfl

def graph_m : FormulaTemplate.Binary where
  body := condition_m (.fvar .here) (.fvar (.there .here))

@[simp] theorem graph_apply_m {bound free : SetContext} (input output : SetTerm bound free) :
    graph_m input output = condition_m input output := by
  simp [graph_m, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

private theorem expression_value_m {𝒩 : Structure.{0,0,0,x} signature}
    (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {bound free : SetContext}
    (env : Env 𝒩 bound free) {arity : Nat} (e : Expr arity)
    (terms : Fin arity → SetTerm bound free) (values : Fin arity → Nat)
    (ht : ∀ i, (terms i).eval env = ObjectMinimumSemantics.number_m 𝒩 (values i)) :
    (e.term terms).eval env = ObjectMinimumSemantics.number_m 𝒩 (e.eval values) := by
  rw [ObjectHornSemantics.expr_eval]
  have he : (fun i => (terms i).eval env) =
      (fun i => ObjectMinimumSemantics.number_m 𝒩 (values i)) := funext ht
  rw [he]
  have h := (e.evaluate ReducedRosser.diagonalSupport.certificate values).sound h𝒩
    (Env.empty : Env 𝒩 [] []) (by intro φ hφ; cases hφ)
  simpa only [Formula.satisfies, ObjectHornSemantics.expr_eval] using h

theorem source_satisfies_m {𝒩 : Structure.{0,0,0,x} signature}
    (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {bound free : SetContext}
    (env : Env 𝒩 bound free) (input output : SetTerm bound free) (n : Nat)
    (hi : input.eval env = ObjectMinimumSemantics.number_m 𝒩 n) :
    (graph_m input output).satisfies env ↔
      output.eval env = ObjectMinimumSemantics.number_m 𝒩 (diagonalValue_m n) := by
  rw [graph_apply_m]
  change (∃ a, (ObjectMinimumSemantics.minimum_m ReducedRosser.diagonalSupport.core.code_domain numeralGraph_m
      (input.weakenBound SetSort.set) (.bvar .here)).satisfies (env.pushBound a) ∧
    (output.weakenBound SetSort.set).eval (env.pushBound a) =
      (outputExpr_m.term (fun i : Fin 2 => [input.weakenBound SetSort.set, .bvar .here][i])).eval (env.pushBound a)) ↔ _
  have hm (a : 𝒩.Carrier SetSort.set) := ObjectMinimumSemantics.satisfies_m
    ReducedRosser.diagonalSupport numeralGraph_m numeralCode_m numeral_positive_m numeral_negative_m
    h𝒩 (env.pushBound a) (input.weakenBound SetSort.set) (.bvar .here) n
    ((Term.eval_weakenBound env a input).trans hi)
  simp only [hm, Term.eval_weakenBound]
  change (∃ a, a = ObjectMinimumSemantics.number_m 𝒩 (numeralCode_m n) ∧ _) ↔ _
  rw [exists_eq_left]
  have he := expression_value_m h𝒩 (env.pushBound (ObjectMinimumSemantics.number_m 𝒩 (numeralCode_m n)))
    outputExpr_m (fun i : Fin 2 => [input.weakenBound SetSort.set, .bvar .here][i])
    (fun i : Fin 2 => [n, numeralCode_m n][i]) (by
      intro i
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · exact (Term.eval_weakenBound env _ input).trans hi
      · rfl)
  rw [he]
  rfl

noncomputable def pureGraph_m : OpenFormula ℒ (pureContext_m [SetSort.set, SetSort.set]) :=
  translate_m graph_m.body

noncomputable def apply_m {bound free : SortContext ℒ}
    (input output : Term ℒ bound free PureModel.setSort) : Formula ℒ bound free :=
  applyTemplate pureGraph_m (.cons input (.cons output .nil))

theorem satisfies_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    {bound free : SortContext ℒ} (env : Env ℳ bound free)
    (input output : Term ℒ bound free PureModel.setSort) (n : Nat)
    (hi : input.eval env = number_m hℳ n) :
    (apply_m input output).satisfies env ↔ output.eval env = number_m hℳ (diagonalValue_m n) := by
  rw [apply_m, applyTemplate_satisfies, pureGraph_m, translate_satisfies_m hℳ]
  let e := sourceEnv_m hℳ (parameters := [SetSort.set, SetSort.set]) (templateEnv (.cons (input.eval env) (.cons (output.eval env) .nil)))
  have h := source_satisfies_m (PureZFCModels.models hℳ) e
    (.fvar .here) (.fvar (.there .here)) n hi
  rw [graph_apply_m] at h
  exact h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureDiagonalGraph
