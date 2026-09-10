import YesMetaZFC.Automation.ObjectNumeralSyntax
import YesMetaZFC.Automation.ObjectFormulaSyntax
import YesMetaZFC.Automation.ObjectSyntaxTransform

/-! # 当前数码图的对象语言总性与唯一性陈述

仅定义公式，不将这些性质加入公理或能力包；具体理论中的证明位于源模型层。
-/
namespace YesMetaZFC.Automation.ObjectNumeralSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def uniqueOutputCondition {bound free : SetContext} (input : SetTerm bound free) : SetFormula bound free :=
  let inputOne := input.weakenFree SetSort.set
  let output : SetTerm bound (.set :: free) := .fvar .here
  let other : SetTerm bound (.set :: .set :: free) := .fvar .here
  ((output ∈ₘ ωₘ) ∧ₘ (condition inputOne output ∧ₘ
    (((other ∈ₘ ωₘ) ∧ₘ condition (inputOne.weakenFree SetSort.set) other) ⟶ₘ
      (other ≐ₘ output.weakenFree SetSort.set)).forallFreeTop SetSort.set)).existsFreeTop SetSort.set

/-- 对所有内部自然数，当前 AST 数码图恰有一个自然数输出。 -/
def totalUnique : SetSentence :=
  (((.fvar .here : SetOpenTerm [.set]) ∈ₘ ωₘ) ⟶ₘ
    uniqueOutputCondition (.fvar .here)).forallFreeTop .set

/-- 使用实际逻辑公理检查器共享的完整语法规则表。 -/
def closedTermCondition {bound free : SetContext} (output : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition ObjectFormulaSyntax.rules (ProofT.IntrinsicQuotation.node 0 [numₘ(0), numₘ(0), output])

/-- 同一闭项数码在任意给定上下文长度下仍是合法项。 -/
def wellFormedAtCondition {bound free : SetContext}
    (input boundCount freeCount : SetTerm bound free) : SetFormula bound free :=
  let output : SetTerm bound (.set :: free) := .fvar .here
  (((output ∈ₘ ωₘ) ∧ₘ condition (input.weakenFree SetSort.set) output) ⟶ₘ
    ObjectHorn.condition ObjectFormulaSyntax.rules (ProofT.IntrinsicQuotation.node 0
      [boundCount.weakenFree SetSort.set, freeCount.weakenFree SetSort.set, output])).forallFreeTop SetSort.set

def wellFormedCondition {bound free : SetContext} (input : SetTerm bound free) : SetFormula bound free :=
  let output : SetTerm bound (.set :: free) := .fvar .here
  (((output ∈ₘ ωₘ) ∧ₘ condition (input.weakenFree SetSort.set) output) ⟶ₘ
    closedTermCondition output).forallFreeTop SetSort.set

/-- 任意上下文深度下，数码在四类变换中均保持原码。 -/
def invariantAtCondition {bound free : SetContext}
    (input mode depth parameter : SetTerm bound free) : SetFormula bound free :=
  let output : SetTerm bound (.set :: free) := .fvar .here
  (((output ∈ₘ ωₘ) ∧ₘ condition (input.weakenFree SetSort.set) output) ⟶ₘ
    ObjectHorn.condition ObjectSyntaxTransform.rules (ProofT.IntrinsicQuotation.node 1
      [mode.weakenFree SetSort.set, depth.weakenFree SetSort.set,
        parameter.weakenFree SetSort.set, output, output])).forallFreeTop SetSort.set

def wellFormed : SetSentence :=
  (((.fvar .here : SetOpenTerm [.set]) ∈ₘ ωₘ) ⟶ₘ
    wellFormedCondition (.fvar .here)).forallFreeTop .set

/-- 固定单自由变量公式在所有内部自然数上的数码代入存在性。 -/
def substitutionTotal (body : SetOpenFormula [.set]) : SetSentence :=
  let input : SetOpenTerm [.set,.set,.set] := .fvar (.there (.there .here))
  let named : SetOpenTerm [.set,.set,.set] := .fvar (.there .here)
  let output : SetOpenTerm [.set,.set,.set] := .fvar .here
  let quoted := (((ProofT.IntrinsicQuotation.quote body).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set
  let witnesses := ((named ∈ₘ ωₘ) ∧ₘ ((output ∈ₘ ωₘ) ∧ₘ (condition input named ∧ₘ
    (closedTermCondition named ∧ₘ ObjectSyntaxTransform.condition (numₘ(3)) (numₘ(0))
      (structural_list_code_term [named]) quoted output)))).existsFreeTop SetSort.set |>.existsFreeTop SetSort.set
  (((.fvar .here : SetOpenTerm [.set]) ∈ₘ ωₘ) ⟶ₘ witnesses).forallFreeTop SetSort.set

end YesMetaZFC.Automation.ObjectNumeralSyntax
