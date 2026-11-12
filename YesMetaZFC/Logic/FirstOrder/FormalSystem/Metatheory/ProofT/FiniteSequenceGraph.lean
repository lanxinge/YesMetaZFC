import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.FiniteSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core

/-!
# 有限序列图的内在基础

有限序列图直接由外部 `List` 递归生成对象项。项和公式的排序、bound 上下文以及
free 上下文全部由类型携带；本模块不再引入 Token、`Admissible` 或裸变量编号。
对象侧的定义合同由 `FiniteSequenceConcatenation` 提供，本模块只声明下游反演所需的
最小理论接口，并提供可计算的有限图构造。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 有限序列图只需要的对象理论合同。 -/
structure FiniteSequenceGraphSupport (T : SetTheory)
    extends ArithmeticSupport T where
  contains_binary_union :
    ∀ {sentence}, binary_union_operator_theory sentence → T sentence
  contains_ordered_pair :
    ∀ {sentence}, ordered_pair_operator_theory sentence → T sentence
  contains_function_predicate :
    ∀ {sentence}, function_predicate_theory sentence → T sentence
  contains_finite_sequence_concatenation :
    ∀ {sentence}, finite_sequence_concatenation_theory sentence → T sentence

/-- 需要函数求值时的有限序列扩展合同。 -/
structure FiniteSequenceEvaluationSupport (T : SetTheory)
    extends FiniteSequenceGraphSupport T where
  contains_function_application :
    ∀ {sentence}, function_application_theory sentence → T sentence
  contains_finite_sequence_formal_system :
    ∀ {sentence}, finite_sequence_formal_system_theory sentence → T sentence

/-- 有限图项满足函数图与递归构造相等的对象条件。 -/
def finite_sequence_graph_condition {bound free : SetContext}
    (start : Nat) (elements : List (SetTerm bound free))
    (graph : SetTerm bound free) : SetFormula bound free :=
  finite_sequence_condition graph ∧ₘ
    (graph ≐ₘ standard_sequence_from start elements)

/-- 有限图中元素成员的直接对象条件。 -/
def finite_sequence_graph_member_condition {bound free : SetContext}
    (start : Nat) (elements : List (SetTerm bound free))
    (member : SetTerm bound free) : SetFormula bound free :=
  member ∈ₘ standard_sequence_from start elements

/-- 图条件的固定点实例，供下游按需要追加定义合同。 -/
def finite_sequence_graph_definition_instance {bound free : SetContext}
    (start : Nat) (elements : List (SetTerm bound free))
    (graph : SetTerm bound free) : SetFormula bound free :=
  (graph ≐ₘ standard_sequence_from start elements) ↔ₘ
    finite_sequence_graph_condition start elements graph

namespace FiniteSequenceGraphSupport

/-- 有限序列图支撑沿理论包含直接提升。 -/
theorem theory_weaken
    {T U : SetTheory}
    (S : FiniteSequenceGraphSupport T)
    (hTU : Theory.Extends U T) :
    FiniteSequenceGraphSupport U where
  toArithmeticSupport := S.toArithmeticSupport.theory_weaken hTU
  contains_binary_union := fun hSentence =>
    hTU (S.contains_binary_union hSentence)
  contains_ordered_pair := fun hSentence =>
    hTU (S.contains_ordered_pair hSentence)
  contains_function_predicate := fun hSentence =>
    hTU (S.contains_function_predicate hSentence)
  contains_finite_sequence_concatenation := fun hSentence =>
    hTU (S.contains_finite_sequence_concatenation hSentence)

theorem weaken_finite_sequence_concatenation
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {sentence : SetSentence}
    (hSentence : finite_sequence_concatenation_theory sentence) :
    T sentence :=
  S.contains_finite_sequence_concatenation hSentence

theorem weaken_finite_sequence_formal_system
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
  {sentence : SetSentence}
    (hSentence : finite_sequence_formal_system_theory sentence) :
    T sentence :=
  S.contains_finite_sequence_formal_system hSentence

end FiniteSequenceGraphSupport

namespace FiniteSequenceEvaluationSupport

/-- 有限序列求值支撑沿理论包含直接提升。 -/
theorem theory_weaken
    {T U : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    (hTU : Theory.Extends U T) :
    FiniteSequenceEvaluationSupport U where
  toFiniteSequenceGraphSupport :=
    S.toFiniteSequenceGraphSupport.theory_weaken hTU
  contains_function_application := fun hSentence =>
    hTU (S.contains_function_application hSentence)
  contains_finite_sequence_formal_system := fun hSentence =>
    hTU (S.contains_finite_sequence_formal_system hSentence)

end FiniteSequenceEvaluationSupport

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
