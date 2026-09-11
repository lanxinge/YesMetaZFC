import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSpaceSemantics

/-!
# 内在有限序列的最小公理联合

本模块只组合有限序列图、函数求值和有限序列空间消费者实际读取的定义合同。
它不恢复旧的 `standard_sequence_semantics_theory`，也不把无穷、自然数上界或
quotation 作为有限序列核心的隐含前提。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory

set_option autoImplicit false

def finite_sequence_support_theory : SetTheory :=
  Theory.union membership_irreflexive_theory <|
    Theory.union empty_set_symbol_theory <|
      Theory.union successor_operator_theory <|
        Theory.union binary_union_operator_theory <|
          Theory.union ordered_pair_operator_theory <|
            Theory.union function_application_theory <|
              Theory.union finite_sequence_flatten_theory
                finite_sequence_space_theory

namespace finite_sequence_support_theory

derive_theory_subset membership_irreflexive_theory ⊆ finite_sequence_support_theory => contains_membership_irreflexive

derive_theory_subset empty_set_symbol_theory ⊆ finite_sequence_support_theory => contains_empty_set_symbol

derive_theory_subset successor_operator_theory ⊆ finite_sequence_support_theory => contains_successor

derive_theory_subset binary_union_operator_theory ⊆ finite_sequence_support_theory => contains_binary_union

derive_theory_subset ordered_pair_operator_theory ⊆ finite_sequence_support_theory => contains_ordered_pair

derive_theory_subset function_application_theory ⊆ finite_sequence_support_theory => contains_function_application

derive_theory_subset function_predicate_theory ⊆ finite_sequence_support_theory => contains_function_predicate

derive_theory_subset finite_sequence_flatten_theory ⊆ finite_sequence_support_theory => contains_finite_sequence_flatten

derive_theory_subset finite_sequence_concatenation_theory ⊆ finite_sequence_support_theory => contains_finite_sequence_concatenation

derive_theory_subset finite_sequence_formal_system_theory ⊆ finite_sequence_support_theory => contains_finite_sequence_formal_system

derive_theory_subset finite_sequence_space_theory ⊆ finite_sequence_support_theory => contains_finite_sequence_space

derive_theory_subset nonempty_finite_sequence_space_theory ⊆ finite_sequence_support_theory => contains_nonempty_finite_sequence_space

end finite_sequence_support_theory

open finite_sequence_support_theory in
/-- 最小有限序列支撑理论的规范支撑实例。 -/
theorem finite_sequence_support_instance :
    FiniteSequenceSpaceSupport finite_sequence_support_theory where
  contains_membership_irreflexive := contains_membership_irreflexive
  contains_empty_set := contains_empty_set_symbol
  contains_successor := contains_successor
  contains_binary_union := contains_binary_union
  contains_ordered_pair := contains_ordered_pair
  contains_function_predicate := contains_function_predicate
  contains_finite_sequence_concatenation := contains_finite_sequence_concatenation
  contains_function_application := contains_function_application
  contains_finite_sequence_formal_system := contains_finite_sequence_formal_system
  contains_finite_sequence_space := contains_finite_sequence_space
  contains_nonempty_finite_sequence_space := contains_nonempty_finite_sequence_space

/-- 任意包含最小支撑理论的对象理论直接获得有限序列空间支撑。 -/
theorem finite_sequence_space_support_of_extends
    {T : SetTheory}
    (hT : Theory.Extends T finite_sequence_support_theory) :
    FiniteSequenceSpaceSupport T :=
  finite_sequence_support_instance.theory_weaken hT

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
