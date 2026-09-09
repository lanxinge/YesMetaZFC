import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.TransformStructuralCorrectness

/-!
# 公式语法变换的公共结构正确性

五种 Hilbert 公式构造节点只依赖统一语法变换关系本身，与具体宿主变换无关。
本模块把这些机械 shape 证明集中一次，具体变换层只保留 scope 与宿主递归交换律。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace QuineEncoding

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols

set_option autoImplicit false

theorem formula_transform_binary_shape
    (operation : SyntaxTransformOperation)
    (variableIndex replacement : SetOpenTerm [])
    (tag : StructuralCodeTag)
    (hTag : tag = .equality ∨ tag = .membership)
    (depth sourceLeft sourceRight targetLeft targetRight : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term operation,
        depth, variableIndex, replacement, sourceLeft, targetLeft))
    (hRight : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .term,
        syntax_transform_operation_term operation,
        depth, variableIndex, replacement, sourceRight, targetRight)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (structural_node_code_term tag [sourceLeft, sourceRight])
        (structural_node_code_term tag [targetLeft, targetRight]) := by
  have hBranch : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      binary_formula_transform_condition tag
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (structural_node_code_term tag [sourceLeft, sourceRight])
        (structural_node_code_term tag [targetLeft, targetRight]) := by
    dsimp [binary_formula_transform_condition]
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetRight (.cons targetLeft (.cons sourceRight (.cons sourceLeft .nil))))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
      Formula.substituteFree, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term, term_weaken_free_four] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (structural_node_code_term tag
              [sourceLeft, sourceRight] : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (structural_node_code_term tag
              [targetLeft, targetRight] : SetOpenTerm [])))
        (FirstOrder.Derives.conj_intro hLeft hRight)
  dsimp [syntax_transform_shape_condition, formula_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .formula : SetOpenTerm [])
  · rcases hTag with rfl | rfl
    · exact FirstOrder.Derives.disj_intro_left hBranch
    · exact FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_left hBranch)

theorem formula_transform_predicate_shape
    (operation : SyntaxTransformOperation)
    (variableIndex replacement : SetOpenTerm [])
    (depth arity symbol sourceArguments targetArguments : SetOpenTerm [])
    (hArity : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      arity ∈ₘ ωₘ)
    (hSymbol : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      symbol ∈ₘ ωₘ)
    (hArguments : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .termList,
        syntax_transform_operation_term operation,
        depth, variableIndex, replacement, sourceArguments, targetArguments)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (pred_codeₘ(arity, symbol, sourceArguments))
        (pred_codeₘ(arity, symbol, targetArguments)) := by
  have hBranch : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      predicate_formula_transform_condition
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (pred_codeₘ(arity, symbol, sourceArguments))
        (pred_codeₘ(arity, symbol, targetArguments)) := by
    dsimp [predicate_formula_transform_condition]
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetArguments (.cons sourceArguments (.cons symbol (.cons arity .nil))))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
      Formula.substituteFree, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term, predicate_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term, godel_pairing_term,
      term_weaken_free_four] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hArity hSymbol)
        (FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro
            (Metatheory.Derives.equality_refl
              (pred_codeₘ(arity, symbol, sourceArguments) : SetOpenTerm []))
            (Metatheory.Derives.equality_refl
              (pred_codeₘ(arity, symbol, targetArguments) : SetOpenTerm [])))
          hArguments)
  dsimp [syntax_transform_shape_condition, formula_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_right
  exact FirstOrder.Derives.conj_intro
    (Metatheory.Derives.equality_refl
      (syntax_code_kind_term .formula : SetOpenTerm []))
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_left hBranch)))

theorem formula_transform_negation_shape
    (operation : SyntaxTransformOperation)
    (variableIndex replacement : SetOpenTerm [])
    (depth sourceBody targetBody : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term operation,
        depth, variableIndex, replacement, sourceBody, targetBody)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (neg_codeₘ(sourceBody)) (neg_codeₘ(targetBody)) := by
  have hBranch : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      negation_formula_transform_condition
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (neg_codeₘ(sourceBody)) (neg_codeₘ(targetBody)) := by
    dsimp [negation_formula_transform_condition]
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetBody (.cons sourceBody .nil))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
      Formula.substituteFree, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term, negation_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term, godel_pairing_term,
      term_weaken_free_two] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (neg_codeₘ(sourceBody) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (neg_codeₘ(targetBody) : SetOpenTerm [])))
        hBody
  dsimp [syntax_transform_shape_condition, formula_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_right
  exact FirstOrder.Derives.conj_intro
    (Metatheory.Derives.equality_refl
      (syntax_code_kind_term .formula : SetOpenTerm []))
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left hBranch))))

theorem formula_transform_implication_shape
    (operation : SyntaxTransformOperation)
    (variableIndex replacement : SetOpenTerm [])
    (depth sourceLeft sourceRight targetLeft targetRight : SetOpenTerm [])
    (hLeft : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term operation,
        depth, variableIndex, replacement, sourceLeft, targetLeft))
    (hRight : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term operation,
        depth, variableIndex, replacement, sourceRight, targetRight)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (imp_codeₘ(sourceLeft, sourceRight))
        (imp_codeₘ(targetLeft, targetRight)) := by
  have hBranch : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      implication_formula_transform_condition
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (imp_codeₘ(sourceLeft, sourceRight))
        (imp_codeₘ(targetLeft, targetRight)) := by
    dsimp [implication_formula_transform_condition]
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetRight (.cons targetLeft (.cons sourceRight (.cons sourceLeft .nil))))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
      Formula.substituteFree, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term, implication_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term, godel_pairing_term,
      term_weaken_free_four] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(sourceLeft, sourceRight) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (imp_codeₘ(targetLeft, targetRight) : SetOpenTerm [])))
        (FirstOrder.Derives.conj_intro hLeft hRight)
  dsimp [syntax_transform_shape_condition, formula_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_right
  exact FirstOrder.Derives.conj_intro
    (Metatheory.Derives.equality_refl
      (syntax_code_kind_term .formula : SetOpenTerm []))
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_left hBranch)))))

theorem formula_transform_universal_preserve_shape
    (operation : SyntaxTransformOperation)
    (hOperation : operation = .substituteFree ∨
      operation = .closeFree ∨ operation = .openBound ∨
        operation = .abstractFreeTop)
    (variableIndex replacement : SetOpenTerm [])
    (depth sourceBody targetBody : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term operation,
        Sₘ(depth), variableIndex, replacement, sourceBody, targetBody)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (all_codeₘ(sourceBody)) (all_codeₘ(targetBody)) := by
  have hPreserve : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (syntax_transform_operation_term operation ≐ₘ
          syntax_transform_operation_term .substituteFree) ∨ₘ
        ((syntax_transform_operation_term operation ≐ₘ
            syntax_transform_operation_term .closeFree) ∨ₘ
        ((syntax_transform_operation_term operation ≐ₘ
            syntax_transform_operation_term .openBound) ∨ₘ
          (syntax_transform_operation_term operation ≐ₘ
            syntax_transform_operation_term .abstractFreeTop))) := by
    rcases hOperation with rfl | rfl | rfl | rfl
    · exact FirstOrder.Derives.disj_intro_left
        (Metatheory.Derives.equality_refl
          (syntax_transform_operation_term .substituteFree :
            SetOpenTerm []))
    · exact FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_left
          (Metatheory.Derives.equality_refl
            (syntax_transform_operation_term .closeFree :
              SetOpenTerm [])))
    · exact FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_left
            (Metatheory.Derives.equality_refl
              (syntax_transform_operation_term .openBound :
                SetOpenTerm []))))
    · exact FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (Metatheory.Derives.equality_refl
              (syntax_transform_operation_term .abstractFreeTop :
                SetOpenTerm []))))
  have hBranch : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      universal_formula_transform_condition
        (syntax_transform_operation_term operation)
        depth variableIndex replacement
        (all_codeₘ(sourceBody)) (all_codeₘ(targetBody)) := by
    dsimp [universal_formula_transform_condition]
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetBody (.cons sourceBody .nil))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
      Formula.substituteFree, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term, universal_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term, godel_pairing_term,
      term_weaken_free_two] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (all_codeₘ(sourceBody) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (all_codeₘ(targetBody) : SetOpenTerm [])))
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.conj_intro hPreserve hBody))
  dsimp [syntax_transform_shape_condition, formula_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_right
  exact FirstOrder.Derives.conj_intro
    (Metatheory.Derives.equality_refl
      (syntax_code_kind_term .formula : SetOpenTerm []))
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right
              (FirstOrder.Derives.disj_intro_right
                (FirstOrder.Derives.disj_intro_right hBranch)))))

theorem formula_transform_universal_weaken_shape
    (variableIndex replacement : SetOpenTerm [])
    (depth sourceBody targetBody : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(depth), Sₘ(variableIndex), replacement,
        sourceBody, targetBody)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .weakenBound)
        depth variableIndex replacement
        (all_codeₘ(sourceBody)) (all_codeₘ(targetBody)) := by
  have hShift : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (syntax_transform_operation_term .weakenBound ≐ₘ
          syntax_transform_operation_term .weakenBound) ∨ₘ
        (syntax_transform_operation_term .weakenBound ≐ₘ
          syntax_transform_operation_term .swapBound) :=
    FirstOrder.Derives.disj_intro_left
      (Metatheory.Derives.equality_refl
        (syntax_transform_operation_term .weakenBound : SetOpenTerm []))
  have hBranch : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      universal_formula_transform_condition
        (syntax_transform_operation_term .weakenBound)
        depth variableIndex replacement
        (all_codeₘ(sourceBody)) (all_codeₘ(targetBody)) := by
    dsimp [universal_formula_transform_condition]
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetBody (.cons sourceBody .nil))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
      Formula.substituteFree, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term, universal_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term, godel_pairing_term,
      term_weaken_free_two] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (all_codeₘ(sourceBody) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (all_codeₘ(targetBody) : SetOpenTerm [])))
        (FirstOrder.Derives.disj_intro_left
          (FirstOrder.Derives.conj_intro hShift hBody))
  dsimp [syntax_transform_shape_condition, formula_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_right
  exact FirstOrder.Derives.conj_intro
    (Metatheory.Derives.equality_refl
      (syntax_code_kind_term .formula : SetOpenTerm []))
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right hBranch)))))

theorem formula_transform_universal_swap_shape
    (variableIndex replacement : SetOpenTerm [])
    (depth sourceBody targetBody : SetOpenTerm [])
    (hBody : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        Sₘ(depth), Sₘ(variableIndex), replacement,
        sourceBody, targetBody)) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term .formula)
        (syntax_transform_operation_term .swapBound)
        depth variableIndex replacement
        (all_codeₘ(sourceBody)) (all_codeₘ(targetBody)) := by
  have hShift : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      (syntax_transform_operation_term .swapBound ≐ₘ
          syntax_transform_operation_term .weakenBound) ∨ₘ
        (syntax_transform_operation_term .swapBound ≐ₘ
          syntax_transform_operation_term .swapBound) :=
    FirstOrder.Derives.disj_intro_right
      (Metatheory.Derives.equality_refl
        (syntax_transform_operation_term .swapBound : SetOpenTerm []))
  have hBranch : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      universal_formula_transform_condition
        (syntax_transform_operation_term .swapBound)
        depth variableIndex replacement
        (all_codeₘ(sourceBody)) (all_codeₘ(targetBody)) := by
    dsimp [universal_formula_transform_condition]
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetBody (.cons sourceBody .nil))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
      Formula.substituteFree, Formula.substitute, Formula.substituteMapped,
      Substitution.free_map, VariableSubstitution.cons, Term.substituteMapped,
      Arguments.substituteMapped, structural_list_code_term, universal_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term, godel_pairing_term,
      term_weaken_free_two] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (all_codeₘ(sourceBody) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (all_codeₘ(targetBody) : SetOpenTerm [])))
        (FirstOrder.Derives.disj_intro_left
          (FirstOrder.Derives.conj_intro hShift hBody))
  dsimp [syntax_transform_shape_condition, formula_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_right
  exact FirstOrder.Derives.conj_intro
    (Metatheory.Derives.equality_refl
      (syntax_code_kind_term .formula : SetOpenTerm []))
    (FirstOrder.Derives.disj_intro_right
      (FirstOrder.Derives.disj_intro_right
        (FirstOrder.Derives.disj_intro_right
          (FirstOrder.Derives.disj_intro_right
            (FirstOrder.Derives.disj_intro_right hBranch)))))

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
