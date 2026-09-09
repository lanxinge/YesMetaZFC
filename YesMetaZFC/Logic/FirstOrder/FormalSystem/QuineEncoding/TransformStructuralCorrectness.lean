import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# 统一语法变换的结构正确性公共内核

本模块只包含与具体语法变换操作无关的组合器及有限自由槽替换快路径。
具体的 `abstractFreeTop`、`openBound` 等递归实现只消费这些接口，不再形成反向依赖。
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

/-- 由码域、scope 与构造形状组合统一语法变换关系。 -/
theorem syntax_transform_intro
    (kind : SyntaxCodeKind) (operation : SyntaxTransformOperation)
    (depth variableIndex : Nat)
    (replacement source target : SetOpenTerm [])
    (hSourceMem : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      source ∈ₘ ωₘ)
    (hTargetMem : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      target ∈ₘ ωₘ)
    (hReplacementMem : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      replacement ∈ₘ ωₘ)
    (hScope : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_scope_condition
        (syntax_code_kind_term kind)
        (syntax_transform_operation_term operation)
        (numₘ(depth)) (numₘ(variableIndex)) replacement
        source target)
    (hShape : ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transform_shape_condition
        (syntax_code_kind_term kind)
        (syntax_transform_operation_term operation)
        (numₘ(depth)) (numₘ(variableIndex)) replacement
        source target) :
    ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
      syntax_transformₘ(
        syntax_code_kind_term kind,
        syntax_transform_operation_term operation,
        numₘ(depth), numₘ(variableIndex), replacement,
        source, target) := by
  apply FirstOrder.Derives.iff_elim_right
    (syntax_transform_definition_instance_derives
      (Γ := ([] : Context signature []))
      (syntax_code_kind_term kind)
      (syntax_transform_operation_term operation)
      (numₘ(depth)) (numₘ(variableIndex)) replacement
      source target)
  have hGlobal := FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := [])
          (syntax_code_kind kind))
        (finite_numeral_mem_expression (Γ := [])
          (syntax_transform_operation operation)))
      (FirstOrder.Derives.conj_intro
        (finite_numeral_mem_expression (Γ := []) depth)
        (finite_numeral_mem_expression (Γ := []) variableIndex)))
    (FirstOrder.Derives.conj_intro
      hReplacementMem
      (FirstOrder.Derives.conj_intro hSourceMem hTargetMem))
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro hGlobal hScope) hShape

theorem four_free_substitution_beta
    {body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]}
    (first second third fourth : SetOpenTerm []) :
    Formula.instantiateFreeTop first
      (Formula.substituteFree
        (VariableSubstitution.liftFree SetSort.set
          (VariableSubstitution.instantiateFreeTop second))
        (Formula.substituteFree
          (VariableSubstitution.liftFree SetSort.set
            (VariableSubstitution.liftFree SetSort.set
              (VariableSubstitution.instantiateFreeTop third)))
          (Formula.substituteFree
            (VariableSubstitution.liftFree SetSort.set
              (VariableSubstitution.liftFree SetSort.set
                (VariableSubstitution.liftFree SetSort.set
                  (VariableSubstitution.instantiateFreeTop fourth))))
            body))) =
      Formula.substituteFree
        (VariableSubstitution.cons first
          (VariableSubstitution.cons second
            (VariableSubstitution.cons third
              (VariableSubstitution.cons fourth
                VariableSubstitution.empty)))) body := by
  change (((body.substituteFree _).substituteFree _).substituteFree _).substituteFree _ = _
  rw [Formula.substituteFree_comp, Formula.substituteFree_comp, Formula.substituteFree_comp]
  congr 1
  funext resultSort entry
  cases entry with
  | here => rfl
  | there entry =>
    cases entry with
    | here => exact Term.substituteMapped_weakenFree_instantiateFreeTop _ _ _
    | there entry =>
      cases entry with
      | here =>
        simp only [VariableSubstitution.postcompose, VariableSubstitution.liftFree,
          VariableSubstitution.instantiateFreeTop,
          Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
          VariableSubstitution.cons]
        rfl
      | there entry =>
        cases entry with
        | here =>
          simp only [VariableSubstitution.postcompose, VariableSubstitution.liftFree,
            VariableSubstitution.instantiateFreeTop,
            Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree,
            VariableSubstitution.cons]
        | there entry => exact nomatch entry


/-- 任意四槽替换消去闭项的四层自由上下文提升。 -/
theorem gq_closed_four_weaken_substitute
    (τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] [] [])
    {resultSort : signature.SortSymbol}
    (term : Term signature [] [] resultSort) :
    Term.substituteMapped VariableSubstitution.boundId τ
        ((((term.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree
          SetSort.set).weakenFree SetSort.set) =
      term := by
  simp only [Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree]

/-! ## 操作无关的项与参数列构造

这些定理只证明 shape；操作码合法性、作用域与总码域由 `syntax_transform_intro`
消费原有合同。子构造的推导可以来自任意目标理论与闭自由上下文上的任意假设。
-/

/-- 常量节点不读取变换参数；只要求符号码的成员证据。 -/
theorem syntax_transform_constant_shape
    {T : SetTheory} {Γ : Context signature []}
    (operation depth variableIndex replacement : SetOpenTerm [])
    (symbol : SetOpenTerm []) (hSymbol : Γ ⊢ₘ[T] symbol ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] syntax_transform_shape_condition
      (syntax_code_kind_term .term) operation depth variableIndex replacement
      (const_codeₘ(symbol)) (const_codeₘ(symbol)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    apply FirstOrder.Derives.exists_intro symbol
    simpa [Formula.instantiateFreeTop, Substitution.instantiateFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.liftFree,
      VariableSubstitution.weakenBound,
      VariableSubstitution.boundId, VariableSubstitution.freeId,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop] using
      FirstOrder.Derives.conj_intro hSymbol
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (const_codeₘ(symbol) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (const_codeₘ(symbol) : SetOpenTerm [])))

/-- 应用节点仅装配参数列的变换；元数、符号和操作均由调用方给定。 -/
theorem syntax_transform_application_shape
    {T : SetTheory} {Γ : Context signature []}
    (operation depth variableIndex replacement : SetOpenTerm [])
    (arity symbol sourceArguments targetArguments : SetOpenTerm [])
    (hArity : Γ ⊢ₘ[T] arity ∈ₘ ωₘ)
    (hSymbol : Γ ⊢ₘ[T] symbol ∈ₘ ωₘ)
    (hTransform : Γ ⊢ₘ[T] syntax_transformₘ(
      syntax_code_kind_term .termList, operation, depth, variableIndex,
      replacement, sourceArguments, targetArguments)) :
    Γ ⊢ₘ[T] syntax_transform_shape_condition
      (syntax_code_kind_term .term) operation depth variableIndex replacement
      (app_codeₘ(arity, symbol, sourceArguments))
      (app_codeₘ(arity, symbol, targetArguments)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .term : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetArguments (.cons sourceArguments (.cons symbol (.cons arity .nil))))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId, Formula.substituteFree,
      Formula.substitute, Formula.substituteMapped, Substitution.free_map,
      VariableSubstitution.cons, Term.substituteMapped, Arguments.substituteMapped,
      structural_list_code_term, application_code_term, structural_node_code_term,
      structural_raw_node_code_term, godel_pairing_term, term_weaken_free_four,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hArity hSymbol)
        (FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro
            (Metatheory.Derives.equality_refl
              (app_codeₘ(arity, symbol, sourceArguments) : SetOpenTerm []))
            (Metatheory.Derives.equality_refl
              (app_codeₘ(arity, symbol, targetArguments) : SetOpenTerm [])))
          hTransform)

/-- 空参数列的构造形状与具体变换操作无关。 -/
theorem syntax_transform_nil_shape
    {T : SetTheory} {Γ : Context signature []}
    (operation depth variableIndex replacement : SetOpenTerm []) :
    Γ ⊢ₘ[T] syntax_transform_shape_condition
      (syntax_code_kind_term .termList) operation depth variableIndex replacement
      code_nilₘ code_nilₘ := by
  derive_prop

/-- 参数列 cons 共用一次见证装配，头项与尾列只提供各自的变换。 -/
theorem syntax_transform_cons_shape
    {T : SetTheory} {Γ : Context signature []}
    (operation depth variableIndex replacement : SetOpenTerm [])
    (sourceHead sourceTail targetHead targetTail : SetOpenTerm [])
    (hHead : Γ ⊢ₘ[T] syntax_transformₘ(
      syntax_code_kind_term .term, operation, depth, variableIndex,
      replacement, sourceHead, targetHead))
    (hTail : Γ ⊢ₘ[T] syntax_transformₘ(
      syntax_code_kind_term .termList, operation, depth, variableIndex,
      replacement, sourceTail, targetTail)) :
    Γ ⊢ₘ[T] syntax_transform_shape_condition
      (syntax_code_kind_term .termList) operation depth variableIndex replacement
      (code_consₘ(sourceHead, sourceTail)) (code_consₘ(targetHead, targetTail)) := by
  dsimp [syntax_transform_shape_condition]
  apply FirstOrder.Derives.disj_intro_right
  apply FirstOrder.Derives.disj_intro_left
  apply FirstOrder.Derives.conj_intro
  · exact Metatheory.Derives.equality_refl
      (syntax_code_kind_term .termList : SetOpenTerm [])
  · apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.existsFreePrefix_intro
      (.cons targetTail (.cons targetHead (.cons sourceTail (.cons sourceHead .nil))))
    simpa [Arguments.substitutionWith, VariableSubstitution.freeId, Formula.substituteFree,
      Formula.substitute, Formula.substituteMapped, Substitution.free_map,
      VariableSubstitution.cons, Term.substituteMapped, Arguments.substituteMapped,
      structural_raw_node_code_term, godel_pairing_term, term_weaken_free_four,
      Term.substituteMapped_weakenFree_tail, Term.substituteMapped_emptyFree] using
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (code_consₘ(sourceHead, sourceTail) : SetOpenTerm []))
          (Metatheory.Derives.equality_refl
            (code_consₘ(targetHead, targetTail) : SetOpenTerm [])))
        (FirstOrder.Derives.conj_intro hHead hTail)

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
