import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalTransfer

/-! # 最终扩张中的语法、逻辑与求值公理闭句

保留原闭句的合取结构与参数顺序；此前最小不动点方程在所有对象参数上成立。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalSyntax
open PureModel Nonlogical.BasicSetTheory FormalSystem PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem structural_syntax (hℳ : Theory.Models ℳ theory) :
    structural_syntax_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ structural_syntax_definition_axiom (by decide +kernel)).mp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply close_of_values
    intro args
    cases args with | cons b tail1 =>
    cases tail1 with | cons a tail2 =>
    cases tail2
    exact PureRelatedStage.term_definition hℳ a b
  · apply close_of_values
    intro args
    cases args with | cons c tail1 =>
    cases tail1 with | cons b tail2 =>
    cases tail2 with | cons a tail3 =>
    cases tail3
    exact PureRelatedStage.term_list_definition hℳ a b c
  · apply close_of_values
    intro args
    cases args with | cons b tail1 =>
    cases tail1 with | cons a tail2 =>
    cases tail2
    exact PureRelatedStage.formula_definition hℳ a b

theorem related_term (hℳ : Theory.Models ℳ theory) :
    related_term_code_at_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ related_term_code_at_definition_axiom (by decide +kernel)).mp
  apply close_of_values
  intro args
  cases args with | cons c tail1 =>
  cases tail1 with | cons b tail2 =>
  cases tail2 with | cons a tail3 =>
  cases tail3
  exact PureRelatedStage.related_term_definition hℳ a b c

theorem related_term_list (hℳ : Theory.Models ℳ theory) :
    related_term_list_code_at_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ related_term_list_code_at_definition_axiom (by decide +kernel)).mp
  apply close_of_values
  intro args
  cases args with | cons d tail1 =>
  cases tail1 with | cons c tail2 =>
  cases tail2 with | cons b tail3 =>
  cases tail3 with | cons a tail4 =>
  cases tail4
  exact PureRelatedStage.related_term_list_definition hℳ a b c d

theorem related_formula (hℳ : Theory.Models ℳ theory) :
    related_formula_code_at_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ related_formula_code_at_definition_axiom (by decide +kernel)).mp
  apply close_of_values
  intro args
  cases args with | cons c tail1 =>
  cases tail1 with | cons b tail2 =>
  cases tail2 with | cons a tail3 =>
  cases tail3
  exact PureRelatedStage.related_formula_definition hℳ a b c

theorem related_term_set (hℳ : Theory.Models ℳ theory) :
    related_term_set_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ related_term_set_definition_axiom (by decide +kernel)).mp
  apply close_of_values
  intro args
  cases args with | cons b tail1 =>
  cases tail1 with | cons a tail2 =>
  cases tail2
  exact PureRelatedStage.term_set_definition hℳ a b

theorem related_formula_set (hℳ : Theory.Models ℳ theory) :
    related_formula_set_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ related_formula_set_definition_axiom (by decide +kernel)).mp
  apply close_of_values
  intro args
  cases args with | cons b tail1 =>
  cases tail1 with | cons a tail2 =>
  cases tail2
  exact PureRelatedStage.formula_set_definition hℳ a b

theorem syntax_transform_parameter_order (𝒩 : Structure.{0,0,0,x} S) (a b c d e f g : 𝒩.Carrier s) :
    (syntax_transform_definition_instance (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons g (.cons f (.cons e (.cons d (.cons c (.cons b (.cons a .nil))))))) : Env 𝒩 [] [s,s,s,s,s,s,s]) ↔
    (syntax_transform_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here)))))))).satisfies
      (templateEnv (.cons a (.cons b (.cons c (.cons d (.cons e (.cons f (.cons g .nil))))))) : Env 𝒩 [] [s,s,s,s,s,s,s])  := by
  let args : Arguments S [] [s,s,s,s,s,s,s] [s,s,s,s,s,s,s] := (.cons (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.fvar (.there (.there (.there (.there (.there .here)))))) (.cons (.fvar (.there (.there (.there (.there .here))))) (.cons (.fvar (.there (.there (.there .here)))) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there .here)) (.cons (.fvar .here) .nil)))))))
  let env : Env 𝒩 [] [s,s,s,s,s,s,s] := templateEnv (.cons g (.cons f (.cons e (.cons d (.cons c (.cons b (.cons a .nil)))))))
  have h := Formula.satisfies_substituteFree env (argumentsSubstitution args)
    (syntax_transform_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there (.there (.there (.there (.there (.there .here))))))))
  rw [syntax_transform_definition_instance_substituteFree] at h
  have hEnv : env.pullback (Substitution.free_map (argumentsSubstitution args)) =
      (templateEnv (.cons a (.cons b (.cons c (.cons d (.cons e (.cons f (.cons g .nil))))))) : Env 𝒩 [] [s,s,s,s,s,s,s]) := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry
      cases entry with
      | here => rfl
      | there entry =>
        cases entry with
        | here => rfl
        | there entry =>
          cases entry with
          | here => rfl
          | there entry =>
            cases entry with
            | here => rfl
            | there entry =>
              cases entry with
              | here => rfl
              | there entry =>
                cases entry with
                | here => rfl
                | there entry =>
                  cases entry with
                  | here => rfl
                  | there entry =>
                    cases entry
  rw [hEnv] at h
  exact h

theorem syntax_transform (hℳ : Theory.Models ℳ theory) :
    syntax_transform_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_values
  intro args
  apply (fromTransform hℳ _ (by decide +kernel) args).mp
  cases args with | cons g tail1 =>
  cases tail1 with | cons f tail2 =>
  cases tail2 with | cons e tail3 =>
  cases tail3 with | cons d tail4 =>
  cases tail4 with | cons c tail5 =>
  cases tail5 with | cons b tail6 =>
  cases tail6 with | cons a tail7 =>
  cases tail7
  apply (syntax_transform_parameter_order (PureTransformStage.expansion hℳ).model a b c d e f g).mpr
  exact PureTransformStage.syntaxTransform_definition hℳ a b c d e f g

theorem free_variable_occurs_parameter_order (𝒩 : Structure.{0,0,0,x} S) (a b c : 𝒩.Carrier s) :
    (free_variable_occurs_definition_instance (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
    (free_variable_occurs_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons a (.cons b (.cons c .nil))) : Env 𝒩 [] [s,s,s])  := by
  let args : Arguments S [] [s,s,s] [s,s,s] := (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there .here)) (.cons (.fvar .here) .nil)))
  let env : Env 𝒩 [] [s,s,s] := templateEnv (.cons c (.cons b (.cons a .nil)))
  have h := Formula.satisfies_substituteFree env (argumentsSubstitution args)
    (free_variable_occurs_definition_instance (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))
  rw [free_variable_occurs_definition_instance_substituteFree] at h
  have hEnv : env.pullback (Substitution.free_map (argumentsSubstitution args)) =
      (templateEnv (.cons a (.cons b (.cons c .nil))) : Env 𝒩 [] [s,s,s]) := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry
      cases entry with
      | here => rfl
      | there entry =>
        cases entry with
        | here => rfl
        | there entry =>
          cases entry with
          | here => rfl
          | there entry =>
            cases entry
  rw [hEnv] at h
  exact h

theorem free_variable_occurs (hℳ : Theory.Models ℳ theory) :
    free_variable_occurs_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_values
  intro args
  apply (fromTransform hℳ _ (by decide +kernel) args).mp
  cases args with | cons c tail1 =>
  cases tail1 with | cons b tail2 =>
  cases tail2 with | cons a tail3 =>
  cases tail3
  apply (free_variable_occurs_parameter_order (PureTransformStage.expansion hℳ).model a b c).mpr
  exact PureTransformStage.freeVariableOccurs_definition hℳ a b c

theorem structure_axiom (hℳ : Theory.Models ℳ theory) :
    structure_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ structure_definition_axiom (by decide +kernel)).mp
  apply close_of_values
  intro args
  cases args with | cons c tail1 =>
  cases tail1 with | cons b tail2 =>
  cases tail2 with | cons a tail3 =>
  cases tail3
  exact PureRelatedStage.structure_definition hℳ a b c

theorem modus_ponens (hℳ : Theory.Models ℳ theory) :
    modus_ponens_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ modus_ponens_definition_axiom (by decide +kernel)).mp
  apply close_of_values
  intro args
  cases args with | cons c tail1 =>
  cases tail1 with | cons b tail2 =>
  cases tail2 with | cons a tail3 =>
  cases tail3
  exact PureRelatedStage.modus_ponens_definition hℳ a b c

theorem term_value (hℳ : Theory.Models ℳ theory) :
    term_value_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_values
  intro args
  cases args with | cons f tail1 =>
  cases tail1 with | cons e tail2 =>
  cases tail2 with | cons d tail3 =>
  cases tail3 with | cons c tail4 =>
  cases tail4 with | cons b tail5 =>
  cases tail5 with | cons a tail6 =>
  cases tail6
  exact PureCompletedStage.termValue_definition hℳ a b c d e f

theorem term_list_value (hℳ : Theory.Models ℳ theory) :
    term_list_value_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_values
  intro args
  cases args with | cons g tail1 =>
  cases tail1 with | cons f tail2 =>
  cases tail2 with | cons e tail3 =>
  cases tail3 with | cons d tail4 =>
  cases tail4 with | cons c tail5 =>
  cases tail5 with | cons b tail6 =>
  cases tail6 with | cons a tail7 =>
  cases tail7
  exact PureCompletedStage.termListValue_definition hℳ a b c d e f g

theorem related_syntax (hℳ : Theory.Models ℳ theory) :
    related_syntax_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) :=
  ⟨related_term hℳ, related_term_list hℳ, related_formula hℳ, related_term_set hℳ, related_formula_set hℳ⟩

theorem nonlogical_symbols (hℳ : Theory.Models ℳ theory) :
    related_nonlogical_symbol_set_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRelatedSentence hℳ related_nonlogical_symbol_set_definition_axiom (by decide +kernel)).mp
  have h := PureRelatedStage.nonlogical_definition hℳ
  have hEnv : (templateEnv .nil : Env (PureRelatedStage.expansion hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  rwa [hEnv] at h

theorem schema_axioms (hℳ : Theory.Models ℳ theory) :
    (propositional_axiom_schema_definition_axiom.conj
      (quantifier_axiom_schema_definition_axiom.conj equality_axiom_schema_definition_axiom)).satisfies
      (Env.empty : Env (E hℳ).model [] []) := by
  have h := PureCompletedStage.schema_axioms hℳ
  have hEnv : (templateEnv .nil : Env (E hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  rwa [hEnv] at h

theorem logical_axioms (hℳ : Theory.Models ℳ theory) :
    logical_axiom_code_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  have h := PureCompletedStage.logical_code_axioms hℳ
  have hEnv : (templateEnv .nil : Env (E hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  rwa [hEnv] at h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalSyntax
