import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalBasic

/-! # 有序对、关系与投影的原公理

把原成员规格接到同一 Kuratowski 编码，投影仍只在原有序对 guard 下使用。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalPairs
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer PureFinalBasic
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem ordered_value (hℳ : Theory.Models ℳ theory) (a b output : Carrier ℳ) :
    output = F hℳ .orderedPair (.cons a (.cons b .nil)) ↔ PureKuratowski.Code ℳ output a b :=
  ((PureCompletedStage.realizes hℳ).function .orderedPair (.cons a (.cons b .nil)) output).symm.trans
    (PureRelationDefinitions.orderedPair_correct output a b)

theorem pair_member (hℳ : Theory.Models ℳ theory) (a b relation : Carrier ℳ) :
    membership ℳ (F hℳ .orderedPair (.cons a (.cons b .nil))) relation ↔
      PureKuratowski.PairMember ℳ a b relation := by
  constructor
  · intro h; exact ⟨_, (ordered_value hℳ a b _).mp rfl, h⟩
  · rintro ⟨output, hCode, h⟩
    exact (ordered_value hℳ a b output).mpr hCode ▸ h

theorem ordered_predicate (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    (E hℳ).relation .isOrderedPair (.cons a .nil) ↔ ∃ left right, PureKuratowski.Code ℳ a left right := by
  have h := PureRelationDefinitions.isOrderedPair_satisfies (templateEnv (.cons a .nil) : Env ℳ [] [setSort]) (.fvar .here)
  rw [PureRelationDefinitions.isOrderedPair, applyTemplate_satisfies] at h
  exact ((PureCompletedStage.realizes hℳ).relation .isOrderedPair (.cons a .nil)).symm.trans h

theorem relation_predicate (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    (E hℳ).relation .isRelation (.cons a .nil) ↔ PureKuratowski.IsRelation ℳ a := by
  have h := PureRelationDefinitions.isRelation_satisfies (templateEnv (.cons a .nil) : Env ℳ [] [setSort]) (.fvar .here)
  rw [PureRelationDefinitions.isRelation, applyTemplate_satisfies] at h
  exact ((PureCompletedStage.realizes hℳ).relation .isRelation (.cons a .nil)).symm.trans h

theorem function_predicate (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    (E hℳ).relation .isFunction (.cons a .nil) ↔ PureKuratowski.IsFunction ℳ a := by
  have h := PureRelationDefinitions.isFunction_satisfies (templateEnv (.cons a .nil) : Env ℳ [] [setSort]) (.fvar .here)
  rw [PureRelationDefinitions.isFunction, applyTemplate_satisfies] at h
  exact ((PureCompletedStage.realizes hℳ).relation .isFunction (.cons a .nil)).symm.trans h

theorem ordered_spec_semantics (𝒩 : Structure.{0,0,0,x} S) (a b output : 𝒩.Carrier s) :
    (ordered_pair_spec (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∀ element, Mem 𝒩 element output ↔
        element = 𝒩.funcInterp .singleton (.cons a .nil) ∨
          element = 𝒩.funcInterp .unorderedPair (.cons a (.cons b .nil)) := by
  simp only [ordered_pair_spec, pair_spec, membership_specification, pair_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem ordered_condition_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (is_ordered_pair_condition (.fvar .here)).satisfies
      (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      ∃ left right, a = 𝒩.funcInterp .orderedPair (.cons left (.cons right .nil)) := by
  simp only [is_ordered_pair_condition, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem relation_condition_semantics (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) :
    (is_relation_condition (.fvar .here)).satisfies
      (templateEnv (.cons a .nil) : Env 𝒩 [] [s]) ↔
      ∀ element, Mem 𝒩 element a → 𝒩.relInterp .isOrderedPair (.cons element .nil) := by
  simp only [is_relation_condition, Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem left_spec_semantics (𝒩 : Structure.{0,0,0,x} S) (a output : 𝒩.Carrier s) :
    (left_projection_spec (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∀ element, (∀ member, Mem 𝒩 member a → Mem 𝒩 element member) ↔ element = output := by
  simp only [left_projection_spec, intersection_member_condition,
    Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem right_spec_semantics (𝒩 : Structure.{0,0,0,x} S) (a output : 𝒩.Carrier s) :
    (right_projection_spec (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons output (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ∃ left, a = 𝒩.funcInterp .orderedPair (.cons left (.cons output .nil)) := by
  simp only [right_projection_spec, Formula.satisfies_existsFreeTop, Formula.satisfies]
  rfl

theorem ordered_pair (hℳ : Theory.Models ℳ theory) :
    ordered_pair_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output b a
  apply (ordered_value hℳ a b output).trans
  apply Iff.trans ?_ (ordered_spec_semantics (E hℳ).model a b output).symm
  constructor
  · rintro ⟨single, pair, hSingle, hPair, hOutput⟩
    have hSingleEq := PureKuratowski.single_unique hℳ hSingle (singleton_value hℳ a)
    have hPairEq := PureKuratowski.pair_unique hℳ hPair ((pair_value hℳ a b _).mp rfl)
    subst single; subst pair
    exact hOutput
  · intro h
    exact ⟨_, _, singleton_value hℳ a, (pair_value hℳ a b _).mp rfl, h⟩

theorem is_ordered_pair (hℳ : Theory.Models ℳ theory) :
    is_ordered_pair_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  apply (ordered_predicate hℳ a).trans
  apply Iff.trans ?_ (ordered_condition_semantics (E hℳ).model a).symm
  exact exists_congr (fun left => exists_congr (fun right => (ordered_value hℳ left right a).symm))

theorem is_relation (hℳ : Theory.Models ℳ theory) :
    is_relation_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro a
  apply (relation_predicate hℳ a).trans
  apply Iff.trans ?_ (relation_condition_semantics (E hℳ).model a).symm
  exact forall_congr' (fun element => imp_congr Iff.rfl (ordered_predicate hℳ element).symm)

theorem left_projection (hℳ : Theory.Models ℳ theory) :
    left_projection_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output a
  intro hPair
  have hCode := (ordered_predicate hℳ a).mp hPair
  have hGraph := ((PureCompletedStage.realizes hℳ).function .leftProjection (.cons a .nil) output).symm
  exact (eq_comm.trans hGraph).trans ((PureRelationFunctions.left_spec hCode output).trans
    (left_spec_semantics (E hℳ).model a output).symm)

theorem right_projection (hℳ : Theory.Models ℳ theory) :
    right_projection_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output a
  intro hPair
  have hCode := (ordered_predicate hℳ a).mp hPair
  have hGraph := ((PureCompletedStage.realizes hℳ).function .rightProjection (.cons a .nil) output).symm
  apply (eq_comm.trans hGraph).trans
  apply (PureRelationFunctions.right_spec hCode output).trans
  exact (exists_congr (fun left => (ordered_value hℳ left output a).symm)).trans
    (right_spec_semantics (E hℳ).model a output).symm

/-- 无 guard 反转定义：任意输入都交换实际总投影，再组成有序对。 -/
theorem reverse (hℳ : Theory.Models ℳ theory) :
    ordered_pair_reverse_definition_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro output input
  apply ((PureCompletedStage.realizes hℳ).function .orderedPairReverse (.cons input .nil) output).symm.trans
  apply (PureOmegaAndReverse.reverse_graph_correct output input).trans
  apply Iff.trans ?_ (ordered_value hℳ
    (F hℳ .rightProjection (.cons input .nil)) (F hℳ .leftProjection (.cons input .nil)) output).symm
  constructor
  · rintro ⟨left, right, hLeft, hRight, hCode⟩
    have hLeftEq := ((PureCompletedStage.realizes hℳ).function .leftProjection (.cons input .nil) left).mp hLeft
    have hRightEq := ((PureCompletedStage.realizes hℳ).function .rightProjection (.cons input .nil) right).mp hRight
    subst left; subst right
    exact hCode
  · intro hCode
    exact ⟨_, _, ((PureCompletedStage.realizes hℳ).function .leftProjection (.cons input .nil) _).mpr rfl,
      ((PureCompletedStage.realizes hℳ).function .rightProjection (.cons input .nil) _).mpr rfl, hCode⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalPairs
