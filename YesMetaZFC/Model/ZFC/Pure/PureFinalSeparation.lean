import YesMetaZFC.Model.ZFC.Pure.PureFinalConstructions
import YesMetaZFC.Model.ZFC.Pure.PureSupportSeparation
import YesMetaZFC.Model.ZFC.Pure.PureFinalBasic

/-! # 三条具体集合收集分离公理

两个收集对象使用实际函数图的全输入规格；关系像直接使用翻译后纯公式的分离。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalSeparation
open PureModel Nonlogical.BasicSetTheory FormalSystem PureFinalTransfer PureFinalBasic
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

theorem finite_semantics (𝒩 : Structure.{0,0,0,x} S) (source : 𝒩.Carrier s) :
    (finite_subset_collection_separation_exists (.fvar .here)).satisfies
      (templateEnv (.cons source .nil) : Env 𝒩 [] [s]) ↔
      ∃ output, (finite_subset_collection_spec (.fvar (.there .here)) (.fvar .here)).satisfies
        (templateEnv (.cons output (.cons source .nil)) : Env 𝒩 [] [s,s]) := by
  simp only [finite_subset_collection_separation_exists, Formula.satisfies_existsFreeTop]
  rfl

theorem finite_subset_collection (hℳ : Theory.Models ℳ theory) :
    finite_subset_collection_separation_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro source
  apply (finite_semantics (PureRoundTwoStage.expansion hℳ).model source).mpr
  refine ⟨(PureRoundTwoStage.expansion hℳ).function .finiteSubsetCollection (.cons source .nil), ?_⟩
  exact (PureRoundTwoSpecifications.bounded_specification hℳ .finiteSubsetCollection (.cons source .nil) _).mp rfl

theorem nonempty_semantics (𝒩 : Structure.{0,0,0,x} S) (source : 𝒩.Carrier s) :
    (nonempty_finite_sequence_space_separation_exists (.fvar .here)).satisfies
      (templateEnv (.cons source .nil) : Env 𝒩 [] [s]) ↔
      ∃ output, (nonempty_finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here)).satisfies
        (templateEnv (.cons output (.cons source .nil)) : Env 𝒩 [] [s,s]) := by
  simp only [nonempty_finite_sequence_space_separation_exists, Formula.satisfies_existsFreeTop]
  rfl

theorem nonempty_sequence_space (hℳ : Theory.Models ℳ theory) :
    nonempty_finite_sequence_space_separation_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply (fromRoundTwoSentence hℳ _ rfl).mp
  apply close_of_curried
  intro source
  apply (nonempty_semantics (PureRoundTwoStage.expansion hℳ).model source).mpr
  refine ⟨(PureRoundTwoStage.expansion hℳ).function .nonemptyFiniteSequenceSpace (.cons source .nil), ?_⟩
  exact (PureRoundTwoSpecifications.filter_specification hℳ .nonemptyFiniteSequenceSpace (.cons source .nil) _).mp rfl

def imageBody : SetOpenFormula [s,s,s] :=
  relation_image_member_condition (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)

theorem image_semantics (𝒩 : Structure.{0,0,0,x} S) (relation source target : 𝒩.Carrier s) :
    (relation_image_separation_exists (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons target (.cons source (.cons relation .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ∃ output, ∀ element, Mem 𝒩 element output ↔ Mem 𝒩 element target ∧
        imageBody.satisfies (templateEnv (.cons element (.cons source (.cons relation .nil))) : Env 𝒩 [] [s,s,s]) := by
  simp only [relation_image_separation_exists, relation_image_separation_spec, membership_specification,
    Formula.satisfies_existsFreeTop, Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

theorem relation_image (hℳ : Theory.Models ℳ theory) :
    relation_image_separation_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro target source relation
  apply (image_semantics (E hℳ).model relation source target).mpr
  obtain ⟨output, hOutput⟩ := PureSeparation.exists_subset hℳ
    (openFormula PureCompletedStage.interpretation imageBody)
    (mapValues PureCompletedStage.interpretation (.cons source (.cons relation .nil))) target
  refine ⟨output, fun element => ?_⟩
  exact (hOutput element).trans (and_congr Iff.rfl
    (openFormula_correct (E hℳ) (PureCompletedStage.realizes hℳ) imageBody
      (.cons element (.cons source (.cons relation .nil)))))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalSeparation
