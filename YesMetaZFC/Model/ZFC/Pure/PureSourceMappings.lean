import YesMetaZFC.Model.ZFC.Pure.PureSourceBounds

/-! # 任意原模型中集合函数图的对应

先确定同一个 Kuratowski 有序对，再把原映射及合法求值解释为纯集合函数。
求值对应只用于原定义域内，不约束非法输入上的总化值。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceMappings
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

abbrev ordered (𝒩 : Structure.{0,0,0,x} signature) (a b : 𝒩.Carrier .set) :=
  𝒩.funcInterp .orderedPair (.cons a (.cons b .nil))
abbrev value (𝒩 : Structure.{0,0,0,x} signature) (f a : 𝒩.Carrier .set) :=
  𝒩.funcInterp .application (.cons f (.cons a .nil))
abbrev domain (𝒩 : Structure.{0,0,0,x} signature) (f : 𝒩.Carrier .set) :=
  𝒩.funcInterp .domain (.cons f .nil)
abbrev Mapping (𝒩 : Structure.{0,0,0,x} signature) (f a b : 𝒩.Carrier .set) :=
  𝒩.relInterp .isMapping (.cons f (.cons a (.cons b .nil)))

theorem ordered_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (a b : 𝒩.Carrier .set) :
    PureKuratowski.Code (PureProjectEmbedding.reduct 𝒩) (ordered 𝒩 a b) a b := by
  have hSingle := (Derives.theory_weaken
    (fun h => intrinsic_zfc_arithmetic_support.contains_ordered_pair
      (singleton_operator_theory_subset_ordered_pair_operator_theory h))
    (singleton_term_spec_derives (Γ := []) (.fvar .here : SetOpenTerm [.set]))).sound
      h𝒩 (templateEnv (.cons a .nil)) (by intro φ h; cases h)
  have hPair := (Derives.theory_weaken
    (fun h => intrinsic_zfc_arithmetic_support.contains_ordered_pair
      (singleton_operator_theory_subset_ordered_pair_operator_theory (Or.inr h)))
    (unordered_pair_term_spec_derives (Γ := []) (.fvar .here : SetOpenTerm [.set,.set])
      (.fvar (.there .here)))).sound h𝒩 (templateEnv (.cons a (.cons b .nil)))
      (by intro φ h; cases h)
  have hOrdered := (Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_ordered_pair
    (ordered_pair_term_spec_derives (Γ := []) (.fvar .here : SetOpenTerm [.set,.set])
      (.fvar (.there .here)))).sound h𝒩 (templateEnv (.cons a (.cons b .nil)))
      (by intro φ h; cases h)
  simp only [singleton_spec, ordered_pair_spec, pair_spec, membership_specification,
    pair_member_condition, Formula.satisfies_forallFreeTop,
    Formula.satisfies, Arguments.eval, Term.eval_weakenFree] at hSingle hPair hOrdered
  exact ⟨𝒩.funcInterp .singleton (.cons a .nil),
    𝒩.funcInterp .unorderedPair (.cons a (.cons b .nil)), hSingle, hPair, hOrdered⟩

theorem ordered_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (a b : 𝒩.Carrier .set) :
    ordered 𝒩 a b = ordered (canonical h𝒩) a b :=
  (PureFinalPairs.ordered_value (PureZFCModels.reduct_models h𝒩) a b _).mpr (ordered_code h𝒩 a b)

theorem pair_member (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (a b f : 𝒩.Carrier .set) :
    mem 𝒩 (ordered 𝒩 a b) f ↔ PureKuratowski.PairMember (PureProjectEmbedding.reduct 𝒩) a b f := by
  rw [ordered_agrees h𝒩]
  exact PureFinalPairs.pair_member (PureZFCModels.reduct_models h𝒩) a b f

theorem ordered_predicate (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (a : 𝒩.Carrier .set) :
    𝒩.relInterp .isOrderedPair (.cons a .nil) ↔
      ∃ left right, PureKuratowski.Code (PureProjectEmbedding.reduct 𝒩) a left right := by
  have h := (Derives.theory_weaken
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_function_theory_subset_function_predicate_theory h))
    (is_ordered_pair_definition_instance_derives (Γ := []) (.fvar .here : SetOpenTerm [.set]))).sound
      h𝒩 (templateEnv (.cons a .nil)) (by intro φ h; cases h)
  change (𝒩.relInterp .isOrderedPair (.cons a .nil) ↔
    (is_ordered_pair_condition (.fvar .here)).satisfies (templateEnv (.cons a .nil) : Env 𝒩 [] [.set])) at h
  refine h.trans ((PureFinalPairs.ordered_condition_semantics 𝒩 a).trans ?_)
  apply exists_congr; intro left
  apply exists_congr; intro right
  change a = ordered 𝒩 left right ↔ _
  rw [ordered_agrees h𝒩]
  exact PureFinalPairs.ordered_value (PureZFCModels.reduct_models h𝒩) left right a

theorem relation_predicate (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (f : 𝒩.Carrier .set) :
    𝒩.relInterp .isRelation (.cons f .nil) ↔
      PureKuratowski.IsRelation (PureProjectEmbedding.reduct 𝒩) f := by
  have h := (Derives.theory_weaken
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_predicate_theory_subset_function_predicate_theory h))
    (is_relation_definition_instance_derives (Γ := []) (.fvar .here : SetOpenTerm [.set]))).sound
      h𝒩 (templateEnv (.cons f .nil)) (by intro φ h; cases h)
  change (𝒩.relInterp .isRelation (.cons f .nil) ↔
    (is_relation_condition (.fvar .here)).satisfies (templateEnv (.cons f .nil) : Env 𝒩 [] [.set])) at h
  exact h.trans ((PureFinalPairs.relation_condition_semantics 𝒩 f).trans
    (forall_congr' (fun element => imp_congr Iff.rfl (ordered_predicate h𝒩 element))))

theorem function_predicate (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (f : 𝒩.Carrier .set) :
    𝒩.relInterp .isFunction (.cons f .nil) ↔
      PureKuratowski.IsFunction (PureProjectEmbedding.reduct 𝒩) f := by
  have h := (Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_function_predicate
    (is_function_iff_condition (Γ := []) (.fvar .here : SetOpenTerm [.set]))).sound
      h𝒩 (templateEnv (.cons f .nil)) (by intro φ h; cases h)
  refine h.trans ((PureFinalMappings.function_semantics 𝒩 f).trans ?_)
  constructor
  · rintro ⟨hRel, hUnique⟩
    exact ⟨(relation_predicate h𝒩 f).mp hRel, fun input left right hl hr =>
      hUnique input left right ⟨(pair_member h𝒩 _ _ _).mpr hl, (pair_member h𝒩 _ _ _).mpr hr⟩⟩
  · rintro ⟨hRel, hUnique⟩
    exact ⟨(relation_predicate h𝒩 f).mpr hRel, fun input left right hs =>
      hUnique input left right ((pair_member h𝒩 _ _ _).mp hs.1) ((pair_member h𝒩 _ _ _).mp hs.2)⟩

theorem application_graph (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {f input : 𝒩.Carrier .set} (hFunction : 𝒩.relInterp .isFunction (.cons f .nil))
    (hInput : mem 𝒩 input (domain 𝒩 f)) :
    PureKuratowski.PairMember (PureProjectEmbedding.reduct 𝒩) input (value 𝒩 f input) f := by
  have h := (Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_function_application
    (function_application_eq_iff_graph (Γ := []) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here : SetOpenTerm [.set,.set,.set]))).sound
      h𝒩 (templateEnv (.cons (value 𝒩 f input) (.cons input (.cons f .nil)))) (by intro φ h; cases h)
  exact (pair_member h𝒩 _ _ _).mp ((h ⟨hFunction, hInput⟩).mp rfl)

theorem domain_member (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {f : 𝒩.Carrier .set} (hFunction : 𝒩.relInterp .isFunction (.cons f .nil)) (input : 𝒩.Carrier .set) :
    mem 𝒩 input (domain 𝒩 f) ↔
      ∃ output, PureKuratowski.PairMember (PureProjectEmbedding.reduct 𝒩) input output f := by
  constructor
  · intro hInput; exact ⟨_, application_graph h𝒩 hFunction hInput⟩
  · rintro ⟨output, hGraph⟩
    have h := (Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_member_left_coordinate_mem_domain (Γ := []) (.fvar (.there (.there .here)))
        (.fvar (.there .here)) (.fvar .here : SetOpenTerm [.set,.set,.set]))).sound
        h𝒩 (templateEnv (.cons output (.cons input (.cons f .nil)))) (by intro φ h; cases h)
    exact h ((relation_predicate h𝒩 f).mpr ((function_predicate h𝒩 f).mp hFunction).1)
      ((pair_member h𝒩 _ _ _).mpr hGraph)

theorem mapping_condition (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (f source target : 𝒩.Carrier .set) :
    Mapping 𝒩 f source target ↔ 𝒩.relInterp .isFunction (.cons f .nil) ∧
      source = domain 𝒩 f ∧ 𝒩.relInterp .subset
        (.cons (𝒩.funcInterp .range (.cons f .nil)) (.cons target .nil)) := by
  exact (Derives.theory_weaken
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_application
      (mapping_predicate_theory_subset_function_application_theory h))
    (is_mapping_iff_condition (Γ := []) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here : SetOpenTerm [.set,.set,.set]))).sound
      h𝒩 (templateEnv (.cons target (.cons source (.cons f .nil)))) (by intro φ h; cases h)

/-- 原映射在同一个纯隶属模型中确为具有精确定义域的集合函数。 -/
theorem mapping_project (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {f source target : 𝒩.Carrier .set} (hMapping : Mapping 𝒩 f source target) :
    PureMappingDefinitions.IsMapping (PureProjectEmbedding.reduct 𝒩) f source target := by
  obtain ⟨hFunction, hSource, _⟩ := (mapping_condition h𝒩 f source target).mp hMapping
  refine ⟨(function_predicate h𝒩 f).mp hFunction, ?_, ?_⟩
  · intro input; rw [hSource]; exact domain_member h𝒩 hFunction input
  · intro input hInput
    have hDomain : mem 𝒩 input (domain 𝒩 f) := hSource ▸ hInput
    have h := (Derives.theory_weaken intrinsic_zfc_arithmetic_support.contains_function_application
      (is_mapping_application_mem_target (Γ := []) (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there .here))) (.fvar (.there .here))
        (.fvar .here : SetOpenTerm [.set,.set,.set,.set]))).sound
        h𝒩 (templateEnv (.cons input (.cons target (.cons source (.cons f .nil))))) (by intro φ h; cases h)
    exact ⟨_, h hMapping hDomain, application_graph h𝒩 hFunction hDomain⟩

theorem application_value (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {f source target input : 𝒩.Carrier .set} (hMapping : Mapping 𝒩 f source target)
    (hInput : mem 𝒩 input source) :
    value 𝒩 f input = PureNaturalInduction.value (PureZFCModels.reduct_models h𝒩) f input := by
  have hCondition := (mapping_condition h𝒩 f source target).mp hMapping
  have hPure := mapping_project h𝒩 hMapping
  exact hPure.1.2 input _ _ (application_graph h𝒩 hCondition.1 (hCondition.2.1 ▸ hInput))
    (PureNaturalInduction.application_member (PureZFCModels.reduct_models h𝒩) hPure hInput)

theorem application_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {f source target input : 𝒩.Carrier .set} (hMapping : Mapping 𝒩 f source target)
    (hInput : mem 𝒩 input source) : value 𝒩 f input = value (canonical h𝒩) f input := by
  rw [application_value h𝒩 hMapping hInput]
  exact (PureFinalTransfer.functionFromDifference (PureZFCModels.reduct_models h𝒩) _ rfl _).symm

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceMappings
