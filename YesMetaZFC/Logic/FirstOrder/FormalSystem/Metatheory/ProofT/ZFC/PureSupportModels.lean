import YesMetaZFC.Automation.FiniteBasisModels
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportAxiomBasis
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalOperations
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalInfinity
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalSeparation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalRelations
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalExtrema
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFinalSyntax

/-! # 裸 ZFC 的最终扩张满足整个原支撑理论

逐项消费原闭句的验证定理，再沿原理论的有限公理基结构组合。
参数分离族由闭模板的普通推导覆盖，因此结论包含所有参数实例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSupportModels
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

private theorem parameter_models (hℳ : Theory.Models ℳ theory) (kind : SupportParameters.Kind) :
    Theory.Models (E hℳ).model (SupportAssembly.parameterBasis kind).theory := by
  intro φ hφ
  have hEqual : φ = SupportAssembly.closedTemplate kind := List.mem_singleton.mp hφ
  exact hEqual.symm ▸ PureSupportSeparation.parameter_template hℳ kind

/-- 任意裸 ZFC 模型的规范扩张满足全部原支撑公理及其无限参数族。 -/
theorem support_models (hℳ : Theory.Models ℳ theory) :
    Theory.Models (E hℳ).model intrinsic_proof_theory := by
  apply (FiniteAxiomBasis.models_iff SupportAxiomBasis.intrinsic_proof (E hℳ).model).mp
  finite_basis_models [
    PureFinalBasic.extensionality_axiom hℳ,
    PureFinalBasic.pairing_exists hℳ,
    PureFinalBasic.pairing hℳ,
    PureFinalBasic.union_exists_axiom hℳ,
    PureFinalBasic.union_definition hℳ,
    PureFinalBasic.binary_union hℳ,
    PureFinalBasic.successor hℳ,
    PureFinalBasic.singleton hℳ,
    PureFinalPairs.ordered_pair hℳ,
    PureFinalPairs.is_ordered_pair hℳ,
    PureFinalPairs.left_projection hℳ,
    PureFinalPairs.right_projection hℳ,
    PureFinalPairs.is_relation hℳ,
    PureFinalMappings.domain hℳ,
    PureFinalMappings.range hℳ,
    PureFinalBasic.subset hℳ,
    PureFinalBasic.power_exists_axiom hℳ,
    PureFinalBasic.power_definition hℳ,
    PureFinalCollections.cartesian_product hℳ,
    PureFinalPairs.reverse hℳ,
    PureFinalOperations.converse hℳ,
    PureFinalOperations.composition hℳ,
    PureFinalRelations.is_equivalence_relation hℳ,
    PureFinalMappings.is_function hℳ,
    PureFinalMappings.is_mapping hℳ,
    PureFinalMappings.application hℳ,
    PureFinalRelations.is_injective hℳ,
    PureFinalRelations.is_surjective hℳ,
    PureFinalRelations.is_bijection hℳ,
    PureFinalCollections.identity hℳ,
    PureFinalCollections.mapping_collection hℳ,
    PureFinalRelations.is_transitive_set hℳ,
    PureSupportSeparation.separation_axiom hℳ membership_relation_predicate,
    PureFinalOperations.membership_relation hℳ,
    PureFinalRelations.is_linear_order hℳ,
    PureFinalRelations.is_order_isomorphism hℳ,
    PureFinalRelations.is_order_isomorphic hℳ,
    PureFinalRelations.is_order_embedding hℳ,
    PureFinalRelations.is_order_embeddable hℳ,
    PureFinalRelations.is_natural_discrete_linear_order hℳ,
    PureFinalRelations.well_order hℳ,
    PureFinalSeparation.relation_image hℳ,
    PureFinalOperations.image hℳ,
    PureFinalCollections.restriction hℳ,
    PureFinalExtrema.minimum_linear_order hℳ,
    PureFinalExtrema.minimum_natural_order hℳ,
    PureFinalExtrema.maximum_natural_order hℳ,
    PureFinalConstructions.minimum_difference hℳ,
    PureFinalConstructions.index_order hℳ,
    PureFinalConstructions.power_set_bijection hℳ,
    PureFinalOperations.symmetric_difference hℳ,
    PureFinalRelations.is_finite hℳ,
    PureFinalRelations.is_equinumerous hℳ,
    PureFinalRelations.cardinality_leq hℳ,
    PureFinalRelations.cardinality_strict_less hℳ,
    PureFinalRelations.is_dedekind_finite hℳ,
    PureFinalInfinity.infinity hℳ,
    PureFinalRelations.is_inductive_set hℳ,
    PureFinalInfinity.inductive_core hℳ,
    PureFinalInfinity.omega hℳ,
    PureFinalRelations.unbounded_subset hℳ,
    PureFinalRelations.bounded_subset hℳ,
    PureFinalConstructions.natural_order_type hℳ,
    PureFinalConstructions.natural_subset_type hℳ,
    PureFinalConstructions.natural_addition hℳ,
    PureFinalConstructions.natural_multiplication hℳ,
    PureFinalConstructions.natural_exponentiation hℳ,
    PureFinalConstructions.godel_pairing hℳ,
    PureFinalArithmetic.exponent_axiom hℳ,
    PureFinalArithmetic.exponent_product_axiom hℳ,
    PureFinalArithmetic.addition_upper_axiom hℳ,
    PureFinalArithmetic.positive_addition_axiom hℳ,
    PureFinalArithmetic.transitivity_axiom hℳ,
    PureFinalArithmetic.pairing_axiom hℳ,
    PureFinalSyntax.structural_syntax hℳ,
    PureFinalBasic.irreflexivity hℳ,
    PureSupportSeparation.separation_axiom hℳ (empty_predicate (free := [])),
    PureFinalBasic.empty_set hℳ,
    PureFinalRelations.is_infinite hℳ,
    PureFinalRelations.is_countable hℳ,
    PureFinalRelations.is_uncountable hℳ,
    PureFinalRelations.is_countably_infinite hℳ,
    PureFinalConstructions.finite_sequence_space hℳ,
    PureFinalConstructions.recursive_sequence_space hℳ,
    PureFinalConstructions.omega_recursive_sequence hℳ,
    PureFinalConstructions.natural_difference hℳ,
    PureFinalRelations.omega_pair_less hℳ,
    PureFinalConstructions.transitive_closure hℳ,
    PureFinalConstructions.finite_hierarchy hℳ,
    PureFinalConstructions.finite_universe hℳ,
    PureFinalRelations.hereditarily_finite hℳ,
    PureFinalSeparation.finite_subset_collection hℳ,
    PureFinalConstructions.finite_subset_collection hℳ,
    PureFinalConstructions.finite_sequence_concatenation hℳ,
    PureFinalSeparation.nonempty_sequence_space hℳ,
    PureFinalConstructions.nonempty_finite_sequence_space hℳ,
    PureFinalConstructions.finite_sequence_flatten hℳ,
    PureFinalSyntax.free_variable_occurs hℳ,
    PureFinalSyntax.syntax_transform hℳ,
    PureFinalSyntax.schema_axioms hℳ,
    PureFinalSyntax.logical_axioms hℳ,
    PureFinalSyntax.modus_ponens hℳ,
    PureFinalSyntax.nonlogical_symbols hℳ,
    PureFinalSyntax.related_syntax hℳ,
    PureFinalSyntax.structure_axiom hℳ,
    PureFinalSyntax.term_value hℳ,
    PureFinalSyntax.term_list_value hℳ,
    parameter_models hℳ .domain,
    parameter_models hℳ .range,
    parameter_models hℳ .cartesianProduct,
    parameter_models hℳ .converse,
    parameter_models hℳ .composition,
    parameter_models hℳ .identity,
    parameter_models hℳ .mappingCollection,
    parameter_models hℳ .indexOrder,
    parameter_models hℳ .powerSetBijection,
    parameter_models hℳ .symmetricDifference,
    parameter_models hℳ .inductiveCore
  ]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSupportModels
