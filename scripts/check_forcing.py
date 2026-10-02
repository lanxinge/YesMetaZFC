"""审计力迫偏序、布尔完备化、名称解释与相对扩张，不引入测试用 Lean 模块。

稠密性证书在 Prop 内使用经典逻辑；规范映射函数和布尔运算分别严格审计。
"""
import sys

from check_filters import ROOT, main

# 模块路径按功能目录组织；数学声明仍使用原命名空间。
MODULE_PREFIX = "YesMetaZFC.Model.Forcing."

ZFC_BASELINE = [f"YesMetaZFC.SetTheory.Axioms.{n}._native.native_decide.ax_1"
                for n in ("extensionality", "emptySet", "foundation", "infinity")]
INTERNAL_BASELINE = [f"YesMetaZFC.SetTheory.Axioms.{n}._native.native_decide.ax_1"
                     for n in ("emptySet", "extensionality", "foundation", "infinity", "pairing", "powerSet", "union")]
CHOICE_BASELINE = INTERNAL_BASELINE + ["YesMetaZFC.SetTheory.Axioms.choice._native.native_decide.ax_1"]

MODULES = [MODULE_PREFIX + n for n in (
    "Applications.Cohen.Algebra", "Applications.Cohen.Internal", "Applications.Cohen.Real",
    "Boolean.Completion", "Boolean.Conditions", "Boolean.Generic", "Boolean.Internal", "Boolean.RegularOpen",
    "External.Domain", "External.Extension", "External.Formula", "External.FormulaEnumeration",
    "External.FormulaGeneric", "External.Generic", "External.NameGeneric", "External.RealName",
    "External.Truth", "External.Valuation", "Internal.Atomic.Syntax", "Internal.Check.Basic",
    "Internal.Check.Realization", "Internal.Check.Syntax", "Internal.Check.Valuation",
    "Internal.Extension.Generic", "Internal.Extension.Instance", "Internal.Forcing.Formula",
    "Internal.Ground.Graph", "Internal.Names.Basic", "Internal.Names.Graph",
    "Internal.Names.Realization", "Order.Basic", "Order.Density", "Order.Separative", "Order.Tree",
)] + [
    "YesMetaZFC.Model.SetTheory.CountableSyntax",
    "YesMetaZFC.Model.SetTheory.ProjectBounded",
    "YesMetaZFC.SetTheory.Definitional.Language",
    "YesMetaZFC.SetTheory.Definitional.Project.Predicate",
]

ZFC_MODULES = [MODULE_PREFIX + n for n in (
    "Applications.Cohen.Theory", "External.ZFCBase",
)]

INTERNAL_MODULES = [MODULE_PREFIX + n for n in (
    "Internal.Automorphism.Basic", "Internal.Automorphism.Names", "Internal.Automorphism.Atomic",
    "Internal.Automorphism.Forcing", "Applications.Cohen.FlipSyntax", "Applications.Cohen.Flip",
    "Internal.Ground.NameRank", "Internal.Ground.Ordinals", "Internal.Forcing.Finite",
    "Internal.Homogeneous.Basic", "Internal.Homogeneous.Definition", "Internal.Homogeneous.Truth",
    "Internal.Homogeneous.Recovery", "Internal.Homogeneous.OrdinalSubsets",
    "Applications.Cohen.Homogeneous", "Applications.Cohen.OrdinalSubsets",
    "Applications.Collapse.NameSyntax", "Applications.Collapse.NameUniqueness",
    "Applications.Collapse.RuleSyntax", "Closed.Sequence", "Closed.Syntax", "Internal.Atomic.Closure",
    "Internal.Atomic.Equivalence", "Internal.Atomic.Recursion", "Internal.Atomic.Truth",
    "Internal.Atomic.Witness", "Internal.Check.Application", "Internal.Check.Forcing", "Internal.Check.Model",
    "Internal.Check.Omega", "Internal.Check.Order", "Internal.Check.Relation", "Internal.Extension.Collection",
    "Internal.Extension.Foundation", "Internal.Extension.Operations", "Internal.Extension.Power",
    "Internal.Extension.Quotient", "Internal.Extension.Separation", "Internal.Extension.ZF",
    "Internal.Forcing.Conditions", "Internal.Forcing.Definability", "Internal.Forcing.Logic",
    "Internal.Forcing.Truth", "Internal.Functions.Basic", "Internal.Functions.Cover",
    "Internal.Functions.Decision", "Internal.Functions.Injection", "Internal.Functions.Rules",
    "Internal.Ground.Cofinality", "Internal.Ground.FiniteSequence", "Internal.Ground.Syntax",
    "Internal.Maximum.Hull", "Internal.Maximum.Normal", "Internal.Maximum.NormalSyntax",
    "Internal.Maximum.Selection", "Internal.Names.Closure", "Internal.Names.Construction",
    "Internal.Names.PairConstruction", "Internal.Names.Sequence", "Internal.Names.SequenceForcing",
    "Internal.Reflection.Transitive", "Iteration.Condition.Absoluteness", "Iteration.Names.Bounded",
    "Iteration.Names.Dense", "Iteration.Names.DenseProjection", "Iteration.Names.Generic",
    "Iteration.Names.GenericName", "Iteration.Names.Inclusion", "Iteration.Names.NameOrder",
    "Iteration.Names.ProjectionName", "Iteration.Names.Quotient", "Iteration.Names.QuotientComparison",
    "Iteration.Names.QuotientEntry", "Iteration.Names.QuotientOrder", "Iteration.Names.QuotientTransfer",
    "Iteration.Names.Representation", "Iteration.Names.Selection", "Iteration.Proper.Ground",
    "Iteration.Proper.Lemma", "Iteration.Proper.Natural", "Iteration.Proper.Prefix.Comparison",
    "Iteration.Proper.Prefix.Limit", "Iteration.Proper.Prefix.Step", "Iteration.Proper.Thread.Bounds",
    "Iteration.Proper.Thread.Coherence", "Iteration.Proper.Thread.Comparison", "Iteration.Proper.Thread.Order",
    "Iteration.Proper.Thread.Realization", "Iteration.Proper.Thread.Syntax", "Iteration.Proper.Thread.Tail",
    "Proper.Elementary.Cofinal", "Proper.Elementary.FirstPreimage", "Proper.Elementary.Membership",
    "Proper.Elementary.RelationPreimage", "Proper.Elementary.Restriction", "Proper.Family.ClosedSyntax",
    "Proper.Family.IndexedLift", "Proper.Family.IndexedSyntax", "Proper.Family.Syntax",
    "Proper.Generic.Countable", "Proper.Generic.Elementary", "Proper.Generic.Evaluation",
    "Proper.Generic.Hull", "Proper.Generic.OperationLift", "Proper.Generic.Rule", "Proper.Generic.Sequence",
    "Proper.Generic.Witness", "Proper.Generic.WitnessReflection", "Proper.Generic.WitnessSyntax",
    "Proper.Hereditary.Value", "Proper.Master.Map", "Proper.Master.Name", "TwoStep.Class",
    "TwoStep.Proper.Projection", "TwoStep.Proper.Pull",
)] + [
    "YesMetaZFC.SetTheory.Card.Aleph.Hartogs",
    "YesMetaZFC.SetTheory.Card.Cofinality.Basic",
    "YesMetaZFC.SetTheory.Card.Cofinality.Countable",
    "YesMetaZFC.SetTheory.Card.Cofinality.LimitLength",
    "YesMetaZFC.SetTheory.Card.CountablePair",
    "YesMetaZFC.SetTheory.Card.FiniteOrdinal",
    "YesMetaZFC.SetTheory.CountableCofinal",
    "YesMetaZFC.SetTheory.Cumulative",
    "YesMetaZFC.SetTheory.CumulativeRank",
    "YesMetaZFC.SetTheory.CumulativeSelection",
    "YesMetaZFC.SetTheory.FunctionCoordinates",
    "YesMetaZFC.SetTheory.IndexedIteration",
    "YesMetaZFC.SetTheory.MembershipInduction",
    "YesMetaZFC.SetTheory.Ord.Recursion",
    "YesMetaZFC.SetTheory.RelationChain",
]

CHOICE_MODULES = [MODULE_PREFIX + n for n in (
    "Internal.Extension.Choice",
)] + [
    "YesMetaZFC.Model.SetTheory.ClassChoice",
    "YesMetaZFC.SetTheory.Choice",
    "YesMetaZFC.SetTheory.CollectionChoice",
]

CH_MODULES = [MODULE_PREFIX + n for n in (
    "Applications.Collapse.Basic", "Applications.Collapse.Generic", "Applications.Continuum.CH",
    "Closed.Basic", "Closed.NoNewReals", "Internal.Ground.Transfer",
)] + [
    "YesMetaZFC.Model.SetTheory.Countable",
    "YesMetaZFC.Model.SetTheory.CountableGround",
    "YesMetaZFC.SetTheory.Card.CountableUnion",
    "YesMetaZFC.SetTheory.Card.Omega",
    "YesMetaZFC.SetTheory.Continuum",
    "YesMetaZFC.SetTheory.DependentChoice",
]

COHEN_MODULES = [MODULE_PREFIX + n for n in (
    "Applications.Cohen.Add", "Applications.Cohen.Coordinates", "Applications.Continuum.Independence",
    "Applications.Continuum.NotCH", "CCC.Basic", "CCC.Bounds", "Internal.Functions.Generic",
)] + [
    "YesMetaZFC.Model.SetTheory.ProjectSoundness",
    "YesMetaZFC.SetTheory.Card.Finite",
    "YesMetaZFC.SetTheory.Fiber",
    "YesMetaZFC.SetTheory.PartialFunction",
    "YesMetaZFC.SetTheory.PartialFunctionCCC",
]

ITERATION_MODULES = [MODULE_PREFIX + n for n in (
    "Applications.Cohen.CountableSupport", "Applications.Cohen.FiniteSupport", "Applications.Cohen.NameSyntax",
    "Applications.Cohen.Names", "Applications.Cohen.Presentation", "Applications.Cohen.Proper",
    "Applications.Cohen.Successor", "Applications.Cohen.TwoStep", "Applications.Collapse.Closed",
    "Applications.Collapse.Iteration", "Applications.Collapse.Names", "Applications.Collapse.Presentation",
    "Applications.Collapse.Proper", "Applications.Collapse.Rule", "CCC.Name", "CCC.Predense", "CCC.Syntax",
    "Closed.Extension", "Closed.Function", "Closed.Master", "Closed.Name", "Closed.NoNewCountable",
    "Closed.NoNewFunctions", "Closed.Proper", "Closed.ProperName", "Internal.Forcing.Congruence",
    "Internal.Forcing.OrderCongruence", "Internal.Forcing.Rules", "Internal.Maximum.Basic",
    "Internal.Maximum.Bounded", "Internal.Maximum.Member", "Internal.Maximum.Mixing", "Internal.Maximum.Pool",
    "Internal.Maximum.Unique", "Internal.Maximum.UniqueRules", "Internal.Maximum.WitnessPool",
    "Internal.Names.Depth", "Internal.Names.PairForcing", "Internal.Reflection.Countable",
    "Internal.Reflection.Countermodel", "Internal.Reflection.Criterion", "Iteration.Closed.Extension",
    "Iteration.Closed.Fusion", "Iteration.Closed.Induction", "Iteration.Closed.Interval",
    "Iteration.Closed.Limit", "Iteration.Closed.Rule", "Iteration.Closed.Successor", "Iteration.Closed.Thread",
    "Iteration.Condition.Basic", "Iteration.Condition.Operations", "Iteration.Condition.Projection",
    "Iteration.Condition.Splice", "Iteration.Condition.Support", "Iteration.FiniteSupport.Amalgamation",
    "Iteration.FiniteSupport.AmalgamationSyntax", "Iteration.FiniteSupport.CCC",
    "Iteration.FiniteSupport.CCCBound", "Iteration.FiniteSupport.CCCSyntax",
    "Iteration.FiniteSupport.DirectUnion", "Iteration.FiniteSupport.RecursionCCC",
    "Iteration.FiniteSupport.SuccessorCCC", "Iteration.FiniteSupport.SystemCCC",
    "Iteration.FiniteSupport.Tail", "Iteration.Fusion.Basic", "Iteration.Fusion.Countable",
    "Iteration.Fusion.Restriction", "Iteration.Fusion.Syntax", "Iteration.Limit.Basic",
    "Iteration.Limit.Order", "Iteration.Limit.Projection", "Iteration.Limit.Syntax",
    "Iteration.Names.DenseName", "Iteration.Names.Witness", "Iteration.Proper.Dense",
    "Iteration.Proper.Extension", "Iteration.Proper.Induction", "Iteration.Proper.Limit",
    "Iteration.Proper.Master", "Iteration.Proper.Model.Basic", "Iteration.Proper.Model.Family",
    "Iteration.Proper.Model.Rule", "Iteration.Proper.Model.Sequence", "Iteration.Proper.Model.Support",
    "Iteration.Proper.Model.Witness", "Iteration.Proper.Omega", "Iteration.Proper.Preservation",
    "Iteration.Proper.Successor", "Iteration.Proper.SuccessorGeneric", "Iteration.Proper.Thread.Basic",
    "Iteration.Proper.Thread.Fusion", "Iteration.Proper.Thread.Limit", "Iteration.Proper.Thread.Master",
    "Iteration.Proper.Thread.Omega", "Iteration.Proper.Thread.Step", "Iteration.Recursion.Basic",
    "Iteration.Recursion.History", "Iteration.Recursion.Invariant", "Iteration.Recursion.InvariantSyntax",
    "Iteration.Recursion.Rule", "Iteration.Recursion.Step", "Iteration.Recursion.Syntax",
    "Iteration.Stage.Basic", "Iteration.Stage.Embedding", "Iteration.Stage.Next", "Iteration.Stage.Successor",
    "Iteration.Stage.System", "Iteration.Stage.SystemSuccessor", "Iteration.Stage.SystemSyntax", "Proper.Base",
    "Proper.Basic", "Proper.Elementary.Club", "Proper.Elementary.Countable", "Proper.Elementary.Inverse",
    "Proper.Elementary.RowMap", "Proper.Family.Basic", "Proper.Family.ClosedForcing",
    "Proper.Family.ClosedLift", "Proper.Family.Forcing", "Proper.Family.Indexed", "Proper.Family.IndexedHull",
    "Proper.Family.Trace", "Proper.Forcing", "Proper.Generic.AtomicDecision", "Proper.Generic.ElementaryHull",
    "Proper.Generic.ElementaryOn", "Proper.Generic.Ground", "Proper.Generic.Member",
    "Proper.Generic.Operations", "Proper.Generic.Successor", "Proper.Generic.WitnessHull",
    "Proper.Hereditary.Atomic", "Proper.Hereditary.AtomicWitness", "Proper.Hereditary.Cardinal",
    "Proper.Hereditary.Correspondence", "Proper.Hereditary.Hull", "Proper.Hereditary.NameBound",
    "Proper.Hereditary.NameChoice", "Proper.Hereditary.NameReduction", "Proper.Master.Basic",
    "Proper.Master.CCC", "Proper.Master.Syntax", "Proper.Name", "Proper.Preservation.Cofinality",
    "Proper.Preservation.Countable", "Proper.Preservation.Cover", "Proper.Preservation.CoverValue",
    "Proper.Preservation.Injection", "Proper.Syntax", "Stage.Atomic.Basic", "Stage.Atomic.Pull",
    "Stage.Atomic.Push", "Stage.Atomic.Syntax", "Stage.CCC", "Stage.Composition", "Stage.Embedding",
    "Stage.Extension", "Stage.Generic", "Stage.NameMap.Basic", "Stage.NameMap.Composition",
    "Stage.NameMap.Construction", "Stage.NameMap.Identity", "Stage.NameMap.Syntax", "Stage.Names",
    "Stage.Reduction", "Stage.Transport", "TwoStep.Atomic.Match", "TwoStep.Atomic.Pull",
    "TwoStep.Atomic.PullMatch", "TwoStep.Atomic.PullSyntax", "TwoStep.Atomic.Push", "TwoStep.Atomic.Syntax",
    "TwoStep.Atomic.Witness", "TwoStep.Basic", "TwoStep.CCC.Forcing", "TwoStep.CCC.Index",
    "TwoStep.CCC.IndexCountable", "TwoStep.CCC.IndexSyntax", "TwoStep.CCC.Preservation", "TwoStep.Closed",
    "TwoStep.Embedding", "TwoStep.Flatten.Construction", "TwoStep.Flatten.Recursion", "TwoStep.Flatten.Round",
    "TwoStep.Flatten.RoundMatch", "TwoStep.Flatten.RoundSyntax", "TwoStep.Flatten.Syntax",
    "TwoStep.Flatten.Value", "TwoStep.Generic.Composition", "TwoStep.Generic.DenseImage",
    "TwoStep.Generic.Density", "TwoStep.Generic.Projection", "TwoStep.Generic.Recovery",
    "TwoStep.Generic.Second", "TwoStep.Names.Construction", "TwoStep.Names.Forcing",
    "TwoStep.Names.Interpretation", "TwoStep.Names.Isomorphism", "TwoStep.Names.Recursion",
    "TwoStep.Names.Syntax", "TwoStep.Names.Valuation", "TwoStep.Order", "TwoStep.Presentation",
    "TwoStep.Proper.Composition", "TwoStep.Proper.Decision", "TwoStep.Proper.Decomposition",
    "TwoStep.Proper.Extension", "TwoStep.Proper.Image", "TwoStep.Proper.Second", "TwoStep.Proper.SecondValue",
    "TwoStep.Proper.Selection", "TwoStep.Proper.Witness", "TwoStep.Top", "TwoStep.Witness",
)] + [
    "YesMetaZFC.Model.SetTheory.ProjectElementary",
    "YesMetaZFC.Model.SetTheory.ProjectExtensional",
    "YesMetaZFC.Model.SetTheory.ProjectReflection",
    "YesMetaZFC.SetTheory.BinaryWitnessClub",
    "YesMetaZFC.SetTheory.CountableClub",
    "YesMetaZFC.SetTheory.CountableHull",
]

PREFIX = "YesMetaZFC.Model.Forcing."
CHOICE_FREE = [PREFIX + n for n in (
    "PO_pre", "PO_ord", "PO_hom", "PO_compat", "PO_dense",
    "Pos_l", "positive_order_l", "positive_nonempty_l", "positive_cmp_l",
    "positive_separative_l", "tree_order_l", "tree_cmp_l", "tree_length_dense_l",
    "binary_split_l", "binary_atomless_l", "binary_antichain_l",
    "Cohen_l", "cohen_algebra_l",
    "PO_filter", "PO_filter.principal_l", "PO_filter.sequence_l",
    "BF_meets_l", "boolean_filter_l", "boolean_filter_proper_l",
    "sup_dense_l", "sup_dense_lower_l", "inf_mem_iff_l", "meet_mem_iff_l",
    "val_graph_l", "val_l", "val_mem_l", "check_graph_l", "val_check_l",
    "check_exists_l", "val_surjective_l",
    "mem_dense_l", "eq_dense_l", "Name_generic_l", "name_dense_l", "name_dense_lower_l",
    "Name_domain_l", "name_span_l", "Ext_l", "ext_structure_l",
    "ext_transitive_l", "ext_extensional_l", "ext_wf_l", "ext_check_l",
    "nat_set_l", "real_name_l", "real_graph_l", "real_set_l", "val_real_l",
    "omega_enum_l", "omega_enum_surjective_l",
    "cohen_bit_l", "cohen_real_name_l", "cohen_avoid_l", "cohen_family_l",
    "cohen_node_enum_l", "cohen_node_surjective_l", "cohen_names_l",
    "cohen_ext_old_l", "cohen_ext_new_l",
    "cohen_ext_omega_l", "domain_str_l", "ext_model_l", "val_map_l", "val_map_surjective_l",
    "Fm_generic_l", "fm_dense_l", "fm_dense_lower_l", "Fm_query_l", "span_enum_l",
    "span_enum_surjective_l",
)] + [PREFIX + "PO_pre." + n for n in (
    "Cmp_l", "Inc_l", "Lower_l", "down_l", "Antichain_l", "Atomless_l",
    "Separative_l", "below_l", "Dense_below_l", "Dense_l", "Predense_below_l",
    "Predense_l", "Sep_le_l", "sep_pre_l", "sep_setoid_l", "Sep_l", "sep_mk_l",
    "sep_order_l", "sep_map_l", "sep_mk_le_l", "sep_mk_cmp_l",
    "ro_neg_l", "ro_reg_l", "ro_reg_idem_l", "RO_l", "ro_regularize_l",
    "ro_bot_l", "ro_meet_l", "ro_imp_l", "ro_sup_l", "ro_algebra_l",
    "ro_principal_l", "ro_principal_le_iff_l", "ro_principal_mono_l",
    "ro_principal_ne_bot_l", "ro_meet_eq_bot_l", "ro_condition_l", "ro_map_l",
)] + [PREFIX + "PO_dense." + n for n in ("id_l", "comp_l")]

CHOICE_FREE += [PREFIX + "Internal." + n for n in (
    "Pair_d", "KPair_d", "kpair_m", "kpair_convention_l", "kpair_interpretation_l",
    "Entry_d", "entry_ext_l", "Supp_d", "Name_d", "supp_m", "name_m", "name_entry_l", "name_empty_l",
    "Setlike_d", "node_l", "decode_graph_l", "Rep_d", "decode_rep_l", "decode_exists_l",
    "rep_child_l", "rep_val_eq_l", "Val_d", "val_exists_unique_l", "val_mem_l", "name_domain_l",
    "sg_kpair_l", "pair_graph_l", "kpair_graph_l", "encode_graph_l", "encode_set_l",
    "condition_set_l", "coded_graph_l", "encode_name_l", "encode_rep_l", "encode_val_l",
    "code_pred_l", "encode_pred_val_l", "sg_setlike_l", "sg_name_domain_l",
    "order_set_l", "order_mem_l", "meet_spec_l", "imp_spec_l", "boolean_model_l", "sup_exists_l",
    "binary_code_l", "cohen_code_graph_l", "cohen_condition_set_l",
    "cohen_order_set_l", "cohen_internal_name_l", "cohen_internal_name_spec_l",
    "Check_step_d", "Check_graph_d", "Check_d", "entry_m", "check_step_m", "check_graph_m",
    "check_m", "check_sat_l", "Check_ops_d", "check_unique_l", "check_mem_l", "check_union_l",
    "check_adjoin_l", "check_exists_l", "check_name_l", "check_entry_l", "check_injective_l",
    "check_mem_iff_l", "Ground_rep_d", "ground_node_l", "ground_graph_l", "ground_decode_l",
    "ground_rep_eq_l", "Ground_d", "check_val_l", "check_val_exists_l", "sg_mem_ind_l",
    "sg_check_range_l", "sg_ground_l", "sg_check_val_l",
    "Triple_d", "Rel_d", "Below_d", "Match_wit_d", "Match_d", "Bisim_d", "Eq_force_d",
    "triple_m", "rel_m", "below_m", "match_wit_m", "match_m", "bisim_m", "eq_force_m",
    "fenv_l", "param_shift_l", "name_shift_l", "neg_code_m", "imp_code_m", "all_code_m",
    "some_code_m", "mem_code_m", "eq_code_m", "force_code_m", "force_code_closed_l", "Code_d", "Forces_d",
    "two_code_l", "two_code_injective_l", "two_order_l", "two_conditions_l", "two_relation_l",
    "two_zero_l", "two_one_l", "two_filter_l", "two_generic_l",
)]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Definitional.TermVector." + n for n in
                ("ofFn", "get_ofFn", "ofFn_freeClosed", "boundParameters_freeClosed")]

INTERNAL_CHOICE_FREE = [PREFIX + "Internal." + n for n in (
    "Aut_d", "aut_m", "aut_m_freeClosed", "aut_sat_l", "aut_bij_l", "aut_of_bij_l", "aut_below_l",
    "Cflip_val_d", "Cflip_pair_d", "Cflip_d", "cflip_val_m", "cflip_pair_m", "cflip_m",
    "cflip_val_sat_l", "cflip_pair_sat_l", "cflip_sat_l", "cflip_val_symm_l", "cflip_val_unique_l",
    "cflip_val_target_l", "cflip_pair_symm_l", "cflip_pair_unique_l", "cflip_unique_l", "cflip_entry_l",
    "cflip_mono_l", "cflip_empty_l",
    "Whom_d", "whom_m", "whom_m_freeClosed", "whom_sat_l", "Gforce_d",
    "gforce_m", "gforce_closed_l", "gforce_sat_l", "od_member_s", "od_member_sat_l",
    "Entry_supp_d", "entry_supp_m", "Name_ops_d", "set_insert_l", "entry_union_l", "name_adjoin_l", "name_subset_l",
    "name_pair_l", "name_unfold_l", "name_support_l", "Triple_carrier_d", "Max_bisim_d",
    "Eq_match_d", "Mem_force_d", "mem_force_m", "Cond_order_d", "Dense_d", "Neg_d", "Lower_d", "Generic_d",
    "Defined_d", "neg_pred_m", "Wit_d", "Bad_d", "wit_m", "bad_m", "Regular_d", "Eval_d",
    "force_at_m", "force_at_closed_l", "force_all_m", "force_all_closed_l", "force_all_sat_l",
    "Source_d", "source_m", "Sub_name_d", "sub_name_m",
    "witness_m", "witness_closed_l",
    "Poss_mem_d", "Min_mem_d", "poss_mem_m", "min_mem_m",
    "Npair_d", "npair_m", "Nkpair_d", "nkpair_m",
    "Name_eq_d", "Name_quot_l", "Qval_d", "qmem_l", "name_quot_membership_l", "qenv_l",
    "qval_unique_l", "qval_name_l", "name_value_l", "value_name_l", "Min_name_d", "min_name_m",
    "Name_hull_d", "name_hull_m", "name_hull_unique_l",
    "All_eq_d", "all_eq_m", "norm_pred_s", "norm_env_l", "norm_args_l", "Norm_name_d", "norm_name_m",
    "Ng_source_d", "ng_source_m", "Ng_name_d", "ng_name_m", "Ng_mem_d",
    "Ng_pair_d", "ng_pair_m", "Ng_witness_d",
    "ng_decide_m", "ng_witness_m", "ng_data_m", "ng_exists_m",
    "Nseq_pair_d", "nseq_pair_m", "Nseq_d", "nseq_m", "nseq_unique_l",
    "Ng_rule_d", "ng_rule_m", "Ng_rule_has_d", "ng_rule_has_m", "Ng_rule_decide_d", "ng_rule_decide_m",
    "ng_elementary_env_l",
    "Nvalue_d", "nvalue_m", "Old_value_d", "old_value_m",
    "fn_body_m", "fn_body_closed_l", "Fn_name_d", "fn_name_m", "fn_name_closed_l",
    "Fst_pull_d", "fst_pull_m", "Ng_index_d", "ng_index_m", "Ng_index_op_d", "ng_index_op_m",
    "Ng_joint_d", "ng_joint_m", "ng_index_exists_m",
    "Rel_pull_d", "rel_pull_m", "mstr_body_m", "mstr_env_l", "mstr_lower_sub_l", "mstr_lower_s",
    "mstr_lower_exists_m", "hsub_body_m", "hsub_env_l", "hsub_force_m", "Hlift_d", "hlift_m",
    "Row_quot_d", "row_quot_m", "Row_pick_d", "row_pick_m", "Row_below_name_d", "row_below_name_m",
    "Prj_wit_d", "prj_wit_m", "Prj_set_d", "prj_case_m", "prj_set_m",
    "Gname_d", "gname_m",
    "Row_dec_d", "row_dec_m", "Row_quot_lower_d", "row_quot_lower_m",
    "Check_app_d", "check_app_m", "Row_proj_d", "row_proj_m",
    "Row_pil_d", "row_pil_m", "row_pil_id_l",
    "Row_cut_lower_d", "row_cut_lower_m", "row_cut_base_l", "Row_pil_stage_d", "row_pil_stage_m",
    "Row_pr_state_d", "row_pr_state_m", "Row_pr_move_d", "row_pr_move_m",
    "Row_pr_thread_d", "row_pr_thread_m", "Row_pr_advance_d", "row_pr_advance_m",
    "Step_named_d", "step_named_m", "step_named_sat_l", "Row_pr_bounds_d",
)]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Definitional.Project." + n for n in
                ("pred_m", "pred_sat_l", "binary_pred_m", "binary_pred_sat_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + n for n in ("image_env_l", "image_env_push_l", "eval_image_env_l", "delta0_image_l")]
INTERNAL_CHOICE_FREE += ["YesMetaZFC.SetTheory." + n for n in
                        ("V_step_d", "v_step_m", "v_op_l", "V_d", "v_m", "v_step_sat_l", "v_op_denote_l",
                         "v_sat_l", "v_step_unique_l", "v_ordinal_l", "v_empty_l", "V_bound_d", "v_bound_m",
                         "v_bound_sat_l", "V_hits_d", "V_min_d", "v_hits_m", "v_min_m", "v_min_congr_l")]
INTERNAL_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Ng_ops_d", "ng_ops_m", "ng_graph_m", "Ng_closed_d", "ng_closed_m")]
INTERNAL_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("cover_body_m", "cover_env_l", "cover_force_m", "Old_cover_d", "old_cover_m")]
INTERNAL_CHOICE_FREE += ["YesMetaZFC.SetTheory.Mem_ind_d",
                        "YesMetaZFC.SetTheory.Structure.IsSequenceOfLength.restriction",
                        "YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction",
                        "YesMetaZFC.SetTheory.Structure.IsRestrictionOf.comp_l"]
CH_CHOICE_FREE = [PREFIX + "Internal." + n for n in
                  ("Chain_d", "Closed_d", "Coll_d", "coll_m", "Dec_check_d", "dec_check_m")]
CH_CHOICE_FREE += ["YesMetaZFC.SetTheory." + n for n in
                   ("CH_d", "hartogs_m", "ch_m", "ch_sentence_l", "ZFC_CH",
                    "values_enum_l", "env_enum_l", "query_holds_l",
                    "ZFC.Next_d", "ZFC.next_m", "ZFC.iter_m")]
COHEN_CHOICE_FREE = ["YesMetaZFC.SetTheory." + n for n in
                     ("Finite_d", "finite_m", "ZF.erase_m", "Pfn_d", "Fn_d", "Agree_d", "pfn_m", "fn_m", "agree_m",
                      "Fn_antichain_d", "fn_antichain_m", "Fn_bounded_d", "fn_bounded_m", "fiber_m",
                      "not_ch_sentence_l", "ZFC_not_CH", "Definitional.Project.FirstOrderSemantics.model_l")]
COHEN_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                      ("Cmp_d", "cmp_m", "Antichain_d", "Ccc_d", "Value_d", "value_m", "Collision_d", "collision_m",
                       "Split_d", "split_m", "Diagonal_d", "diagonal_m")]
ITERATION_CHOICE_FREE = [PREFIX + "Internal." + n for n in
                         ("rel_at_m", "Preord_d", "preord_m", "rel_env_l", "ord_env_l", "Rel_force_d",
                          "rel_force_m", "Step_cond_d", "Step_le_d", "step_le_m", "Two_step_d", "First_generic_d")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                          ("Stage_dense_d", "stage_dense_m", "stage_env_l", "Step_hits_d", "step_hits_m", "Second_generic_d")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in ("Compose_generic_d", "Proj_below_d")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("cond_order_m", "fn_order_m", "Cohen_spec_d", "cohen_m", "cohen_env_l",
                          "top_m", "top_env_l", "Reg_embed_d", "Max_antichain_d")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Nmap_step_d", "Nmap_graph_d", "Nmap_d", "nmap_step_m", "nmap_graph_m", "nmap_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Red_d", "red_m", "Eq_push_d", "eq_push_m", "Eq_pull_d", "eq_pull_m", "Pull_generic_d")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Curry_step_d", "Curry_graph_d", "Curry_d", "curry_step_m", "curry_graph_m", "curry_m", "Curry_val_d")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in ("npair_env_l", "step_cond_m", "two_step_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("iter_eq_body_m", "iter_eq_env_l", "Iter_eq_d", "iter_eq_m", "Curry_eq_d", "curry_eq_m", "curry_children_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Curry_pull_d", "curry_pull_m", "Curry_pull_wit_d", "curry_pull_wit_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Entry_path_d", "entry_path_m", "Flat_step_d", "Flat_graph_d", "Flat_d",
                          "flat_step_m", "flat_graph_m", "flat_m", "round_body_m", "round_env_l", "Round_force_d",
                          "round_force_m", "Flat_round_d", "flat_round_m", "flat_round_children_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Row_d", "Coord_d", "Row_append_d", "row_m", "coord_m", "row_append_m",
                          "Supp_size_d", "Row_supp_d", "supp_size_m", "row_supp_m", "Row_code_d", "row_code_m",
                          "Row_stage_d", "row_stage_m", "row_empty_l", "row_append_entry_l", "row_append_unique_l",
                          "row_append_prefix_l", "row_append_row_l", "row_ext_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Row_splice_d", "row_splice_m", "Row_link_d", "row_splice_unique_l",
                          "row_splice_entry_l", "row_splice_row_l", "row_splice_prefix_l",
                          "row_splice_absorb_l", "row_append_splice_l", "row_link_id_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Row_tail_reg_d", "row_tail_reg_m", "row_splice_dense_m", "row_splice_overwrite_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Row_system_d", "Row_system_supp_d", "Row_lim_d", "Row_lim_le_d", "row_lim_m",
                          "row_lim_le_m", "row_lim_prefix_l", "row_splice_cut_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("two_step_unique_l", "two_step_pool_unique_l", "Row_repr_d", "Row_next_d", "row_repr_m",
                          "row_next_m", "row_repr_unique_l", "row_next_unique_l", "Row_limit_d", "row_limit_m", "row_limit_unique_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("unique_m", "unique_sat_l", "cohen_spec_unique_l", "cohen_spec_top_unique_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("forces_exists_intro_l", "Cohen_names_d", "cohen_names_m", "cohen_names_sat_l",
                          "Row_cohen_d", "row_cohen_m", "row_cohen_sat_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("row_link_m", "row_link_sat_l", "row_system_m", "row_system_sat_l", "row_system_supp_m",
                          "Row_part_d", "row_part_m", "Row_history_d", "row_history_m", "row_history_sat_l",
                          "row_part_unique_l", "row_history_unique_l", "row_history_entry_l", "row_part_restrict_l",
                          "row_rule_env_l", "Row_extend_d", "Row_rule_d", "Cohen_rule_d", "cohen_rule_m", "cohen_rule_s",
                          "Row_good_d", "row_good_m", "Row_action_d", "row_action_m", "Row_op_d", "row_op_s", "row_op_env_l",
                          "row_op_decode_l", "row_invariant_s", "Row_iteration_d", "row_iteration_s", "row_iteration_denote_l")]
ITERATION_CHOICE_FREE += ["YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics." + n for n in
                         ("native_assignment_l", "native_env_l", "submodel_env_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("antichain_m", "ccc_m", "ccc_exists_m", "Row_disjoint_d", "row_disjoint_m",
                          "Row_cmp_d", "row_cmp_m", "Row_amalgam_d", "row_amalgam_m",
                          "Row_tail_d", "row_tail_m", "Row_tail_bound_d", "row_tail_bound_m",
                          "Row_bounded_ccc_d", "row_bounded_ccc_m", "inj_body_m", "inj_body_closed_l",
                          "fn_env_l", "Inj_name_d", "inj_name_m", "inj_name_closed_l",
                          "Step_index_d", "step_idx_entry_m", "step_graph_entry_m", "step_index_m",
                          "Row_ccc_next_d", "Row_ccc_rule_d", "successor_not_union_l")]
ITERATION_CHOICE_FREE += ["YesMetaZFC.SetTheory." + n for n in
                         ("Cc_closed_d", "cc_closed_m", "Cc_step_d", "cc_step_m",
                          "Cc_union_d", "cc_union_m", "Cc_increasing_d", "cc_increasing_m", "Cc_club_d", "cc_club_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Row_fusion_d", "row_fusion_m", "Dense_set_d", "dense_set_m", "Mstr_d", "mstr_m",
                          "mstr_lower_l", "Proper_d", "proper_m", "proper_exists_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Name_bound_d", "name_bound_m", "Name_pool_d", "name_pool_m", "name_pool_unique_l",
                          "Name_pool_d.left", "Name_pool_d.right", "Name_pool_d.closed", "Name_pool_d.mem_of_entries")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Ng_dense_op_d", "ng_dense_op_m", "Ng_select_at_d", "ng_select_at_m",
                          "Ng_select_op_d", "ng_select_op_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                          ("Hchild_d", "hchild_m", "Pr_base_d", "pr_base_m",
                           "Pr_name_d", "pr_name_body_m", "pr_name_env_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("pr_name_m", "Row_pr_next_d", "Row_pr_wit_d", "row_pr_wit_m", "Row_pr_aux_d", "row_pr_aux_m",
                          "Row_pr_pick_d", "row_pr_pick_m", "Row_pr_family_d", "row_pr_family_m", "Row_pr_rule_d",
                          "row_pr_pick_resolve_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                          ("At_dec_d", "at_dec_m", "Inv_graph_d", "inv_graph_m", "Row_map_d", "row_map_m")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in ("row_dense_s", "row_dense_env_l")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in ("Step_dec_d", "step_dec_m")]
INTERNAL_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                        ("chain_m", "chain_bound_m", "closed_m", "Nchain_d", "nchain_m")]
INTERNAL_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                        ("coll_names_m", "Row_coll_d", "row_coll_m", "Coll_rule_d", "coll_rule_m", "coll_rule_s")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Coll_spec_d", "coll_spec_m", "coll_closed_body_m", "coll_names_body_m", "coll_names_env_l", "Coll_names_d")]
ITERATION_CHOICE_FREE += [PREFIX + "Internal." + n for n in
                         ("Old_fn_d", "old_fn_m", "Row_chain_lower_d", "row_chain_lower_m", "Row_cl_d", "row_cl_m", "Row_cl_stage_d", "row_cl_stage_m",
                          "Row_cl_at_d", "row_cl_at_m", "Row_cl_next_d", "Row_cl_rule_d")]

ITERATION_CHOICE_FREE += ["YesMetaZFC.SetTheory." + n for n in
                         ("Bw_wit_d", "bw_wit_m", "bw_wit_closed_l")]

if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    # 路径调整及后续新增模块都必须进入真实审计切片，避免仅由导入图偶然覆盖。
    listed = {m for group in (MODULES, ZFC_MODULES, INTERNAL_MODULES, CHOICE_MODULES,
                             CH_MODULES, COHEN_MODULES, ITERATION_MODULES)
              for m in group if m.startswith(MODULE_PREFIX)}
    present = {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
               for p in (ROOT / "YesMetaZFC/Model/Forcing").rglob("*.lean")}
    if listed != present:
        raise SystemExit(f"力迫审计模块索引不完整：遗漏 {sorted(present - listed)}；失效 {sorted(listed - present)}")
    result = main(MODULES, CHOICE_FREE, [], "FORCING_GUARD_PASS")
    if result == 0:
        result = main(ZFC_MODULES, [], ZFC_BASELINE, "FORCING_ZFC_GUARD_PASS")
    if result == 0:
        result = main(INTERNAL_MODULES, INTERNAL_CHOICE_FREE, INTERNAL_BASELINE, "FORCING_INTERNAL_GUARD_PASS",
                      {PREFIX + "Internal.row_cut_base_l": [],
                       PREFIX + "Internal.image_ordinal_reflect_l": [],
                       PREFIX + "Internal.image_cofinal_subset_l": [],
                       "YesMetaZFC.SetTheory.Structure.IsRestrictionOf.comp_l": [],
                       PREFIX + "Internal.row_system_restrict_l": []})
    if result == 0:
        result = main(CHOICE_MODULES, ["YesMetaZFC.SetTheory.ZFC." + n for n in
            ("Rem_d", "rem_m", "Enum_step_d", "enum_step_m")], CHOICE_BASELINE, "FORCING_CHOICE_GUARD_PASS")
    if result == 0:
        result = main(CH_MODULES, CH_CHOICE_FREE, CHOICE_BASELINE, "FORCING_CH_GUARD_PASS",
                      {PREFIX + "Internal.image_entry_iff_l": []})
    if result == 0:
        result = main(COHEN_MODULES, COHEN_CHOICE_FREE, CHOICE_BASELINE, "FORCING_COHEN_GUARD_PASS")
    if result == 0:
        result = main(ITERATION_MODULES, ITERATION_CHOICE_FREE, CHOICE_BASELINE, "FORCING_ITERATION_GUARD_PASS",
                      {PREFIX + "Internal." + n: INTERNAL_BASELINE for n in
                       ("countable_forcing_l", "forcing_zf_countermodel_l", "forces_zf_valid_l", "forces_zf_l",
                        "forces_of_generics_l", "npair_forces_l", "nkpair_forces_l", "curry_forces_name_l",
                        "eq_force_order_l", "mem_force_order_l", "forces_order_l", "preord_order_l", "two_step_factors_l",
                        "curry_value_unique_l", "curry_value_l", "curry_value_mem_l", "two_step_valuation_l",
                        "two_step_eq_pick_l", "two_step_common_l", "curry_forces_eq_l", "curry_eq_push_l",
                        "curry_value_congr_l", "two_step_iso_l", "source_of_generics_l", "iter_eq_truth_l",
                        "curry_pull_generic_match_l", "curry_pull_match_l", "curry_forces_eq_pull_l",
                        "curry_forces_eq_iff_l", "curry_eq_pull_l", "curry_value_eq_l", "entry_path_ind_l",
                        "entry_path_set_l", "qval_entry_path_l", "flat_exists_l", "flat_unique_l", "flat_name_l",
                        "round_force_truth_l", "flat_round_force_l", "flat_round_l", "flat_value_l",
                        "row_append_exists_l", "row_append_injective_l", "row_restrict_l", "row_append_supp_l",
                        "row_restrict_supp_l", "order_transport_l", "order_recode_l", "two_step_rows_l",
                        "row_zero_l", "row_successor_l", "row_splice_exists_l", "row_splice_supp_l",
                        "row_link_comp_l", "row_splice_restore_l", "row_system_empty_l", "row_system_extend_l",
                        "row_system_successor_l", "row_lim_order_l", "row_lim_link_l", "row_link_embed_l",
                        "row_limit_l", "row_system_limit_l", "row_system_zero_l", "two_step_l", "two_step_pointed_l",
                        "forces_name_congr_l", "witness_pool_l", "forced_unique_l", "unique_maximum_l",
                        "cohen_names_l", "cohen_names_unique_l", "row_cohen_unique_l",
                        "row_cohen_successor_l", "row_system_cohen_l", "row_part_exists_l", "row_history_exists_l",
                        "cohen_rule_l", "row_action_l", "row_op_total_l", "row_op_extend_l", "row_recursive_good_l",
                        "row_op_class_l", "row_iteration_l", "row_iteration_unique_l", "row_iteration_step_l", "cohen_iteration_l",
                        "row_lim_bounded_l", "row_limit_union_l", "row_amalgam_l", "row_tail_exists_l", "row_tail_delete_l",
                        "inj_name_val_l", "inj_name_no_collision_l", "inj_name_value_l", "step_index_l",
                        "step_index_countable_l", "step_index_forces_countable_l", "reg_surj_ccc_l",
                        "row_fusion_restrict_l", "row_fusion_reconstruct_l", "mstr_generic_l", "proper_mstr_l",
                        "name_pool_exists_l", "name_pool_mix_l", "name_pool_represent_l", "mixing_l",
                        "two_step_represent_l", "two_step_lower_name_l", "row_next_represent_l", "row_next_lower_name_l",
                        "size_chain_bound_l", "smem_subset_l", "smem_successor_l", "smem_function_l",
                        "smem_injection_l", "selem_omega_subset_l", "pr_base_exists_l", "pr_name_value_l",
                        "forces_countable_l", "source_of_generics_theory_l", "at_dec_exists_l", "at_dec_dense_l",
                        "selem_kpair_coords_l", "smem_inv_graph_l", "two_step_inverse_name_l",
                        "two_step_inverse_value_l", "two_step_image_dense_set_l", "ng_rule_env_l",
                        "ng_dense_env_l", "ng_select_env_l", "ng_joint_resolve_l", "ng_joint_slice_l",
                        "pr_name_lower_l", "check_cover_l", "row_dense_force_l", "nmap_identity_l",
                        "row_quot_lower_step_l", "smem_coord_l", "selem_coord_l",
                        "mstr_dense_sequence_l", "rel_force_congr_l", "row_pr_master_l", "selem_predecessor_l",
                        "row_iteration_limit_l", "step_dec_exists_l", "coll_spec_exists_l",
                        "row_chain_project_l", "row_cl_project_l", "row_cl_comp_l")} |
                    {PREFIX + "Internal." + n: [] for n in ("row_splice_glb_l", "row_pil_id_l", "mstr_trace_l", "step_dec_dense_l",
                                                            "coll_spec_sat_l", "coll_spec_unique_l", "coll_spec_top_l", "coll_spec_top_unique_l",
                                                            "row_cl_id_l", "row_chain_lower_sat_l", "row_cl_sat_l", "row_cl_stage_sat_l", "row_cl_at_sat_l")})
    sys.exit(result)
