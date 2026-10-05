"""审计内部模型、公式编译、司寇伦闭包、有限反射及 OD/HOD。

ZF 基础逐声明限制在原七条证书；司寇伦选择与闭包装配另允许原选择公理证书。
编码和解码数据排除经典选择，司寇伦模块的 ZF 端点另逐项收紧。
复用实际声明审计，不生成常驻测试模块。
"""
import sys

from check_filters import BASELINE, main

MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
           ("Numeral", "Structure", "Assignment", "Syntax", "TruthSyntax", "Truth",
            "TruthRules", "FormulaCode", "Satisfaction", "Theory", "Prefix", "Source",
            "Builder", "CompileSemantics", "Compiler", "Countable", "FiniteAssignment", "FiniteSource", "SkolemSyntax",
            "CanonicalRows", "CanonicalCode", "CanonicalSatisfaction",
            "SupportSyntax", "SupportBound", "Support", "Induction", "TarskiVaughtSyntax",
            "FullWitness", "ElementarySyntax", "TarskiVaught", "Elementary", "SourceElementary", "Membership", "MembershipSkolem", "Hereditary")]
MODULES += ["YesMetaZFC.Model.SetTheory.LevyReflection." + name for name in
            ("Parameters", "WitnessSyntax", "Collection", "Step", "Chain", "Closure", "Relativization", "Decode", "Bounded")]
MODULES += ["YesMetaZFC.Model.SetTheory.LevyReflection", "YesMetaZFC.SetTheory.CumulativeUnion"]
MODULES += ["YesMetaZFC.SetTheory.RelationChain"]
MODULES += ["YesMetaZFC.SetTheory.IndexedIteration"]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("FinitaryTraceSyntax", "FinitaryFamily", "Card.FiniteParameters")]
MODULES += ["YesMetaZFC.SetTheory.Card." + name for name in
            ("FiniteSequenceSyntax", "FiniteSequenceRecursion", "FiniteSequenceNumbering",
             "FiniteSequenceCountable", "FiniteSequenceLift", "FiniteSequenceEnd", "OrdinalImage")]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("CountableChain", "FinitaryHullSyntax", "FinitaryHullStep", "FinitaryHull")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal", "YesMetaZFC.Model.SetTheory.Internal.ReducedPower"]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("Rank", "TransitiveClosure", "RankImage", "Hereditary", "Card.SmallBound", "FunctionRetraction", "FinitarySlice")]
MODULES += ["YesMetaZFC.SetTheory.Ord.Code." + name for name in
            ("Transport", "Pair", "Natural", "Fold", "Prefix", "Sequence")]
MODULES += ["YesMetaZFC.SetTheory.Ord.Code", "YesMetaZFC.SetTheory.InnerModel.OD"]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.OD." + name for name in
            ("Syntax", "Source", "Code", "Definition", "Complexity", "Minimum", "Order", "Choice")]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("CumulativeCertificate", "Ord.DefinableMinimum", "Definitional.Project.Hierarchy.Levy",
             "InnerModel.HOD.Definition", "InnerModel.HOD")]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.OD." + name for name in
            ("Graph", "Brackets", "Parameters", "Relative", "RelativeClosure", "Separation", "Relations")]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.HOD." + name for name in
            ("Relative", "Relativization", "Closure", "Schemas", "Models", "Parameters", "Coding", "Presentation")]
MODULES += ["YesMetaZFC.SetTheory.Collapse." + name for name in
            ("RelationSyntax", "RelationRecursion", "RelationExistence", "RelationIso", "RelationBounded", "RelationMap")]
MODULES += ["YesMetaZFC.SetTheory.Collapse"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("ExtenderRelationCode", "ExtenderModelCode")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("EmbeddingSmallRestriction", "EmbeddingCountableBound", "ExtenderCopyRestriction")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in ("EmbeddingOrdinal", "SourceOmegaBound", "SourceHierarchy")]
MODULES += ["YesMetaZFC.SetTheory.CumulativeRelativeAlgebra", "YesMetaZFC.SetTheory.LargeCardinal.ExtenderTreeBranch"]
MODULES += ["YesMetaZFC.SetTheory.Descriptive." + name for name in ("TreeCons", "TreeBounded", "TreeWellFounded")]
MODULES += ["YesMetaZFC.SetTheory.Descriptive"]
MODULES += ["YesMetaZFC.SetTheory.Card.FiniteSequenceJoin"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding",
            "YesMetaZFC.SetTheory.LargeCardinal.Woodin",
            "YesMetaZFC.SetTheory.Descriptive.Game", "YesMetaZFC.SetTheory.Descriptive.Determinacy"]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.Relative." + name for name in
            ("Operator", "Hierarchy", "Class", "Structure", "Relativization", "Reflection",
             "Schemas", "Model", "Reals", "LReal", "Determinacy")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("EmbeddingSource", "PredicateSource", "Isomorphism", "Collapse", "SeparationCode", "Separation",
             "BinaryTruth", "CollectionCode", "DeltaCode", "UniformizationCode", "FunctionCode",
             "PointwiseAssignment", "PointwiseSyntax", "PointwiseSteps", "PointwiseValue", "PointwiseTruth",
             "SeparationSource", "SourceField")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in
            ("Relation", "Classes", "Model", "Truth", "Update", "Assignment", "Atomic", "LosSyntax",
             "SourceSyntax", "SourceTruth", "SourceAssignment", "SourceProjection", "PullbackKernel", "ProjectionLaws")]
MODULES += ["YesMetaZFC.SetTheory.CumulativeClosure", "YesMetaZFC.SetTheory.InnerModel.Recursion.Graph",
            "YesMetaZFC.SetTheory.InnerModel.Recursion.Composition"]
MODULES += ["YesMetaZFC.SetTheory.Filter." + name for name in ("Relative", "Source", "Projection")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("DerivedFilter", "SourceMeasure", "CriticalMeasure", "CriticalOrdinal", "MeasureCompleteness", "Measurable",
             "TreeReflection", "MeasureFamily", "FiberCompleteness", "FiniteSupport", "SupportCompleteness",
             "SupportProjection", "Coherence", "SupportConstruction")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.Quotient",
            "YesMetaZFC.Model.SetTheory.Internal.DirectedSystem"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem." + name for name in
            ("Basic", "Limit", "WellFounded", "Cone", "Union", "Stages", "ElementarySyntax", "Elementary", "Factor")]
MODULES += ["YesMetaZFC.SetTheory.Collapse.RelationSequence", "YesMetaZFC.SetTheory.Filter.Countable",
            "YesMetaZFC.SetTheory.LargeCardinal.ComponentWellFounded",
            "YesMetaZFC.SetTheory.LargeCardinal.WellFoundedComponents"]
MODULES += ["YesMetaZFC.SetTheory.CountableChoice", "YesMetaZFC.SetTheory.Filter.Finite",
            "YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullProjection"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("CountableSupport", "SupportIndex", "MeasureConstraints", "ConstraintLevels", "JointFiber", "ExtenderFunctions")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.AscendingDescent"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem." + name for name in ("FiniteCover", "ElementaryFactor")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("EmbeddingFinite", "PointwiseContext", "SeparationTransport", "SourceTransport")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in ("CopyKernel", "CopyConstant")]
MODULES += ["YesMetaZFC.SetTheory.Filter.SourceUltrafilter"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderRelative", "ExtenderTransport", "ExtenderCopyPull", "ExtenderCopySyntax")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in ("Bounded", "DeltaImage")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderFunctionCode", "ExtenderNormalSource", "ExtenderRepresentative", "ExtenderCoordinateSource",
             "ExtenderSeed", "ExtenderSeedNormal", "ExtenderSeedCollapse", "ExtenderCopySeed", "ExtenderCopyCollapse",
             "ExtenderTuple", "ExtenderSetCode")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("IterationOrder", "IterationDiagram", "IterationNextMaps", "IterationDiagramExtend", "IterationStep",
             "IterationTree", "IterationTreeExtend", "IterationRoot", "IterationLimit", "Iteration")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Isomorphism"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("IterationBranch", "IterationTag", "IterationTagIso", "IterationSystem", "IterationDirectLimit",
             "IterationProjection", "IterationLimitModel", "IterationLimitOrder", "IterationLimitMaps",
             "IterationLimitDiagram", "IterationLimitExtend", "IterationWellFounded", "IterationCofinal",
             "IterationRealizer", "IterationBranchExtend", "IterationPadding")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderSystemSyntax", "ExtenderEdge", "ExtenderDescentSyntax", "ExtenderWellFounded")]
MODULES += ["YesMetaZFC.SetTheory.OrdinalChoice"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("EmbeddingComposition", "Extensionality", "RelationCollapse")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("UniversalSyntax", "UniversalClosure", "EmbeddingOmega", "SourceFinite", "SourceSequences",
             "UniformizationSource", "PointwiseQuantifier", "Pointwise", "PointwiseTrace",
             "PointwiseDiagonal", "PointwiseWitness", "SourceReindex")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in
            ("SourceLos", "SourceSatisfaction", "Constant", "SourceComposition", "SourceTrace", "Restriction")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderComponents", "ExtenderEvaluation", "ExtenderEvaluationPull", "ExtenderFactor",
             "ExtenderRepresent", "RankLookup")]
MODULES += ["YesMetaZFC.SetTheory.Card.PowerBound", "YesMetaZFC.SetTheory.LargeCardinal.ExtenderTag",
            "YesMetaZFC.SetTheory.LargeCardinal.DerivedEvaluation"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("DerivedSeparation", "ExtenderNormalSyntax", "ExtenderNormal", "ExtenderOperator", "ExtenderAlgebra",
             "ExtenderSeeds", "ExtenderRestriction", "ExtenderPrefix", "ExtenderBoundedSyntax", "ExtenderBounded",
             "ExtenderShort", "ExtenderSyntax", "WoodinExtender", "ExtenderTruncation", "ExtenderProduct", "Extender")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.EmbeddingRange",
            "YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.RelationChange"]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("Kuratowski", "Card.SmallEnumeration", "Collapse.EmbeddingFixed", "CumulativeRelative")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderComparison", "ExtenderCoordinates", "ExtenderLength", "DerivedPredicate",
             "RankTransport", "RankEnumerationSyntax", "RankLookupSyntax")]

CHOICE_FREE = ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Num_d", "num_m", "num_unique_l", "Smdl_d", "smdl_m", "smdl_structure_l",
                "smdl_unique_l", "Senv_update_d", "senv_update_m", "senv_update_unique_l",
                "Sop_d", "sop_m", "Sfm_node_d", "sfm_node_m", "Sfm_d", "sfm_m",
                "Sarg_d", "sarg_m", "Snode_d", "snode_m", "Seval_at_d", "seval_at_m",
                "Seval_step_d", "seval_step_m", "seval_s", "seval_env_l", "Seval_d", "seval_m",
                "seval_step_unique_l", "Ssat_d", "ssat_m", "Sformula_d", "sformula_m",
                "sformula_unique_l", "Scode_d", "scode_m", "scode_unique_l",
                "Satisfies_d", "satisfies_m", "satisfies_decode_l", "Smodels_d", "smodels_m",
                "source_core_l", "Sbuild_d", "Scompile_d", "Senv_fill_d", "senv_fill_m",
                "senv_fill_unique_l", "Ssk_wit_d", "ssk_wit_m", "Ssk_choice_d", "ssk_choice_m",
                "Ssk_d", "ssk_m", "Ssk_closed_d", "ssk_closed_m", "Scoord_d", "scoord_m",
                "Sbound_d", "sbound_m", "Senv_agree_d", "senv_agree_m", "Stv_d", "stv_m",
                "Ssub_d", "ssub_m", "Selem_d", "selem_m", "selem_refl_l", "Selem_d.trans_l",
                "Smem_d", "smem_m", "smem_unique_l", "Ssk_mem_d", "ssk_mem_m", "ssk_mem_s", "Hsub_d", "hsub_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("lr_env_l", "lr_shift_l", "lr_all_m", "lr_and_m", "Lr_bound_d", "Lr_fiber_d",
                 "lr_fiber_m", "lr_bound_m", "Lr_family", "Lr_step_d", "lr_step_m", "lr_cover_s",
                 "Lr_next_d", "lr_next_m", "lr_iter_s", "lr_queries_l", "lr_rel_m", "Lr_reflect_d", "Lr_formula")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Fseq_space_d", "fseq_space_m", "Fseq_pair_d", "fseq_pair_m", "Fseq_snoc_d",
                 "fseq_snoc_m", "Fseq_at_d", "fseq_at_m", "Fseq_step_d", "fseq_step_m",
                 "fseq_env_l", "fseq_step_s", "Ord_image_d", "ord_image_m", "Fc_value_d", "fc_value_m",
                 "Fc_closed_d", "fc_closed_m", "Fc_step_d", "fc_step_m", "Fc_hull_d", "fc_hull_m",
                 "Fseq_end_d", "fseq_end_m", "fseq_end_unique_l", "fseq_end_rebuild_l", "Fc_slice_d", "fc_slice_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Fc_seed_d", "fc_seed_m", "Fc_trace_d", "fc_trace_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sc_node_d", "sc_node_m", "Sc_rows_d", "sc_rows_m", "Sc_num_d", "sc_num_m", "Sc_sat_d", "sc_sat_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Oc_at_d", "oc_at_m", "Oc_pair_d", "oc_pair_m", "Oc_fold_d", "oc_fold_m", "Oc_seq_d", "oc_seq_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("Od_local_d", "od_local_m", "Od_code_d", "od_code_m", "Od_in_d", "od_in_m",
                 "Od_ext_d", "od_decoder_s", "Od_eval_d", "od_eval_m", "od_eval_s", "od_s", "Od_d", "od_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("Od_rank_d", "od_rank_m", "od_sigma_m", "Od_min_d", "od_min_m", "Od_pick_d", "od_pick_m",
                 "Od_choices_d", "od_choices_m", "Od_lt_d", "od_lt_m", "Hod_d", "hod_m", "hod_sigma_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("lr_truth_s", "Lr_truth_d", "lr_truth_m", "Vc_step_d", "vc_step_m", "Vc_d", "vc_matrix_m", "v_sigma_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("od_unique_s", "Od_graph_d", "od_graph_m", "od_graph_s", "ob_s", "Ob_d", "ob_m",
                 "Ob_eval_d", "ob_eval_m", "Ob_ext_d", "od_ex_m", "ob_subst_s", "Oa_seq_d", "oa_seq_m",
                 "Oa_param_d", "oa_param_m", "Oa_d", "oa_m", "Op_d", "Ha_d", "Hb_d", "Hp_d",
                 "ha_m", "ha_cut_s", "ha_rel_m", "oa_sep_s", "Hb_pick_d", "hb_pick_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Fs_tail_d", "YesMetaZFC.SetTheory.fs_tail_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Spred_d", "spred_m", "Smap_assign_d", "smap_assign_m", "Smap_d", "smap_m",
                 "Spred_emb_d", "spred_emb_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive." + name for name in
                ("Gm_even_d", "gm_even_m", "Gm_follows_d", "gm_follows_m", "Gm_win_d", "gm_win_m",
                 "Det_d", "det_m", "AD_d", "ad_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Wd_crit_d", "wd_crit_m", "Wd_witness_d", "wd_witness_m", "Wd_strong_d", "wd_strong_m",
                 "Woodin_d", "woodin_m", "Wd_proper_d", "wd_proper_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.spred_core_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Smap_assign_d.update_l", "Smap_row_d", "smap_row_m", "Smap_d.ssat_l", "Senv_update_d.agree_l", "Ssep_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in ("Sbin_d", "sbin_m", "Scollect_d", "sbin_update_l", "sbin_value_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Suniform_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sfun_d", "sfun_m", "Sfun_d.function_l", "Pe_assign_d", "pe_assign_m", "pe_atom_m",
                 "Pe_row_d", "pe_row_m", "Pe_state_d", "pe_state_m", "Pe_repr_d", "pe_repr_m",
                 "Pe_sat_d", "pe_sat_m", "Pe_holds_d", "pe_holds_m", "Rs_eval_d", "rs_eval_m", "Rs_los_d", "rs_los_m",
                 "Pe_repr_d.update_l", "Pe_assign_d.value_l", "Pe_assign_d.agree_right_l", "Rs_eval_d.repr_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF.Rel_ultra_d.nor_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF." + name for name in
                ("Pull_d", "pull_m", "Push_d", "push_m", "Pull_d.comp_l", "Push_d.comp_l", "Push_d.member_l", "push_id_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Rs_const_d", "rs_const_m", "rs_const_unique_l", "Rp_lift_d",
                 "rs_projection_id_l", "rs_projection_comp_l", "rs_projection_constant_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("Fn0_d.retarget_l", "Cp0_d.value_l", "Cp0_d.assoc_l", "Cp0_d.retarget_l",
                 "cp0_projection_id_l", "cp0_projection_comp_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Rp_eq_d", "rp_eq_m", "Rp_eq_d.symm_l", "Rp_rel_d", "rp_rel_m", "rp_rel_congr_l",
                "Rp_class_d", "rp_class_m", "Rp_map_d", "rp_map_m", "rp_kernel_l", "Rp_model_d", "rp_model_m",
                "Rp_holds_d", "rp_holds_m", "Rp_trace_d", "rp_trace_m", "Rp_update_d", "rp_update_m", "Rp_ex_d", "rp_ex_m",
                "Rp_column_d", "rp_column_m", "Rp_eval_d", "rp_eval_m", "Rp_los_d", "rp_los_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ed_trace_d", "ed_trace_m", "Ed_filter_d", "ed_filter_m", "Ed_nonprincipal_d", "ed_nonprincipal_m",
                 "Ed_all_d", "ed_all_m", "Ed_complete_d", "ed_complete_m", "Measurable_d", "measurable_m",
                 "Eb_d", "eb_m", "Ef_family_d", "ef_family_m", "Ef_levels_d", "ef_levels_m",
                 "Ef_fiber_d", "ef_fiber_m", "Ef_image_fiber_d", "ef_image_fiber_m",
                 "Es_value_d", "es_value_m", "Es_family_d", "es_family_m", "Es_fiber_d", "es_fiber_m",
                 "Es_pull_d", "es_pull_m", "Es_reindex_d", "es_reindex_m", "Es_coherent_d", "es_coherent_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF." + name for name in
                ("Base_d", "base_m", "Field_d", "field_m", "Rel_ultra_d", "rel_ultra_m", "Source_d", "source_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel.Fn0_d." + name for name in ("domain_eq_l", "mono_target_l", "ext_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in ("Cp0_d", "cp0_m", "cp0_unique_l", "cp0_mono_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Wf_rel_d", "wf_rel_m", "Wc_step_d", "wc_step_m", "Wc_graph_d", "wc_graph_m",
                 "Wc_value_d", "wc_value_m", "wf_rel_sat_l", "wc_step_sat_l", "wc_graph_sat_l",
                 "wc_value_sat_l", "wc_union_entry_l")]

CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Qt_equiv_d", "Qt_class_d", "qt_class_m", "Qt_map_d", "Di_order_d", "Di_system_d",
                 "Di_eq_d", "di_eq_m", "Di_rel_d", "di_rel_m", "Di_limit_d", "Di_sigma_d", "Di_wf_d",
                 "Di_system_d.eq_refl_l", "Di_eq_d.symm_l", "Di_system_d.eq_trans_l", "Di_system_d.eq_at_l",
                 "Di_system_d.rel_at_l", "Di_system_d.rel_congr_l", "Di_limit_d.commute_l", "di_sigma_of_top_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Wf_desc_d", "YesMetaZFC.SetTheory.FilterZF.Cc_d",
                "YesMetaZFC.SetTheory.FilterZF.cc_m", "YesMetaZFC.SetTheory.LargeCardinal.Ew_down_d",
                "YesMetaZFC.SetTheory.LargeCardinal.ew_down_m", "YesMetaZFC.SetTheory.LargeCardinal.ed_countable_l",
                "YesMetaZFC.SetTheory.LargeCardinal.ew_down_value_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ec_value_d", "ec_value_m", "Ei_d", "ei_m", "Ei_map_d", "ei_map_m", "Em_family_d",
                 "Ec_ok_d", "ec_ok_m", "Ec_all_d", "ec_all_m", "Ec_level_d", "ec_level_m", "Ec_eval_d", "ec_eval_m",
                 "Ep_space_d", "ep_space_m", "Ep_fun_d", "ep_fun_m", "Ep_pull_d", "ep_pull_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF.Mt_d", "YesMetaZFC.SetTheory.FilterZF.mt_m",
                "YesMetaZFC.SetTheory.Internal.Rp_atom_d", "YesMetaZFC.SetTheory.Internal.rp_atom_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Di_step_d", "YesMetaZFC.SetTheory.Internal.di_step_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ep_at_d", "ep_at_m", "Ep_rel_d", "ep_rel_m", "Ep_graph_d", "Ep_lift_d", "Ep_system_d",
                 "Ee_constraint_d", "ee_constraint_m", "Ee_hit_d", "ee_hit_m", "Ee_rep_d", "ee_rep_m",
                 "Ee_row_d", "ee_row_m", "Ee_test_d", "ee_test_m")]

CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("En_graph_d", "en_graph_m", "En_normal_d", "en_normal_m", "Ex_value_d", "ex_value_m",
                 "Ex_operator_d", "Ex_derived_d", "Ea_test_d", "ea_test_m", "Ea_part_d", "Ea_atoms_d",
                 "ea_part_m", "ea_atoms_m", "Ex_bp_at_d", "ex_bp_at_m", "Ex_bp_d", "Ex_pre_d", "Ex_short_d",
                 "em_family_m", "ex_complete_m", "ex_principal_m", "ex_nonprincipal_m", "ex_countable_m",
                 "ex_pre_m", "ex_short_m", "Ex_product_d", "ex_product_at_m", "Ex_value_d.mono_l",
                 "Ex_operator_d.at_l", "Ex_operator_d.total_l", "ex_inter_l", "ea_test_read_l",
                 "ex_value_at_l", "ex_value_type_l", "ex_append_unique_l", "ex_prefix_cp_l")]

SKOLEM_MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in ("Skolem", "ElementaryHull", "ElementaryClub")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.FinitaryClub"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.FinitaryTrace", "YesMetaZFC.Model.SetTheory.Internal.ElementaryTrace"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.ClassChoice"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory." + name for name in
                   ("Card.Properties.SuccessorRegularity", "Card.SmallUnion", "HereditaryClosure", "HereditaryAlgebra",
                    "HereditaryCover", "IndexedChoice", "CountableDirected")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.InnerModel.Condensation.Internal"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.SeparationHull"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
                   ("Collection", "Uniformization", "UniformizationHull", "SourceTheory", "SourceCollapse", "SourceBranch")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.HereditaryCollapse"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.InaccessibleEnumeration", "YesMetaZFC.SetTheory.LargeCardinal.EmbeddingRankRestriction"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.RelativeRankSegment"]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Rk_d", "rk_m", "Tc_d", "tc_m", "Hmem_d", "hmem_m", "H_d", "h_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Wc_ext_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in ("Wc_iso_d", "wc_iso_m", "wc_ext_m", "Wc_map_d", "wc_map_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in ("Sc_wf_d", "Sc_collapse_d", "sc_collapse_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sc_branch_d", "sc_branch_m", "wf_chain_m", "Sc_hierarchy_d", "sc_hierarchy_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive.Tb_step_d", "YesMetaZFC.SetTheory.Descriptive.tb_step_m",
                "YesMetaZFC.SetTheory.LargeCardinal.Er_level_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.ep_binary_pair_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Sc_omega_bound_d", "YesMetaZFC.SetTheory.Internal.sc_omega_bound_m",
                "YesMetaZFC.SetTheory.LargeCardinal.ec_count_value_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Di_stage_d", "di_stage_m", "Di_elementary_d", "Di_row_d", "di_row_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Ee_value_d", "YesMetaZFC.SetTheory.LargeCardinal.ee_value_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Vr_d", "YesMetaZFC.SetTheory.KPair_d.mem_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ep_comparison_d", "Ep_length_d", "Su0_d", "su0_m", "Er_enum_d", "er_enum_m",
                 "Er_stage_d", "er_stage_m", "Er_hit_d", "er_hit_m", "Er_hit_d.bound_l")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory." + name for name in
                   ("InaccessibleHierarchy", "HereditaryFunction", "HereditarySequences")]
ZFC_BASELINE = BASELINE + ["YesMetaZFC.SetTheory.Axioms.choice._native.native_decide.ax_1"]
# 全背景见证选择及商赋值代表选择允许对象 AC；给定源理论后的源内部 Łoś 按 ZF 审计。
LOS_MODULES = ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in
               ("Witness", "Los", "Lift", "Projection")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.SourceProjection"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderSource", "ExtenderArrows", "ExtenderLaws",
                "ExtenderGraphs", "ExtenderSystem", "ExtenderLimit", "ExtenderElementary", "ExtenderConstant",
                "ExtenderCollapse", "ExtenderRankSource", "ExtenderDerivedLimit")]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullElementary"]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullEmbedding"]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Copy"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderUltrapower", "ExtenderCopyComponent", "ExtenderCopy", "ExtenderCopyApplication")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderValue", "ExtenderTupleValue", "ExtenderValueAgreement", "ExtenderValueBound",
                "ExtenderSetTransfer", "ExtenderSuccessor", "ExtenderSuccessorApplication", "ExtenderCopySuccessor", "ExtenderSupportBound")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("IterationApply", "IterationAgreement", "IterationFork")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("RankEnumeration", "RankCover", "RankLength",
                "ExtenderPredicateComponent", "ExtenderPredicateLimit", "ExtenderStrength", "WoodinStrength")]
LOS_CHOICE_FREE = ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                   ("Ep_source_d", "Ep_component_d", "ep_component_m", "Ep_arrow_d", "ep_arrow_m", "Ep_limit_d",
                    "Ep_collapse_d", "Ee_node_d", "ee_node_m", "ee_node_pair_l", "Ee_factor_d", "Ep_derived_limit_d")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                   ("Ep_constants_d", "Ep_strength_d", "Ep_strong_limit_d")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.rp_change_filter_l", "YesMetaZFC.SetTheory.Internal.rp_lift_unique_l"]
LOS_ZF_BOUNDS = {"YesMetaZFC.SetTheory.Internal.rp_lift_exists_l": BASELINE}
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Ep_source_d.space_l", "Ep_source_d.space_mem_l", "Ep_source_d.function_l",
                      "Ep_source_d.projection_l", "Ep_source_d.family_l", "Ep_source_d.model_l", "Ep_source_d.successor_l",
                      "es_source_push_l", "Ep_limit_d.factor_l", "ep_representatives_l", "ep_relation_l", "ep_arrow_id_l")})
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_support_cover_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_value_support_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.Internal.rp_matrix_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_copy_identity_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.Ep_source_d.rebase_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.it_apply_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.er_stage_l"] = BASELINE
ZF_BOUNDS = {"YesMetaZFC.SetTheory.Internal.Ssk_d." + name: BASELINE for name in
             ("value_l", "closed_l", "point_mem_l")}
ZF_BOUNDS["YesMetaZFC.SetTheory.InnerModel.jc_internal_l"] = BASELINE
ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                  ("sc_separation_forward_l", "sc_uniform_forward_l", "Sc_theory_d.map_l",
                   "sc_wf_relative_l", "sc_collapse_sat_l", "Sc_collapse_d.map_l", "Sc_collapse_d.collapse_l",
                   "Sc_collapse_d.wf_absolute_l", "sc_branch_sat_l", "Sc_branch_d.map_l", "sc_branch_absolute_l")})
ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal.Er_level_d." + name: BASELINE for name in
                 ("map_l", "restriction_l")})
ZF_BOUNDS["YesMetaZFC.SetTheory.ZF.h_collapse_image_l"] = BASELINE
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Senv_tail_d", "senv_tail_m", "Sall_d", "sall_m", "Sc_theory_d", "Sc_sequences_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Pe_context_d", "YesMetaZFC.SetTheory.Internal.pe_context_m",
                "YesMetaZFC.SetTheory.FilterZF.Sf_ultra_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Em_source_d", "Ec_source_d", "Ea_agree_d", "Ea_maps_d", "Ec_class_d", "ec_class_m",
                 "Ec_node_d", "ec_node_m", "Ec_limit_d")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Ec_ultrapowers_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("En_source_d", "Ep_repr_d", "ep_repr_m", "Ep_coord_d", "ep_coord_m", "Ep_seed_d", "ep_seed_m", "ep_pair_at_m")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                    ("Ep_value_d", "ep_value_m", "ep_subspace_m", "Ep_successor_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("It_pred_d", "It_order_d", "It_map_d", "it_map_m", "It_comp_d", "it_comp_m", "It_diagram_d",
                 "It_next_d", "it_next_m", "It_source_d", "It_local_d", "It_ultra_d", "It_payload_d", "It_active_d",
                 "It_step_d", "It_limit_d", "It_tree_d", "It_extension_d", "It_image_d", "it_image_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("It_branch_d", "It_tag_d", "It_arrow_d", "it_arrow_m", "It_system_d",
                 "It_project_d", "it_project_m", "It_cone_d", "It_finish_d", "it_finish_m",
                 "It_wf_branch_d", "It_realizer_d", "It_value_d", "it_value_m", "It_limit_extension_d")]
# HOD 的 AC 定理仅需原选择句子的自由闭合性证书，不假设背景 AC。
HOD_CHOICE_MODULES = ["YesMetaZFC.SetTheory.InnerModel.HOD." + name for name in ("Choice", "BracketChoice")]
HOD_ZF_BOUNDS = {"YesMetaZFC.SetTheory.InnerModel." + name: BASELINE for name in
                 ("hod_choice_set_l", "hod_model_l", "hod_model_ext_l")}
HOD_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.InnerModel." + name: BASELINE for name in
                      ("hb_pick_exists_l", "hb_pick_unique_l", "hb_choice_set_l")})

if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    result = main(MODULES, CHOICE_FREE, BASELINE, "INTERNAL_MODEL_GUARD_PASS")
    if not result:
        result = main(HOD_CHOICE_MODULES, [], ZFC_BASELINE, "HOD_CHOICE_GUARD_PASS", HOD_ZF_BOUNDS)
    if not result:
        result = main(SKOLEM_MODULES, [], ZFC_BASELINE, "INTERNAL_SKOLEM_GUARD_PASS", ZF_BOUNDS)
    if not result:
        result = main(LOS_MODULES, LOS_CHOICE_FREE, ZFC_BASELINE, "INTERNAL_LOS_GUARD_PASS", LOS_ZF_BOUNDS)
    sys.exit(result)
