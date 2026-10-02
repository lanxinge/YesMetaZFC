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
MODULES += ["YesMetaZFC.Model.SetTheory.Internal"]
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
            ("RelationSyntax", "RelationRecursion", "RelationExistence")]
MODULES += ["YesMetaZFC.SetTheory.Card.FiniteSequenceJoin"]

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
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Wf_rel_d", "wf_rel_m", "Wc_step_d", "wc_step_m", "Wc_graph_d", "wc_graph_m",
                 "Wc_value_d", "wc_value_m", "wf_rel_sat_l", "wc_step_sat_l", "wc_graph_sat_l",
                 "wc_value_sat_l", "wc_union_entry_l")]

SKOLEM_MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in ("Skolem", "ElementaryHull", "ElementaryClub")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.FinitaryClub"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.FinitaryTrace", "YesMetaZFC.Model.SetTheory.Internal.ElementaryTrace"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.ClassChoice"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory." + name for name in
                   ("Card.Properties.SuccessorRegularity", "Card.SmallUnion", "HereditaryClosure",
                    "HereditaryCover", "IndexedChoice", "CountableDirected")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Rk_d", "rk_m", "Tc_d", "tc_m", "Hmem_d", "hmem_m", "H_d", "h_m")]
ZFC_BASELINE = BASELINE + ["YesMetaZFC.SetTheory.Axioms.choice._native.native_decide.ax_1"]
ZF_BOUNDS = {"YesMetaZFC.SetTheory.Internal.Ssk_d." + name: BASELINE for name in
             ("value_l", "closed_l", "point_mem_l")}
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
    sys.exit(result)
