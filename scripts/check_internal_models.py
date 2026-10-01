"""审计内部模型、公式编译、司寇伦闭包、内部初等性及 Lévy 有限公式反射。

ZF 基础逐声明限制在原七条证书；司寇伦选择与闭包装配另允许原选择公理证书。
编码和解码数据排除经典选择，司寇伦模块的 ZF 端点另逐项收紧。
复用实际声明审计，不生成常驻测试模块。
"""
import sys

from check_filters import BASELINE, main

MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
           ("Numeral", "Structure", "Assignment", "Syntax", "TruthSyntax", "Truth",
            "TruthRules", "FormulaCode", "Satisfaction", "Theory", "Prefix", "Source",
            "Builder", "CompileSemantics", "Compiler", "Countable", "FiniteAssignment", "SkolemSyntax",
            "SupportSyntax", "SupportBound", "Support", "Induction", "TarskiVaughtSyntax",
            "FullWitness", "ElementarySyntax", "TarskiVaught", "Elementary", "SourceElementary", "Membership", "MembershipSkolem", "Hereditary")]
MODULES += ["YesMetaZFC.Model.SetTheory.LevyReflection." + name for name in
            ("Parameters", "WitnessSyntax", "Collection", "Step", "Chain", "Closure", "Relativization", "Decode")]
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

if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    result = main(MODULES, CHOICE_FREE, BASELINE, "INTERNAL_MODEL_GUARD_PASS")
    if not result:
        result = main(SKOLEM_MODULES, [], ZFC_BASELINE, "INTERNAL_SKOLEM_GUARD_PASS", ZF_BOUNDS)
    sys.exit(result)
