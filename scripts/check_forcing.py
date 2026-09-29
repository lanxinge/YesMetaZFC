"""审计力迫偏序、布尔完备化、名称解释与相对扩张，不引入测试用 Lean 模块。

稠密性证书在 Prop 内使用经典逻辑；规范映射函数和布尔运算分别严格审计。
"""
import sys

from check_filters import main

MODULES = ["YesMetaZFC.Model.Forcing." + n for n in
           ("Order", "Density", "Separative", "Boolean", "Tree",
            "RegularOpen", "Completion", "Cohen", "Generic", "Valuation",
            "BooleanGeneric", "Truth", "NameGeneric", "Extension", "RealName", "CohenReal",
            "Domain", "Formula", "FormulaGeneric", "FormulaEnumeration",
            "InternalPair", "InternalNames", "InternalGraph", "InternalRealization",
            "InternalBoolean", "InternalCohen", "InternalCheckSyntax", "InternalCheck",
            "InternalGround", "InternalCheckVal", "InternalCheckRealization",
            "InternalAtomicSyntax", "InternalFormula", "InternalGenericInstance", "InternalGeneric")]
MODULES += ["YesMetaZFC.Model.SetTheory.CountableSyntax"]
# 原公理公式已有的自由闭合证书，只允许出现在直接消费原公理的切片中。
ZFC_MODULES = ["YesMetaZFC.Model.Forcing." + n for n in ("ZFCBase", "CohenTheory")]
ZFC_BASELINE = [f"YesMetaZFC.SetTheory.Axioms.{n}._native.native_decide.ax_1"
                for n in ("extensionality", "emptySet", "foundation", "infinity")]
# 从完整原 ZF 模型抽取内部名称所需的窄模式片段，单独固定原七条公理的既有依赖。
INTERNAL_MODULES = ["YesMetaZFC.Model.Forcing.InternalClosure",
                    "YesMetaZFC.Model.Forcing.InternalCheckModel",
                    "YesMetaZFC.SetTheory.MembershipInduction",
                    "YesMetaZFC.SetTheory.Ord.Recursion",
                    "YesMetaZFC.SetTheory.Card.Aleph.Hartogs"]
INTERNAL_MODULES += ["YesMetaZFC.Model.Forcing." + n for n in (
    "InternalAtomicClosure", "InternalAtomic", "InternalConditions", "InternalDefinability",
    "InternalAtomicWitness", "InternalEquivalence", "InternalQuotient", "InternalFoundation", "InternalCheckForcing",
    "InternalAtomicTruth", "InternalLogic", "InternalTruth", "InternalNameConstruction",
    "InternalSeparation", "InternalCollection", "InternalPower", "InternalZFOperations", "InternalZF",
    "InternalSelection")]
INTERNAL_BASELINE = [f"YesMetaZFC.SetTheory.Axioms.{n}._native.native_decide.ax_1"
                     for n in ("emptySet", "extensionality", "foundation", "infinity",
                               "pairing", "powerSet", "union")]
CHOICE_MODULES = ["YesMetaZFC.SetTheory.Choice", "YesMetaZFC.Model.Forcing.InternalChoice"]
CHOICE_BASELINE = INTERNAL_BASELINE + ["YesMetaZFC.SetTheory.Axioms.choice._native.native_decide.ax_1"]
CH_MODULES = ["YesMetaZFC.Model.Forcing." + n for n in
              ("InternalClosed", "Collapse", "NoNewReals", "GroundTransfer", "CollapseGeneric", "CH")]
CH_MODULES += ["YesMetaZFC.SetTheory." + n for n in
               ("DependentChoice", "Card.Omega", "Card.CountableUnion", "Continuum")]
CH_MODULES += ["YesMetaZFC.Model.SetTheory.Countable"]
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
    "Entry_d", "Supp_d", "Name_d", "supp_m", "name_m", "name_entry_l", "name_empty_l",
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
INTERNAL_CHOICE_FREE = [PREFIX + "Internal." + n for n in (
    "Entry_supp_d", "entry_supp_m", "Name_ops_d", "set_insert_l", "name_adjoin_l", "name_subset_l",
    "name_pair_l", "name_unfold_l", "name_support_l", "Triple_carrier_d", "Max_bisim_d",
    "Eq_match_d", "Mem_force_d", "mem_force_m", "Cond_order_d", "Dense_d", "Neg_d", "Lower_d", "Generic_d",
    "Defined_d", "pred_m", "neg_pred_m", "Wit_d", "Bad_d", "wit_m", "bad_m", "Regular_d", "Eval_d",
    "force_at_m", "force_at_closed_l", "Source_d", "source_m", "Sub_name_d", "sub_name_m",
    "witness_m", "witness_closed_l",
    "Poss_mem_d", "Min_mem_d", "poss_mem_m", "min_mem_m",
    "Name_eq_d", "Name_quot_l", "Qval_d", "qmem_l", "name_quot_membership_l",
    "qval_unique_l", "qval_name_l", "name_value_l", "value_name_l", "Min_name_d", "min_name_m",
)]
INTERNAL_CHOICE_FREE += ["YesMetaZFC.SetTheory.Mem_ind_d",
                        "YesMetaZFC.SetTheory.Structure.IsSequenceOfLength.restriction",
                        "YesMetaZFC.SetTheory.Structure.IsRecursiveSequence.restriction"]
CH_CHOICE_FREE = [PREFIX + "Internal." + n for n in
                  ("binary_pred_m", "Chain_d", "Closed_d", "Coll_d", "coll_m", "Dec_check_d", "dec_check_m")]
CH_CHOICE_FREE += ["YesMetaZFC.SetTheory." + n for n in
                   ("CH_d", "hartogs_m", "ch_m", "ch_sentence_l", "ZFC_CH",
                    "values_enum_l", "env_enum_l", "query_holds_l",
                    "ZFC.Next_d", "ZFC.next_m", "ZFC.iter_m")]

if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    result = main(MODULES, CHOICE_FREE, [], "FORCING_GUARD_PASS")
    if result == 0:
        result = main(ZFC_MODULES, [], ZFC_BASELINE, "FORCING_ZFC_GUARD_PASS")
    if result == 0:
        result = main(INTERNAL_MODULES, INTERNAL_CHOICE_FREE, INTERNAL_BASELINE, "FORCING_INTERNAL_GUARD_PASS")
    if result == 0:
        result = main(CHOICE_MODULES, ["YesMetaZFC.SetTheory.ZFC." + n for n in
            ("Rem_d", "rem_m", "Enum_step_d", "enum_step_m")], CHOICE_BASELINE, "FORCING_CHOICE_GUARD_PASS")
    if result == 0:
        result = main(CH_MODULES, CH_CHOICE_FREE, CHOICE_BASELINE, "FORCING_CH_GUARD_PASS")
    sys.exit(result)
