"""审计力迫偏序、布尔完备化、名称解释与相对扩张，不引入测试用 Lean 模块。

稠密性证书在 Prop 内使用经典逻辑；规范映射函数和布尔运算分别严格审计。
"""
import sys

from check_filters import main

MODULES = ["YesMetaZFC.Model.Forcing." + n for n in
           ("Order", "Density", "Separative", "Boolean", "Tree",
            "RegularOpen", "Completion", "Cohen", "Generic", "Valuation",
            "BooleanGeneric", "Truth", "NameGeneric", "Extension", "RealName", "CohenReal")]
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

if __name__ == "__main__":
    sys.exit(main(MODULES, CHOICE_FREE, [], "FORCING_GUARD_PASS"))
