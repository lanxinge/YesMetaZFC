"""初等子结构的公理与数据边界审计；复用滤子切片的声明级检查器。

Tarski–Vaught 的全称量词步骤允许 Prop 内经典反证。所有新增数据定义及
直接复用接口单独排除 Classical.choice；本切片不接受 native_decide 公理。
"""
import sys

from check_filters import main

MODULES = ["YesMetaZFC.Model.Closure"] + [
    "YesMetaZFC.Model.FirstOrder." + m for m in ("Elementary", "Substructure", "Skolem")
]
PREFIX = "YesMetaZFC.Logic.FirstOrder."
CHOICE_FREE = [PREFIX + "Str_emb." + n for n in (
    "Elementary_m", "WitnessClosed_m", "witness_of_elementary_m",
    "elementary_of_surjective_m", "elementary_refl_m", "elementary_comp_m",
    "elementary_cancel_m", "elementary_models_iff_m",
)] + [PREFIX + "Substructure_m." + n for n in (
    "structure_m", "incl_m", "Params_m", "restrict_m", "map_restrict_m", "params_map_m",
    "term_mem_m", "Elementary_m", "WitnessClosed_m", "models_iff_m",
    "inclusion_m", "elementary_inclusion_m",
)] + ["YesMetaZFC.Model.RuleFamily_l." + n for n in (
    "of_operations_l", "Closed_l", "Closure_l", "closed_l", "least_l", "mono_l",
    "closure_iff_l", "idempotent_l", "reindex_l", "reindex_le_l", "reindex_iff_l",
    "sum_l", "sum_closed_iff_l", "union_l", "union_closed_iff_l", "closure_union_iff_l",
)] + [PREFIX + n for n in ("Skolem_m", "SkolemIndex_m")] + [PREFIX + "Skolem_m." + n for n in (
    "rules_m", "Closed_m", "witness_mem_m", "nonempty_m", "substructure_m",
    "witness_closed_m", "hull_m", "seed_mem_m", "hull_closed_m", "hull_le_m",
    "hull_mono_m", "hull_idem_m", "hull_union_iff_m", "hull_with_m",
    "hull_with_closed_m", "hull_with_le_m",
)]

if __name__ == "__main__":
    sys.exit(main(MODULES, CHOICE_FREE, [], "ELEMENTARY_GUARD_PASS"))
