"""超幂、约化积和 Łoś 的实际声明审计。

只准 Prop 内经典推理；数据构造端点严格排除 Classical.choice。
见证拼接是公开前提，不以宿主选择定理自动填充；不接受 native_decide 公理。
"""
import sys

from check_filters import main

MODULES = [
    "YesMetaZFC.SetTheory.Filter.Logic",
    "YesMetaZFC.Model.ReducedProduct.Germ",
    "YesMetaZFC.Model.ReducedProduct.Structure",
    "YesMetaZFC.Model.ReducedProduct.Los",
    "YesMetaZFC.Model.Ultrapower",
]
PREFIX = "YesMetaZFC.Logic.FirstOrder."
CHOICE_FREE = ["YesMetaZFC.SetTheory.Filter." + n for n in (
    "congr_l", "pointwise_l", "and_iff_l", "point_l", "point_mem_l", "point_proper_l",
)] + ["YesMetaZFC.Model." + n for n in ("germSetoid_l", "Germ_l")] + [
    "YesMetaZFC.Model.Germ_l." + n for n in (
        "class_l", "class_eq_l", "induction_l", "exists_rep_l", "map_l", "map₂_l",
        "pred_l", "map_class_l", "map₂_class_l", "pred_class_l",
    )
] + [PREFIX + "ReducedProduct." + n for n in (
    "Nonempty_m", "product_m", "values_m", "values_class_m", "structure_m", "projection_m",
    "quotient_m", "relation_class_m", "assignment_surjective_m", "env_surjective_m",
    "Witness_m", "WitnessData_m", "witness_of_data_m", "Choice_m",
)] + [PREFIX + "Ultrapower." + n for n in (
    "nonempty_m", "structure_m", "constant_m", "diagonal_fn_m", "Witness_m",
    "constant_projection_m", "principal_witness_m", "evaluation_m",
)]

if __name__ == "__main__":
    sys.exit(main(MODULES, CHOICE_FREE, [], "ULTRAPOWER_GUARD_PASS"))
