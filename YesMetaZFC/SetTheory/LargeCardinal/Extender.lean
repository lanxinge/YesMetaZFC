import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderProduct
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTruncation
import YesMetaZFC.SetTheory.LargeCardinal.WoodinStrength
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyApplication
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopySuccessor

/-! # 扩展器理论的公共入口

ZF 中的有限支撑预扩展器、短扩展器、原公式与语义、实际幂集算子及其布尔、
乘积、坐标和有界投影运算、长度截断，以及武丁强嵌入的标准短扩展器识别。
现有源超幂系统与良基极限直接消费 Ex_short_d；源装配的 ZFC 边界单独保留。
woodin_rank_strength_l 按 ν 自动选长，恢复 Vν 覆盖、谓词一致性及完整谓词初等嵌入。
相对测度族可跨模型施加；双映射复制自动构造两侧超幂、唯一初等复制及常值交换方块。
相同扩展器的两次施加保持每个 μ∈L 上的有限幂子集一致性；坍塌后的复制在 L 上等于 σ。
两个入口均实际构造传递后继及下一次施加的源证书，复制只消费目标侧的可数共同纤维。
-/
