import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderProduct
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTruncation
import YesMetaZFC.SetTheory.LargeCardinal.WoodinStrength
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyApplication
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopySuccessor
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelCode
import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingRankRestriction
import YesMetaZFC.SetTheory.LargeCardinal.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTreeBranch

/-! # 扩展器理论的公共入口

ZF 中的有限支撑预扩展器、短扩展器、原公式与语义、实际幂集算子及其布尔、
乘积、坐标和有界投影运算、长度截断，以及武丁强嵌入的标准短扩展器识别。
现有源超幂系统与良基极限直接消费 Ex_short_d；源装配的 ZFC 边界单独保留。
woodin_rank_strength_l 按 ν 自动选长，恢复 Vν 覆盖、谓词一致性及完整谓词初等嵌入。
相对测度族可跨模型施加；双映射复制自动构造两侧超幂、唯一初等复制及常值交换方块。
相同扩展器的两次施加保持完整 L 上的有限幂子集一致性，且 L 本身属于两侧后继；
坍塌后的复制在 L 上等于 σ。原 μ<L 接口已迁移到包含端点的接口。
两个入口均实际构造传递后继及下一次施加的源证书，复制只消费目标侧的可数共同纤维。
源证书包含实际塌缩闭包；`Ea_agree_d.transitive_l` 从源内的小枚举图自动编码关系，
再由有限幂一致性和目标内塌缩证明同一个传递集合属于另一源。
`ep_copy_countable_restriction_l` 从源内可数旧嵌入、内部不可数共尾性及支撑以下一致性，
实际构造复制在已枚举传递域上的限制图。不可达 Vκ 的 κ 枚举及 Hχ 中的成员资格已有实际构造。
`Er_level_d` 将相对秩历史与实际枚举一同传输，并直接供秩段限制恢复使用。
`Ep_source_d.tree_branch_l` 在任意字母表的源内前缀树上构造源内分支。
嵌入尝试树的实际编码、模型内小壳装配及递降模型反证仍未完成。
-/
