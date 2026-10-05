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
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEmbeddingCountable
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemStep
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBranch

/-! # 扩展器理论的公共入口

ZF 中的有限支撑预扩展器、短扩展器、原公式与语义、实际幂集算子及其布尔、
乘积、坐标和有界投影运算、长度截断，以及武丁强嵌入的标准短扩展器识别。
现有源超幂系统与良基极限直接消费 Ex_short_d；源装配的 ZFC 边界单独保留。
woodin_rank_strength_l 按 ν 自动选长，恢复 Vν 覆盖、谓词一致性及完整谓词初等嵌入。
相对测度族可跨模型施加；双映射复制自动构造两侧超幂、唯一初等复制及常值交换方块。
相同扩展器的两次施加保持完整 L 上的有限幂子集一致性，且 L 本身属于两侧后继；
坍塌后的复制在 L 上等于 σ。原 μ<L 接口已迁移到包含端点的接口。
两个入口均实际构造传递后继及下一次施加的源证书，复制只消费目标侧的可数共同纤维。
源证书包含小外延关系的实际塌缩闭包；`Ea_agree_d.transitive_l` 从源内的小枚举图自动编码关系，
再由有限幂一致性和目标内塌缩证明同一个传递集合属于另一源。
`ep_copy_countable_restriction_l` 从源内可数旧嵌入、内部不可数共尾性及支撑以下一致性，
实际构造复制在已枚举传递域上的限制图。不可达 Vκ 的 κ 枚举及 Hχ 中的成员资格已有实际构造。
`Er_level_d` 将相对秩历史与实际枚举一同传输，并直接供秩段限制恢复使用。
`Ep_source_d.tree_branch_l` 另消费独立枝反射，在任意字母表的源内前缀树上构造源内分支。
`Ep_source_d.at_tree_l` 实际构造检验全部内部公式的嵌入尝试树；
`Ep_source_d.countable_membership_l` 从源内可数域及外部完整初等图，返回保留规定限制的
源内完整初等嵌入及其图的源内可数性见证。
`sh_source_iff_l` 保持模型内小 Skolem 壳及实际枚举；`ep_skolem_step_l` 构造源内壳、
传递塌缩与小枚举，再由两源的有限幂一致性证明塌缩属于另一源。
弱源接口已直接适用于正则 Vβ，无强极限前提；源内小性、统一化、塌缩与后继调用均已迁移。
`ep_skolem_rank_step_l` 已将源内尝试树回收、严格秩界及 Vκ∪{κ,σ} 的指定种子调整接通；
返回属于两源的新传递模型，嵌入与可数性见证属于新模型自身，指定低秩值保持不变；
同一输出自动保留完整源、枝反射、层级及小壳闭包。
`Ex_short_d.node_l` 自动构造携带上述不变量的实际短扩展器后继；枝反射经同一共同纤维证明。
`Ep_source_d.rank_l` 与 `skolem_rank_l` 保持内部正则秩段的源证书及小壳性质。
完整 Pₙ 递归仍未完成：任意树内的相对短扩展器判断尚不能直接代入背景共同纤维入口，
复制嵌入的秩段限制和全部前驱的相容性仍需统一装配。
-/
