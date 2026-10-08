import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderProduct
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTruncation
import YesMetaZFC.SetTheory.LargeCardinal.WoodinStrength
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyApplication
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopySuccessor
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelCode
import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingRankRestriction
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankAgreement
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyBounded
import YesMetaZFC.SetTheory.LargeCardinal.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTreeBranch
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEmbeddingCountable
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemStep
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBranch
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLevelTransfer
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLocalRead
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSuccessors
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderOmegaClosed
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetCopy
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankLift

/-! # 扩展器理论的公共入口

ZF 中的有限支撑预扩展器、短扩展器、原公式与语义、实际幂集算子及其布尔、
乘积、坐标和有界投影运算、长度截断，以及武丁强嵌入的标准短扩展器识别。
现有源超幂系统与良基极限直接消费 Ex_short_d；源装配的 ZFC 边界单独保留。
woodin_rank_strength_l 按 ν 选择实际不可达 L>ν，恢复整个 V_L 覆盖、谓词一致性及完整谓词初等嵌入。
不可达选择消费原武丁测度的正则性和强极限性证明；同一目标缺少某个 L 的子集，最大强度恰为 L。
`Ex_strength_d` 保留源内实际有界超幂及求值图；原强度公式随完整初等图搬运，
`realize_l` 在指定超幂中读出相对最大强度，未把像支撑当作背景不可达基数。
同一入口还构造所属模型中的原始不可达性与短扩展器判断；不可达性沿完整初等图及严格极限秩截断保持。
`Ep_strong_limit_d.rank_l` 用实际秩层枚举自动构造严格正则截断的源，并保留原扩展器的最大强度、
秩层枚举、内部不可达性及短扩展器判断；有界超幂保留同一节点、传递像和求值图。
相对测度族可跨模型施加；双映射复制自动构造两侧超幂、唯一初等复制及常值交换方块。
相同扩展器的两次施加保持完整 L 上的有限幂子集一致性，且 L 本身属于两侧后继；
坍塌后的复制在 L 上等于 σ。支撑秩段带实际枚举时，复制在 L 本身及整个 j(κ)+1 上也等于 σ。
复制入口固定原树的实际超幂，并保留目标实际超幂和两张常值箭头的交换方块；所属判断沿原初等图搬运。
源证书包含小外延关系的实际塌缩闭包；`Ea_subset_d.transitive_l` 从源内的小枚举图自动编码关系，
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
同一输出自动保留完整源、枝反射、层级、相对幂集及小壳闭包。
`Ex_short_d.node_l` 自动构造携带上述不变量的实际短扩展器后继；枝反射经同一共同纤维证明。
`Ep_source_d.rank_l` 与 `skolem_rank_l` 保持内部正则秩段的源证书及小壳性质。
`It_local_d.apply_l` 从内部所属判断、有限幂的相对幂集及子集一致性直接构造初等定向极限；
`bounded_model_l` 自动构造留在所属源中的有界分量商。
嵌套两源之间的源内可数层族由有限 κ 幂一致性搬运；`source_fiber_l` 再用所属模型的
枝反射和原可数共同纤维公式得到实际源内 κ 值纤维。
`It_local_d.source_wf_l` 已从任意下降链构造统一源内代表界、实际源内约束列与共同纤维，
证明相对后继良基性。无枝标签关系复用同一回收与求值，给出后继枝反射保持。
`It_local_d.node_l` 从内部所属判断直接构造同一实际超幂边及全部下一步不变量。
`It_local_d.closed_limit_l` 从所属源对有界值域的背景 ω 序列闭性构造跨模型良基超幂；
逐步选择的测度一集合均由原所属测度回收，不要求所属源包含于施加源。
`It_ultra_d.closed_l` 从共同强度秩段和所属源内部的 ω 正则界证明 nice 后继保持
背景 ω 闭性；`ep_value_apply_l` 在同一实际超幂中读取 j(f)(a)=[a,f]。
`ep_set_value_l` 搬运整张有限真值表，在 j(A) 中读取任意代表赋值的全部内部
公式；不要求 A 的高度正则，也不要求目标赋值属于常值嵌入的像。
`ep_set_copy_l` 将 π:M→A 复制为原实际后继到 j(A) 的完整初等图，保持常值
交换方块、长度端点及全部有限 L 幂子集上的 σ；包含因子通过有限代表矩阵
直接证明全部内部公式的保持，代表求值的外层目标与复制图的小目标分别保留。
`atoms_l` 和 `normal_l` 直接读取内部原子条件与源内正规性；`successors_l` 构造两侧
后继并证明支撑端点上的子集一致性。`subsets_l` 通过源内有界迹将自身超幂的子集
送回所属模型，复合后直接给出小模型编码所需的 `Ea_subset_d`；全部单向搬运接口已迁移。
`it_ultra_rank_l` 证明内部正则秩段的超幂恰为 j(Vα)，并保留实际限制 j↾Vα 作为同一超幂边。
`it_ultra_unique_l` 识别同源同扩展器的实际超幂及嵌入；`it_ultra_rank_agree_l` 将共同
正则秩段送到同一秩段，保留同一限制嵌入，并给出该像高度以下的有限幂子集一致性。
`it_ultra_owned_image_l` 用支撑秩段的实际枚举控制全部有界代表节点，在所属源中
还原同一个超幂像及求值图；`Eb_collapse_d` 保留实际节点关系与有界塌缩证书。
`eb_owned_value_l` 双向搬运 κ 值代表，直接把施加超幂的实际 j(κ) 及求值图放回所属源；
`Eb_collapse_d.map_l` 传输全部节点及原求值图，`realize_l` 辨认为目标施加超幂的同一值。
`Ea_maps_d.function_l` 从有限幂编码推出两图在 κ 值函数上一致；`ep_copy_bounded_l`
由此证明复制与 σ 在 j(κ) 以下相同，常值方块处理端点；普通后继复制和集合像复制均使用同一接口。
`Ea_maps_d.set_function_l` 进一步搬运集合值代表的完整成员编码；`Eb_trace_d` 保留所属源
实际分离出的完整支撑迹。其传输和跨源读取证明 `ep_copy_subsets_l`，得到有限 L 幂子集上的映射一致性。
`Ea_maps_d.transitive_l` 再以源内实际枚举的关系码和塌缩唯一性，证明整个被枚举传递集合上逐点一致；
同一后继复制入口已返回这一结论及原来的限制图恢复。
`ep_countable_ultra_l` 在包含源内构造全部原代表及测度一关系，借满射呈示回收同一个
原超幂及其可数编号。复制入口从旧嵌入图的源内可数性自动产生这些输入；
原超幂的成员资格、定义域和编号均由实际构造给出。
`ep_set_restriction_l` 以有限真值表证明集合限制的完整内部初等性。
`It_local_d.rank_l` 保持严格极限秩段中的原短扩展器公式，包括内部极大性及可数共同纤维。
`It_local_d.of_rank_l` 将同一原公式向上读取；`Ex_strength_d.of_rank_l` 保留同一个
有界坍塌和最大强度证书，均只要求拥有的极限秩段。
`It_local_d.return_l` 将指定实际后继的支撑子集送回原所属模型，复制入口同步返回这一性质。
Pₙ 全前驱递归与递降模型反证已完成；整树复制、移位秩及 Skolem 回拉仍待接通，
nice 树弱迭代策略、一般迭代策略与 L(R) 的 AD 尚未证明。
-/
