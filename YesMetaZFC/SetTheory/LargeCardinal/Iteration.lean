import YesMetaZFC.SetTheory.LargeCardinal.IterationAgreement
import YesMetaZFC.SetTheory.LargeCardinal.IterationLocalAgreement
import YesMetaZFC.SetTheory.LargeCardinal.IterationFork
import YesMetaZFC.SetTheory.LargeCardinal.IterationLimit
import YesMetaZFC.SetTheory.LargeCardinal.IterationPadding
import YesMetaZFC.SetTheory.LargeCardinal.IterationDescent
import YesMetaZFC.SetTheory.LargeCardinal.IterationInitial
import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptRegular
import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyTree
import YesMetaZFC.SetTheory.LargeCardinal.IterationNiceReturn
import YesMetaZFC.SetTheory.LargeCardinal.IterationWeak
import YesMetaZFC.Model.SetTheory.Internal.SourceRankSizeInitial

/-! # 迭代树、后继扩张与极限添枝的公共入口

任意内部序数长度的树序、模型列、完整初等嵌入列和操作列；单根、pad、
任意树前驱上的实际超幂扩张、后继一致性及三结点分叉均有自动构造。
`it_local_apply_l` 从嵌套模型中的内部短扩展器及有限幂一致性自动构造活动步，
返回加入原树的同一实际节点以及枝反射、层级、相对幂集、传递包络和小壳不变量。
`it_local_apply_agree_l` 同时构造所属模型的实际超幂，保留两侧后继的一致性，并把
支撑范围内的新子集送回原所属模型。
共尾枝的实际直接极限、完整规范初等嵌入、传递坍塌及整树极限扩张均已构造。
共尾度大于 ω 时用 ZF＋DC 证明枝极限良基；可数共尾长度的可延伸树由最小
后继递归选枝，实际相容的良基实现保证所得枝良基，只需 ZF。
任意内部极限长度的 padding 树提供直接实例。
`pn_copy_step_l` 从指定实际超幂中的严格正则秩段构造下降模型，旧图在整个
支撑秩段及端点上保持相同，原缺失子集见证和新旧目标的共同秩段一并保留。
下降模型、嵌入行和全部内部有限历史均有一阶编码；`pn_initial_row_l` 从可数
传递域的给定初等图自动回收模型内图和可数编号。`pn_history_extend_l` 从原树
及实际正则秩段列延伸每段历史，保持所有前驱的一致性及缺失子集。
`it_pnice_no_drop_l` 在恒等段保持同一秩段，对全部有限历史先取末模型、再取原高度的隶属极小值，排除连续下降。
`ja_failure_l` 从返回嵌入的失败实际构造联合尝试关系及正则基数值下降秩。
尝试链解码得到共尾枝、完整初等腿和实际传递直接极限，根复合式精确保留。
`Ic_model_d` 编码可数闭工作模型，正规秩层提供实际初值；`rank_apply_l` 将拥有
秩段中的 nice 扩展器向上读取，构造完整工作源上的同一超幂、可数闭后继及共同强度秩段。
`Ic_row_d.copy_l` 用实际类依赖选择及相容图列取并构造长度 ω 的整棵 nice 复制树；
保持同一树序、全部前驱一致性、常值方块、原根嵌入及每个可数闭工作模型中的拥有目标秩段。
联合节点的完整初等性已迁移到实际有限真值证书；`Ja_space_d.full_image_l` 用源内
绝对性及有限部分图闭性证明像树包含全部背景联合节点，并保持原严格扩展关系。
`it_countable_fixed_l` 固定原树序、模型列、嵌入列及枚举列；`Ic_history_d.rank_l`
构造定义域恰为内部 ω 的移位高度列，在每条严格树边上证明新高度小于旧高度的像。
高度在所属模型内正则；`rank_cut_l` 构造包含同一扩展器与支撑的实际秩段列。
`it_pnice_failure_copy_l` 从可数 nice 树的返回失败自动装配正规根上的完整下降反例。
`it_ultra_read_l` 从传递有限闭源中的相对超幂证书恢复原指定超幂边；有限幂、商类、
直接极限、常值图、坍塌和复合图全部保留，完整初等性由原 Łoś 定理重新证明。
`rank_read_source_l` 为任意包含 ω 的拥有极限秩段提供读取闭性，不要求高度正则。
`it_pnice_return_l` 对整棵反例取有限反射层与可数壳，恢复原 nice 树和实际下降秩段，
由原正则根构造 Pₙ 初始行，最后调用下降反证。因而任意可数 nice ω 树的给定
根嵌入都沿某条共尾良基枝返回原 Vθ，根复合式精确保留，无需额外高度假设。
`it_nice_weakly_iterable_l` 自动构造实际 ω₁ 及公开枝策略。后继应答使用原 nice 树返回定理，
可数极限先取全部相容旧图的并，再构造同一商投影的传递极限与规范腿。
内部选择函数产生唯一超限运行，合法历史的原公式归纳排除失败；唯一重放把内部
返回列消去，得到只读公开走法历史的集合函数。获胜证书覆盖直到 ω₁ 的所有初始对局。
-/
