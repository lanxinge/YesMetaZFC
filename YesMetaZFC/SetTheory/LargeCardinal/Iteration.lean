import YesMetaZFC.SetTheory.LargeCardinal.IterationAgreement
import YesMetaZFC.SetTheory.LargeCardinal.IterationLocalAgreement
import YesMetaZFC.SetTheory.LargeCardinal.IterationFork
import YesMetaZFC.SetTheory.LargeCardinal.IterationLimit
import YesMetaZFC.SetTheory.LargeCardinal.IterationPadding
import YesMetaZFC.SetTheory.LargeCardinal.IterationDescent
import YesMetaZFC.SetTheory.LargeCardinal.IterationInitial
import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptRegular
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
`it_nice_no_drop_l` 用内部依赖选择构造 ω 历史列，再由基础公理排除末模型下降。
`ja_failure_l` 从返回嵌入的失败实际构造联合尝试关系及正则基数值下降秩。
尝试链解码得到共尾枝、完整初等腿和实际传递直接极限，根复合式精确保留。
复制整树中的移位秩、正则秩段的 Skolem 回拉及 nice 树弱迭代策略仍未完成。
-/
