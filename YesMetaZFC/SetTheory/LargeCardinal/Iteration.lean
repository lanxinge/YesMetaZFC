import YesMetaZFC.SetTheory.LargeCardinal.IterationAgreement
import YesMetaZFC.SetTheory.LargeCardinal.IterationFork
import YesMetaZFC.SetTheory.LargeCardinal.IterationLimit
import YesMetaZFC.SetTheory.LargeCardinal.IterationPadding

/-! # 迭代树、后继扩张与极限添枝的公共入口

任意内部序数长度的树序、模型列、完整初等嵌入列和操作列；单根、pad、
任意树前驱上的实际超幂扩张、后继一致性及三结点分叉均有自动构造。
共尾枝的实际直接极限、完整规范初等嵌入、传递坍塌及整树极限扩张均已构造。
共尾度大于 ω 时用 ZF＋DC 证明枝极限良基；可数共尾长度的可延伸树由最小
后继递归选枝，实际相容的良基实现保证所得枝良基，只需 ZF。
任意内部极限长度的 padding 树提供直接实例；一般迭代策略仍未构造。
-/
