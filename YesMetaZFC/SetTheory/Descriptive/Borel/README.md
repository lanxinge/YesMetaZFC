# Borel

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [Boolean](Boolean.lean) | 内部良基布尔递归 |
| [Pullback](Pullback.lean) | 在叶节点增加一层并节点；连续逆像码的唯一原公式构造；连续逆像码的整树求值对应 |
| [RankRelative](RankRelative.lean) | Borel 码树的内部序数秩；标准 Borel 层级的内部超限递归；Borel 层级的基层、补集、升层与可数并规则；Borel 树全部节点的实际解释集合 |
| [Relabel](Relabel.lean) | 内部 Borel 码的树语法；Borel 码的内部求值与集合解释；Borel 码的节点方程与三条求值规则；可数码族的内部子树拼接 |
| [Universe](Universe.lean) | 基本柱集的规范单节点码；可数并交的规范码算子；开集与闭树体的 Borel 码；内部 Borel 集及空间实例 |
