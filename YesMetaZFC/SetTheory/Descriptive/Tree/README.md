# Tree

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [HistoryTree](HistoryTree.lean) | 字母映射下树的逆像；指定旧对局或指定策略的有限历史树 |
| [RetractionFixed](RetractionFixed.lean) | 全部输入字母驱动的内部历史递归；有限输入上的确定求值表；对全部内部有限历史作末项归纳；无终端节点树上的实际纠正表 |
| [ScanStrategy](ScanStrategy.lean) | 最小编号驱动的三步响应表；最小请求递归产生原有限历史策略 |
| [Trace](Trace.lean) | 内部实数投影与相对补；内部子空间的迹与点类集合 |
| [TreeShift](TreeShift.lean) | 无约束首项的树 |
| [TreeTail](TreeTail.lean) | 内部逐项延拓的分支；模型内部前缀树与闭集；内部前缀树地址的首项拼接；补齐树的第一层而不改变无限枝 |
| [TreeWellFounded](TreeWellFounded.lean) | 任意字母表前缀树的有界子边；任意集合字母表上的无枝树与良基性；有限前缀树上的秩沿任意真延长下降；任意集合树的序数秩证书 |
