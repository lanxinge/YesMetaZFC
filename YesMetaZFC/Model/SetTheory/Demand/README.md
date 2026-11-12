# 深度调度与 demanding 构造

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [Graph](Graph.lean) | 任意有限排列后的双图恢复 |
| [NodeScope](NodeScope.lean) | 内部有限指定坐标组的完整集合程序；两组原变量形成同一完整节点的内部程序；7.1 双组完整节点的实际类型查询；固定 demanding 节点查询的一阶证书 |
| [Realize](Realize.lean) | 指定待回应标签的实际后继秩界；原两图、指定 pending 与高度的实际典范元组；从原树、指定字母和实际秩层生产完整回答查询 |
| [RecordSyntax](RecordSyntax.lean) | 完整双图回合记录的一阶表示 |
| [Recovery](Recovery.lean) | 原 subtype 的同一次实现恢复两图与指定待回应值 |
| [Reply](Reply.lean) | 同一树中两组辅助字母的最小载体；同一树的两个最小辅助字母域的一阶表示；demanding 查询所用的内在完整树性质；7.1 的指定待回应标签及实际类型成员 |
| [ReplyRestore](ReplyRestore.lean) | 任意回答排列的根与两新增槽；任意回答与原两图记录之间的实际排列；原回答类型的两图恢复与严格下降 |
| [Separated](Separated.lean) | 双辅助字母域的不交不变量 |
| [TagSyntax](TagSyntax.lean) | 标签解码框架的完整一阶规格 |
| [Untag](Untag.lean) | 辅助字母及有限图的实际标签编码；逐项标签编码与实际末项追加交换；标签编码精确保留完整三坐标节点；同一辅助树的实际标签重编码数据 |
