# 实数与有限图编码

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [FunctionCode](FunctionCode.lean) | 可数值图的实数编码 |
| [Prefix](Prefix.lean) | 内部有限前缀与无限延拓 |
| [RealChoice](RealChoice.lean) | 任意内部坐标重编号诱导连续实数映射；一个内部实数编码可数列实数；实数行列的内部编码与常行对角映射；仅对内部实数使用的可数选择 |
| [RelationCode](RelationCode.lean) | 自然数关系及一般实数的规范二值编码；二值解码的有界检查与实际函数构造；可数良序的单实数编码 |
| [SequenceCons](SequenceCons.lean) | 任意字母表上的无限列首项拼接 |
