# 深度调度与 demanding 构造

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [DemandCounterWeave](DemandCounterWeave.lean) | 固定原对局的补树博弈规则；补树博弈的实际检查集、闭收益及控制；补树游戏及其先手获胜参数的原公式；原先手胜策在完整轮后的实际挑战 |
| [InputIteration](InputIteration.lean) | 交替博弈输入的确定递归及有限前缀因果性 |
| [MapIteration](MapIteration.lean) | 内部函数迭代及首步交换 |
