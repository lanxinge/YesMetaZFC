# 博弈与策略

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [Closed](Closed.lean) | 闭集的规范前缀树表示 |
| [ClosedDeterminacy](ClosedDeterminacy.lean) | 首次违规者输的闭收益集合；首次违规的唯一性及玩家 II 违规后的吸收；首次违规收益的完整一阶表示；全部有限轮均合法的内部历史树 |
| [FirstViolationMonotone](FirstViolationMonotone.lean) | 非法对局总有内部最早违规；只放宽本方合法步时的闭收益单调性 |
| [GameAttemptRank](GameAttemptRank.lean) | 获胜策略在合法有限历史上的实际后继；原获胜策略的有限历史控制集合；II 获胜策略的合法尝试树有实际序数秩 |
| [GameShift](GameShift.lean) | 自然数博弈、策略与获胜；AD 的原一阶句子；内部回合在后继处换手；插入一手后换手的实际策略 |
| [GameStrategyProjection](GameStrategyProjection.lean) | 只在本方回合定义的实际策略；只定义在本方回合的策略全域化；本方回合策略到固定时序策略 |
| [GameWitness](GameWitness.lean) | 全部有限局面的规范自然数编号；自然数博弈的全部策略由实数编码；博弈基础数据的有界识别；只量化实数及有限局面的有界决定性公式 |
