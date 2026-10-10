# 内部小模型与 properness

主条件、内部初等闭包、N[G] 提升、H(χ) 对应及 proper 扩张保持。

[总索引](../INDEX.md)

## 子目录

| 目录 | 模块数 | 职责 |
| --- | ---: | --- |
| [Elementary](Elementary/README.md) | 9 | 内部初等小模型的关系见证、原像、限制、可数集合及序数迹。 |
| [Family](Family/README.md) | 11 | 阶段索引的共同运算、统一 H(χ) 与 N、提升证书和实际交集 club。 |
| [Generic](Generic/README.md) | 18 | 实际求值函数图、可数性、存在见证、有限参数和全部内部公式的初等提升。 |
| [Hereditary](Hereditary/README.md) | 9 | 小名称定理、原子绝对性、H(χ) 泛型对应及实际 H(χ) 中的模型装配。 |
| [Master](Master/README.md) | 5 | 主条件的原公式、加强保持、名称形式、序同构与 CCC 主条件闭包。 |
| [Preservation](Preservation/README.md) | 5 | 旧可数性反射、ω₁ 保持、新可数集合的旧覆盖与 ω 共尾性保持。 |

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Syntax.lean](Syntax.lean) | `InternalProperSyntax.lean` | properness 的内部 club 主条件刻画 |
| [Base.lean](Base.lean) | `InternalProperBase.lean` | properness 的实际 club 见证与初等模型主条件 |
| [Name.lean](Name.lean) | `InternalProperName.lean` | proper 后继的统一 club 名称 |
| [Forcing.lean](Forcing.lean) | `InternalProperForcing.lean` | 固定 N[G] 内主加强的存在力迫 |
| [Basic.lean](Basic.lean) | `InternalProper.lean` | CCC 的 properness 与实际主条件装配 |
