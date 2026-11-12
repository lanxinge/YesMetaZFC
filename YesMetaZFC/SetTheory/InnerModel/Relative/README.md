# 相对 Jensen 构造、L(ℝ) 与收益呈示

以传递集合 S 为起层的相对 Jensen 递归给出 `Ja_d`，并类为 `La_d S`。
在 ZF 背景中，规范 ω→ω 实数集合 B 及 S=TC({B}) 唯一确定 `lr_model_l`。
`lr_model_zf_l` 证明该模型满足 ZF；`lr_real_l` 保留背景的每个内部实数。
本层不使用大基数假设。

## 模块

| 模块 | 数学内容 |
| --- | --- |
| [Hierarchy](Hierarchy.lean) | 以传递集合为基的 Jensen 递归；相对 Jensen 层的存在、唯一性与层级方程 |
| [PayoffImage](PayoffImage.lean) | 同一较低 Jensen 层上的收益运输 |
| [PayoffLayer](PayoffLayer.lean) | 任意相对收益的共同 Jensen 层 |
| [PayoffModelMinimum](PayoffModelMinimum.lean) | 派生 Jensen 模型的实际有限参数表示；内部有限实数列合并为一个二值实数参数；一个固定公式呈示 L(ℝ) 的全部收益集；固定公式及实数参数的实际收益代码 |
| [PayoffQuerySound](PayoffQuerySound.lean) | L(ℝ) 中 AD 的原句子与实际模型语义；完整旧收益表的有界核验；最小坏收益的合并有界检查；最小坏收益的完整博弈见证 |
| [TruthImage](TruthImage.lean) | 函数实数族的传递种子沿成员满嵌入保持；原派生模型断言向弱目标的公式运输 |
| [TruthSyntax](TruthSyntax.lean) | 相对 J 并类、统一层界与有界分离；相对 J 并类的实际结构与基础封闭性；原公式在相对 J 并类中的统一相对化；相对 J 层上的有限公式反射 |

## 决定性与呈示

`Axioms.lr_ad` 是原一阶句子；`lr_ad_axiom_sat_l` 将它与规范 L(ℝ) 的内部 AD 对应。
原 AD 使用完整 Baire 空间、全部有限局面和内部策略，收益遍历模型内的全部实数子集。

`Jp_d` 用固定公式、实数参数、序数代码和实际 Jensen 层呈示收益。
参数表示覆盖 L(ℝ) 的全部收益；代码的唯一性用于最小坏收益及正负查询的一致性。
有界证书先在 L(ℝ) 内构造，再由传递包含送到背景；模型之间的收益运输保留同一代码和层。

`lr_counterexample_data_l` 从原句子的否定实际构造反例资料。
策略通过规范局面编号编码为实数，有界决定性与原 `Det_d` 等价。
弱测试壳只反射这些实际有界资料，不能把其内部实数迹直接认作背景全部实数。

大基数终点已由 [wd_lr_ad_l](../../LargeCardinal/Determinacy/LReal.lean) 完成，
前提为 ZFC＋真类 Woodin。该蕴涵位于大基数层，本层的定义和模型构造不依赖它。
完整证明路线和较弱前提版本的边界见 [L(ℝ) 的 AD](../../../../markdown/LR_AD.md)。
