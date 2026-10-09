# 相对 Jensen 层级、L(ℝ) 与决定性目标

公开入口为 `YesMetaZFC.SetTheory.InnerModel`，命名空间为
`YesMetaZFC.SetTheory.InnerModel.Relative`。实数采用 Kuratowski 编码的内部 Baire 空间。
模型可外部非良基、ω 非标准；所有层号、递归历史、策略和对局均在原模型中解释。

对实际传递集合 S，定义并证明

\[
J^S_0=S,\qquad J^S_{\alpha+1}=\operatorname{Rud}(J^S_\alpha\cup\{J^S_\alpha\}),
\qquad J^S_\lambda=\bigcup_{\alpha<\lambda}J^S_\alpha.
\]

`La_d S` 是这些层的并类。取 S=TC({ℝ}) 得到这里的 L(ℝ)。起层约定见
[Schlicht 论文 §1.2](https://noah.nrw/ulbmshsnoah/download/pdf/4279230#page=21)。
本构造沿用仓库已有 rud 有限基及 J 索引；与独立 Def 递归、一般 rud 项定义的
比较仍属于主指南中列出的未完成工作。

| 接口 | 已证明内容 | 背景 |
| --- | --- | --- |
| [Hierarchy](Hierarchy.lean)：`ja_value_exists_l`、`ja_value_unique_l`、`ja_zero_l`、`ja_successor_l`、`ja_limit_l` | 实际内部层递归、存在唯一性、三条层级方程 | KPi |
| [Class](Class.lean)：`la_bound_l`、`la_separation_l`、`la_ordinal_l` | Σ₁ 证书收集给出统一层界；有界分离；包含全部内部序数 | KPi；后两项要求 S 传递 |
| [Relativization](Relativization.lean)：`la_rel_sat_l` | 任意原公式在并类中的统一相对化及语义对应 | KPi，S 传递 |
| [Model](Model.lean)：`la_model_zf_l` | 子类型隶属结构满足原 ZF 全部公理、分离及收集模式 | ZF，S 传递 |
| [Reals](Reals.lean)：`lr_seed_exists_l`、`lr_reals_l` | 自动构造 ω、ℝ、TC({ℝ})；相对模型内部 ω、完整 Baire 空间与背景一致 | ZF |
| [LReal](LReal.lean)：`lr_model_l`、`lr_model_zf_l` | 无需调用者选择起层的规范 L(ℝ) 结构及完整 ZF 模型性 | ZF |
| [LReal](LReal.lean)：`lr_transitive_l`、`lr_ordinal_l`、`lr_real_l` | 规范成员类传递，包含全部原序数与全部原实数 | ZF |
| [Determinacy](Determinacy.lean)：`lr_ad_axiom_sat_l` | 原句子 `Axioms.lr_ad` 恰好断言该规范模型满足 AD | ZF |

全分离通过有限公式反射落到实际 J 层，再调用有界分离。全收集将背景中取得的
见证集与并类求交，再取统一层界。内部幂集同样从背景幂集取迹并在层内分离。
这些证明不要求对象模型的 AC 或 DC。构造不使用 `noncomputable`；证明允许元层经典逻辑。

[Game](../../Descriptive/Game.lean) 的策略是全部内部有限局面到 ω 的集合函数，
先手占偶数坐标、后手占奇数坐标。服从条件逐内部长度读取实际前缀与落子。
[Determinacy](../../Descriptive/Determinacy.lean) 的 `AD_d` 遍历 ℝ 的全部内部子集，
`Axioms.ad_axiom` 与此语义已证明对应。没有把模型外部策略代入内部 AD。

下一阶段的结论已固定为 `Axioms.lr_ad`，前提句子为
[`Axioms.woodin_proper`](../../LargeCardinal/Woodin.lean)。本层没有证明两者之间的
蕴涵。源内部 extender 超幂、迭代树及 nice 树弱可迭代性的已证接口见
[LargeCardinal](../../LargeCardinal/README.md)；齐性树、泛型迭代及相应决定性定理仍待完成。
L(ℝ) 的 ZF 模型性与“大基数推出其中 AD”分别是已完成和待完成的数学内容。
