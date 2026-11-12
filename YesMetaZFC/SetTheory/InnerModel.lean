import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Model
import YesMetaZFC.SetTheory.InnerModel.Computation.Readback
import YesMetaZFC.SetTheory.InnerModel.Computation.Library
import YesMetaZFC.SetTheory.InnerModel.ProofCode
import YesMetaZFC.SetTheory.InnerModel.Order.Statement
import YesMetaZFC.SetTheory.InnerModel.Condensation
import YesMetaZFC.SetTheory.InnerModel.GCH
import YesMetaZFC.SetTheory.InnerModel.Jensen.Definable
import YesMetaZFC.SetTheory.InnerModel.OD
import YesMetaZFC.SetTheory.InnerModel.HOD
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffQuerySound
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffModelMinimum

/-! # 内模型技术的共同基础

提供 KP 的 rudimentary 有限基、KPi 的内部 Σ₁ 成员递归、最小闭包及 J 层级。
J 自身满足 KPi，内部层级与背景层级一致，并满足原演绎核的 KP + V=L。
在 ZF 背景中，同一 J 结构满足 ZF + V=L；全分离、全收集和内部幂集均已验证。
独立集合程序具有 KP 总性、Δ₁ 图、Δ₀ 判定与 Σ₁ 见证验证编译，并提供 C 风格前端。
J 搜索在 KPi + V=L 中实现互补 Σ₁ 正规形与总布尔计算的双向等价。
J 构造推导码具有内部语法检查、Σ₁ 求值及覆盖性；精确码初段和唯一最小代表
产生 L 上无参数 Σ₁ 全局良序及初段函数。良序在 L 上为 Δ₁，与 J 内部解释绝对。
Jensen 逐层良序由同一无参数 Σ₁ 公式在每个非空 J 层内定义；各层均为其初段。
完整递归历史的局部存在性已证明，不要求单层满足 KP 或可容许性。
比较在每层内具有统一 Δ₁ 定义；完整初段属于该层，其函数图也统一局部 Σ₁。
微层状态、比较及初段在 J 内外一致；每个非空 J 层满足同一原语言全局良序句子。
内部 Σ₁ 初等子结构的实际坍塌是唯一 J 层，并有凝聚高度界和传递参数子集固定。
任意无限基数的小壳和 J 层基数界已实现；外部仅需 ZF，同一 L 模型满足 ZFC+GCH。
内部 OD 通过 V 层满足关系定义，允许非标准公式及有限参数列，等价于原公式的序数
参数唯一可定义性。单序数解码单值且覆盖 OD，公开谓词支持分离与内部传递结构相对化。
OD 与 HOD 均具有实际 Σ₂ 证书；OD 的唯一最小序数代表导出全局良序和集合初段。
背景仅需 ZF，实际 HOD 隶属结构满足原选择集公理，选择集自身属于 HOD。
两种集合参数版本已给出原公式陈述：HOD[A] 为实际 ZFC 模型，HOD(A) 为实际 ZF 模型；
全收集使用秩切片作内部见证池，允许非标准有限参数列且不使用背景选择公理。
HOD[A] 的有界序数关系呈现与总坍塌已构造。弱齐性力迫的 HOD/HOD[A] 比较
另由 Model.Forcing.Internal.Homogeneous.HOD 导出；具体边界和待建内容见 InnerModel/README.md。
相对 Jensen 层级在 KPi 上构造；任意传递基集的并类在 ZF 上满足原 ZF。
`Relative.lr_model_l` 以 TC({ℝ}) 为起层构造规范 L(ℝ)，保留全部序数与实数；
`lr_ad_axiom_sat_l` 精确识别 L(ℝ) 中 AD 的原句子；大基数层的
`LargeCardinal.RealDeterminacy.wd_lr_ad_l` 已在 ZFC 加真类 Woodin 前提下证明该句子。
相对层元素的有限实数参数及单序数码已构造；完整实数族下合并为一个二值实数。
lr_min_counterexample_l 从原 lr_ad 目标的否定取得 L(ℝ) 内唯一最小坏收益代码，
并为每个原查询实数生产四个实数参数的正负 Sr_truth_d 断言；声音性允许非传递见证。
规范代码方块、同一 Jensen 递归图及完整旧收益覆盖也已纳入同一 Δ₀ 矩阵。
非传递见证已由有限成员同余条件构造实际满坍塌，序数性与最小归纳性识别其背景 ω。
常零、后继实数的有限条件已接入工厂；规范化同时恢复完整自然数支撑并固定全部二值实数。
有限规范解码闭包已恢复值域的完整背景实数覆盖，并识别真实 Baire 空间；所选二值参数被固定。
有限局面、编号、偶数集合及种子的 Δ₀ 识别已接入；最小坏收益存在断言已完成 Σ₁(ℝ) 封装。
一般原坍缩派生模型无新实数已由 Model.Forcing.Applications.Collapse.ProductNoNewReals 证明。
la_reals_l 与 la_real_self_l 只要求并类上的准确实数刻画，派生模型的完整 Baire 空间及原种子已有实际实例。
带符号成员性由同一坍塌图及唯一解码准确恢复，两个断言对应同一最小坏收益。
PayoffModelMinimum 给出派生最小坏代码的精确原公式、代码序数性和唯一性。
具体统一力迫判定已由 Model.Forcing 的 ProductMinimumUniform 完成；双侧见证树仍待构造。
-/
