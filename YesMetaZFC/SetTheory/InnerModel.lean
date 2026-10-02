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
-/
