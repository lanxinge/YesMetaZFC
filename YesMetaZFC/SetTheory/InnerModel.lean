import YesMetaZFC.SetTheory.InnerModel.Jensen.ZF.Model
import YesMetaZFC.SetTheory.InnerModel.Computation.Readback
import YesMetaZFC.SetTheory.InnerModel.Computation.Library
import YesMetaZFC.SetTheory.InnerModel.ProofCode
import YesMetaZFC.SetTheory.InnerModel.Order.Sigma1
import YesMetaZFC.SetTheory.InnerModel.Jensen.Definable

/-! # 内模型技术的共同基础

提供 KP 的 rudimentary 有限基、KPi 的内部 Σ₁ 成员递归、最小闭包及 J 层级。
J 自身满足 KPi，内部层级与背景层级一致，并满足原演绎核的 KP + V=L。
在 ZF 背景中，同一 J 结构满足 ZF + V=L；全分离、全收集和内部幂集均已验证。
独立集合程序具有 KP 总性、Δ₁ 图、Δ₀ 判定与 Σ₁ 见证验证编译，并提供 C 风格前端。
J 搜索在 KPi + V=L 中实现互补 Σ₁ 正规形与总布尔计算的双向等价。
J 构造推导码具有内部语法检查、Σ₁ 求值及覆盖性；精确码初段和唯一最小代表
产生 L 上无参数 Σ₁ 全局良序及初段函数。良序在 L 上为 Δ₁，与 J 内部解释绝对。
Jensen 逐层良序的一步构造已有实际 Σ₁ 图及端延拓；整层的统一局部定义尚待证明。
-/
