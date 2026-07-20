import YesMetaZFC.Logic
import YesMetaZFC.SetTheory
import YesMetaZFC.Automation

/-!
`YesMetaZFC.Basic` 是项目当前的公共入口。

旧 `MF1` 层已经从公共入口移除；新主入口暴露 `YesMetaZFC.Logic` 语义核，以及
只有隶属原子的 `YesMetaZFC.SetTheory` 纯集合语言和已经按新语义核重建的
`YesMetaZFC.Automation` 稳定边界。

当前自动化入口先导出搜索数据结构、命题残差检查和新 soundness 合同；`prove_auto`
tactic 请求层后续应直接消费这套新合同，而不是桥回旧 soundness。
-/

namespace YesMetaZFC

end YesMetaZFC
