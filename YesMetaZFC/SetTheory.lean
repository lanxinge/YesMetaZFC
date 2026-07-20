import YesMetaZFC.SetTheory.Language
import YesMetaZFC.SetTheory.Theory
import YesMetaZFC.SetTheory.Definitional
import YesMetaZFC.SetTheory.FunctionSemantics
import YesMetaZFC.SetTheory.WellFounded
import YesMetaZFC.SetTheory.Ord
import YesMetaZFC.SetTheory.Card
import YesMetaZFC.SetTheory.Collection
import YesMetaZFC.SetTheory.Infinitary
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.SetTheory.Axioms.Common
import YesMetaZFC.SetTheory.Axioms.KP
import YesMetaZFC.SetTheory.Axioms.ZF
import YesMetaZFC.SetTheory.Axioms.ZFC
import YesMetaZFC.SetTheory.Extension
import YesMetaZFC.SetTheory.SetConstruction
import YesMetaZFC.SetTheory.Foundation
import YesMetaZFC.SetTheory.Automation.Context

/-!
# 项目集合论公共入口

本层以带定义原子的 Project 核作为唯一生产公式语言：

* 有限一阶项目语法固定在 `Type 0`；
* `x = y` 编译为带审计定义的外延等同原子；
* 一般隶属结构与外延结构显式区分；
* Jech 风格的类是公式/元层谓词，不是对象语言中的集合；
* `L_{κ,κ}` 扩展只提升无穷索引族，不改变底层原子语言。
* KP（含无穷）、ZF 与 ZFC 形成可传递的理论扩张层级；
* 有限公理切片可以直接进入 checked preprocessing、SearchDAG 与 `prove_auto`。

旧纯 `∈` AST 仅由 `SetTheory.Definitional.Audit` 显式导入，用于展开与双向保守性审计。
-/

namespace YesMetaZFC
namespace SetTheory

end SetTheory
end YesMetaZFC
