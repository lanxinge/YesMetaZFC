import YesMetaZFC.Logic.Signature
import YesMetaZFC.Logic.Syntax
import YesMetaZFC.Logic.Semantics
import YesMetaZFC.Logic.FreeVariableSupport
import YesMetaZFC.Logic.Theory
import YesMetaZFC.Logic.HigherOrder
import YesMetaZFC.Logic.Infinitary
import YesMetaZFC.Logic.SecondOrder
import YesMetaZFC.Logic.Fragment
import YesMetaZFC.Logic.Shallow
import YesMetaZFC.Logic.FirstOrder
import YesMetaZFC.Logic.Notation

/-!
# YesMetaZFC 新语义核

这一层是后 MF1 阶段的对象逻辑入口：

* `Logic.Signature`：多 sorted 函数/关系签名；
* `Logic.Syntax`：sorted locally nameless 原始语法、well-formed/well-scoped 关系和 open/close 操作；
* `Logic.Semantics`：单域多 sorted Tarski 结构与满足关系；
* `Logic.FreeVariableSupport`：自由变量支持、环境一致性和有限环境合并；
* `Logic.Theory`：语义理论、模型满足和语义蕴涵；
* `Logic.HigherOrder`：原生 `apply/lam`、简单类型检查与高阶语义合同；
* `Logic.Infinitary`：`L_{κ,κ}` 风格小索引族合取/析取和量词块；
* `Logic.SecondOrder`：Henkin / Full 二阶语义，Henkin 作为默认自动化档位；
* `Logic.Fragment`：有限一阶、`L_{κ,κ}` 和二阶语义档位的长期接口。
* `Logic.Shallow`：浅嵌入到深嵌入的机械 proof-carrying 桥接层。
* `Logic.Notation`：原始 LN 记号与具名数学 DSL 的双层入口。
-/

namespace YesMetaZFC
namespace Logic

end Logic
end YesMetaZFC
