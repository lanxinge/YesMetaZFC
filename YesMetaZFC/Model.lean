import YesMetaZFC.Model.FirstOrder
import YesMetaZFC.Model.HigherOrder
import YesMetaZFC.Model.Infinitary
import YesMetaZFC.Model.SecondOrder.Full
import YesMetaZFC.Model.Semantics
import YesMetaZFC.Model.Boolean.Native

/-! # 通用模型论入口

相对语义底座、原生及布尔值语义、普通映射及可选的高阶、二阶解释。
特定集合论模型、关系消去和已有 Henkin 结果按各自子目录显式导入。
这些语义定义不向任意一阶结构附加二阶封闭或外部良基性要求。
-/
