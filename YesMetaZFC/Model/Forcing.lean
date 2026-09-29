import YesMetaZFC.Model.Forcing.Separative
import YesMetaZFC.Model.Forcing.Boolean
import YesMetaZFC.Model.Forcing.Tree
import YesMetaZFC.Model.Forcing.CohenTheory
import YesMetaZFC.Model.Forcing.InternalCohen
import YesMetaZFC.Model.Forcing.InternalCheckModel
import YesMetaZFC.Model.Forcing.InternalCheckRealization

/-! # 力迫偏序、名称求值与相对扩张入口

预序、相容性、稠密映射、分离商、正则开完备化及其规范条件映射，
布尔名称的图求值、完整一阶真值、可数族泛型滤子及相对名称域的实际解释扩张。
Cohen 实例同时满足全部公式真值、指定稠密要求和旧实数规避要求。
已核验四条原 ZFC 基础公理；内部地模型与其余公理保持的边界见模块文档。
内部名称的一阶定义、支撑收集、小图解码、编码往返及 Cohen 内部实例见 Internal 各模块。
内部规范名称递归由 zf_check_l 一次取得；解释还原由 zf_check_val_l 给出。
文献选择、顺序方向、调用方式和尚未实现的语义范围见 `Forcing/README.md`。
-/
