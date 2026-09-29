import YesMetaZFC.Model.Forcing.Separative
import YesMetaZFC.Model.Forcing.Boolean
import YesMetaZFC.Model.Forcing.Tree
import YesMetaZFC.Model.Forcing.CohenTheory
import YesMetaZFC.Model.Forcing.InternalCohen
import YesMetaZFC.Model.Forcing.InternalCheckModel
import YesMetaZFC.Model.Forcing.InternalCheckRealization
import YesMetaZFC.Model.Forcing.InternalAtomicTruth
import YesMetaZFC.Model.Forcing.InternalChoice
import YesMetaZFC.Model.Forcing.InternalGenericInstance
import YesMetaZFC.Model.Forcing.CH
import YesMetaZFC.Model.Forcing.CHIndependence

/-! # 力迫偏序、名称求值与相对扩张入口

预序、相容性、稠密映射、分离商、正则开完备化及其规范条件映射，
布尔名称的图求值、完整一阶真值、可数族泛型滤子及相对名称域的实际解释扩张。
Cohen 实例同时满足全部公式真值、指定稠密要求和旧实数规避要求。
内部名称泛型商的完整原公式真值和原 ZFC 全部公理及模式由实际内部构造证明，
适用于外部非良基、内部 ω 非标准的任意地模型；商载体保持地模型的 universe。
preserves_zfc_l 一次取得全部保持性，two_extension_zfc_l 给出可直接调用的实际实例。
ch_extension_l 自动构造可数地模型的 CH 塌缩扩张；ch_model_l 给出实际 ZFC＋CH 模型存在。
cohen_extension_l 以地模型指标集 κ 参数化添加量，自动构造互异新实数族并保持旧无限基数。
not_ch_extension_l 自动添加 ω₂ 个 Cohen 实数；ch_independent_l 在原 Derives 核中给出 CH 双侧不可证。
内部名称的一阶定义、支撑收集、小图解码、编码往返及 Cohen 内部实例见 Internal 各模块。
内部规范名称递归由 zf_check_l 一次取得；解释还原由 zf_check_val_l 给出。
文献选择、顺序方向、调用方式和尚未实现的语义范围见 `Forcing/README.md`。
-/
