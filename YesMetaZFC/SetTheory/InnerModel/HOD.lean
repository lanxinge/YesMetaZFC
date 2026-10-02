import YesMetaZFC.SetTheory.InnerModel.HOD.Choice
import YesMetaZFC.SetTheory.InnerModel.HOD.Parameters

/-! # HOD 及两种参数版本

遗传 OD 等价于 TC({x}) 的全部元素属于 OD。它包含全部内部序数且为传递类。
背景仅需 ZF，即可在实际 HOD 隶属结构中验证原选择集公理；本入口暂未提供
该结构的全套 ZF 模型性，也不把背景 OD 良序等同于 HOD 内部重算的良序。
参数版本已统一验证全分离、全收集和内部幂集：HOD[A] 满足 ZFC，HOD(A) 满足 ZF。
圆括号允许内部有限 A 参数列；当 A 传递时，A 及其成员属于 HOD(A)。
-/
