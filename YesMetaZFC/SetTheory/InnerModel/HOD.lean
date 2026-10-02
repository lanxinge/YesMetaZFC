import YesMetaZFC.SetTheory.InnerModel.HOD.Choice
import YesMetaZFC.SetTheory.InnerModel.HOD.Parameters
import YesMetaZFC.SetTheory.InnerModel.HOD.Presentation

/-! # HOD 及两种参数版本

遗传 OD 等价于 TC({x}) 的全部元素属于 OD。它包含全部内部序数且为传递类。
背景仅需 ZF，即可在实际 hod_model_l 中验证原选择集公理。完整模型入口采用
参数结构 hb_model_l；序数参数下已证明 HOD[A]=HOD，尚未归并两种模型接口。
背景 OD 良序与 HOD 内部重算的良序之间的绝对性未在此断言。
参数版本已统一验证全分离、全收集和内部幂集：HOD[A] 满足 ZFC，HOD(A) 满足 ZF。
圆括号允许内部有限 A 参数列；当 A 传递时，A 及其成员属于 HOD(A)。
HOD[A] 对象有 OD[A] 的有界序数关系呈现，其解码满射为实际坍塌图；背景仍只需 ZF。
-/
