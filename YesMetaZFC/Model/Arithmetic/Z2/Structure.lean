import YesMetaZFC.Logic.Arithmetic.Z2.Syntax
import YesMetaZFC.Model.FirstOrder.Semantics

/-! # 任意双排序算术结构

数集载体及成员关系来自给定结构，不预设外部幂集、标准性或良基性。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
universe u

abbrev num_l (ℳ : Structure.{0, 0, 0, u} signature_m) := ℳ.Carrier sort_m.num

abbrev set_l (ℳ : Structure.{0, 0, 0, u} signature_m) := ℳ.Carrier sort_m.set

def zero_l (ℳ : Structure.{0, 0, 0, u} signature_m) : num_l ℳ :=
  ℳ.funcInterp .zero .nil

def succ_l {ℳ : Structure.{0, 0, 0, u} signature_m} (n : num_l ℳ) : num_l ℳ :=
  ℳ.funcInterp .succ (.cons n .nil)

def mem_l {ℳ : Structure.{0, 0, 0, u} signature_m} (n : num_l ℳ) (X : set_l ℳ) : Prop :=
  ℳ.relInterp .mem (.cons n (.cons X .nil))

end YesMetaZFC.Model.Arithmetic.Z2
