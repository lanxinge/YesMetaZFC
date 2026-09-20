import YesMetaZFC.Logic.Arithmetic.Syntax
import YesMetaZFC.Model.FirstOrder.Semantics

/-! # 任意算术结构的数域操作

结构不必满足 Q 或 PA，数域也不必是标准自然数。运算与模型公理分开提供。
-/
namespace YesMetaZFC.Model.Arithmetic
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

abbrev num_l (ℳ : Structure.{0, 0, 0, u} signature_m) := ℳ.Carrier sort_m.num

def zero_l (ℳ : Structure.{0, 0, 0, u} signature_m) : num_l ℳ :=
  ℳ.funcInterp .zero .nil

def succ_l {ℳ : Structure.{0, 0, 0, u} signature_m} (n : num_l ℳ) : num_l ℳ :=
  ℳ.funcInterp .succ (.cons n .nil)

def add_l {ℳ : Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : num_l ℳ :=
  ℳ.funcInterp .add (.cons m (.cons n .nil))

def mul_l {ℳ : Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : num_l ℳ :=
  ℳ.funcInterp .mul (.cons m (.cons n .nil))

end YesMetaZFC.Model.Arithmetic
