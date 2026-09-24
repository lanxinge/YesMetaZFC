import YesMetaZFC.Logic.Signature

/-! # Q 与 PA 共用的最小算术签名

只有自然数排序和零、后继、加法、乘法；等号使用逻辑等号。
不含配对、BMS 关系或任意宿主谓词。此处不预设任何模型或归纳公理。
-/
namespace YesMetaZFC.Logic.Arithmetic

/-- 算术语言的唯一排序。 -/
inductive sort_m where
  | num
  deriving DecidableEq

/-- Q 与 PA 的四个函数符号。 -/
inductive func_m where
  | zero | succ | add | mul
  deriving DecidableEq

abbrev signature_m : Signature where
  SortSymbol := sort_m
  FuncSymbol := func_m
  RelSymbol := Empty
  funcDomain
    | .zero => []
    | .succ => [.num]
    | .add | .mul => [.num, .num]
  funcCodomain _ := .num
  relDomain r := nomatch r

end YesMetaZFC.Logic.Arithmetic
