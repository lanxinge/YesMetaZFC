/-!
# 通用逻辑签名

这一层只描述对象语言的符号表，不携带任何 MF1 章节语义。
后续自动化、无穷语言和二阶扩展都应通过这里的签名接口进入。
-/

namespace YesMetaZFC
namespace Logic

universe u v w

/-- 多 sorted 一阶签名：函数和关系的 arity 都由 sort 列表给出。 -/
structure Signature where
  SortSymbol : Type u
  FuncSymbol : Type v
  RelSymbol : Type w
  funcDomain : FuncSymbol → List SortSymbol
  funcCodomain : FuncSymbol → SortSymbol
  relDomain : RelSymbol → List SortSymbol

namespace Signature

/-- 函数字符的元数。 -/
def funcArity (σ : Signature) (f : σ.FuncSymbol) : Nat :=
  (σ.funcDomain f).length

/-- 关系字符的元数。 -/
def relArity (σ : Signature) (r : σ.RelSymbol) : Nat :=
  (σ.relDomain r).length

end Signature

end Logic
end YesMetaZFC
