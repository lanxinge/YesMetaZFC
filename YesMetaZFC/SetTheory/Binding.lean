import YesMetaZFC.Logic.Syntax

/-!
# 集合论语法的共享绑定底座

本模块只保存新旧集合论语法共同使用的 locally nameless 变量编号与 bound-variable
嵌入，不定义任何公式 AST。
-/

namespace YesMetaZFC
namespace SetTheory

/-- 集合论公式中的稳定自由变量编号。 -/
abbrev FreeVarId := Nat

namespace BoundEmbedding

/-- 在已有 bound-variable 嵌入外侧保留一个最新 binder。 -/
def lift {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    Fin (sourceDepth + 1) → Fin (targetDepth + 1) :=
  Fin.cases 0 fun entry => Fin.succ (indexMap entry)

/-- 在一元模式的主变量之后插入一个局部 binder。 -/
def unaryUnderOne {parameterCount : Nat} :
    Fin (parameterCount + 1) → Fin (parameterCount + 2) :=
  Fin.cases 0 fun parameter =>
    ⟨parameter.val + 2, by omega⟩

/-- 在最新变量之后插入两个局部 binder。 -/
def unaryUnderTwo {parameterCount : Nat} :
    Fin (parameterCount + 1) → Fin (parameterCount + 3) :=
  Fin.cases 0 fun parameter =>
    ⟨parameter.val + 3, by omega⟩

/-- 在二元模式的两个主变量之后插入一个局部 binder。 -/
def binaryUnderOne {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 3) :=
  Fin.cases 0 <| Fin.cases 1 fun parameter =>
    ⟨parameter.val + 3, by omega⟩

/-- 在二元模式的两个主变量之后插入两个局部 binder。 -/
def binaryUnderTwo {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 4) :=
  Fin.cases 0 <| Fin.cases 1 fun parameter =>
    ⟨parameter.val + 4, by omega⟩

end BoundEmbedding

end SetTheory
end YesMetaZFC
