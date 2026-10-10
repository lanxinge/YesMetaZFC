import YesMetaZFC.Logic.Syntax
/-!
# 集合论语法的共享绑定底座
本模块只保存新旧集合论语法共同使用的 locally nameless 变量编号与 bound-variable
嵌入，不定义任何公式 AST。
-/
namespace YesMetaZFC
namespace SetTheory
/-- 自然数后继非零的直接证书，供有限下标字面量使用。 -/
instance (priority := 1100) nat_succ_nezero {n : Nat} : NeZero (n+1) :=
  ⟨fun h => Nat.noConfusion h⟩

/-- 有限下标按底层自然数直接消去；不调用经逻辑重写构造的归纳器。 -/
@[elab_as_elim] def fin_cases {n : Nat} {p : Fin (n+1) → Sort _}
    (z : p 0) (s : ∀ i : Fin n, p i.succ) : ∀ i : Fin (n+1), p i
  | ⟨0, _⟩ => z
  | ⟨k+1, h⟩ => s ⟨k, Nat.lt_of_succ_lt_succ h⟩

@[simp] theorem fin_cases_zero {n : Nat} {p : Fin (n+1) → Sort _}
    (z : p 0) (s : ∀ i : Fin n, p i.succ) : @fin_cases n p z s 0 = z := rfl

@[simp] theorem fin_cases_mk_succ {n : Nat} {p : Fin (n+1) → Sort _}
    (z : p 0) (s : ∀ i : Fin n, p i.succ) (k : Nat) (h : k+1 < n+1) :
    @fin_cases n p z s ⟨k+1, h⟩ = s ⟨k, Nat.lt_of_succ_lt_succ h⟩ := rfl

@[simp] theorem fin_cases_succ {n : Nat} {p : Fin (n+1) → Sort _}
    (z : p 0) (s : ∀ i : Fin n, p i.succ) (i : Fin n) :
    @fin_cases n p z s i.succ = s i := rfl
/-- 集合论公式中的稳定自由变量编号。 -/
abbrev FreeVarId := Nat
namespace BoundEmbedding
/-- 在已有 bound-variable 嵌入外侧保留一个最新 binder。 -/
def lift {sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) :
    Fin (sourceDepth + 1) → Fin (targetDepth + 1) :=
  fin_cases 0 fun entry => Fin.succ (indexMap entry)
/-- 在一元模式的主变量之后插入一个局部 binder。 -/
def unaryUnderOne {parameterCount : Nat} :
    Fin (parameterCount + 1) → Fin (parameterCount + 2) :=
  fin_cases 0 fun parameter => parameter.succ.succ
/-- 在最新变量之后插入两个局部 binder。 -/
def unaryUnderTwo {parameterCount : Nat} :
    Fin (parameterCount + 1) → Fin (parameterCount + 3) :=
  fin_cases 0 fun parameter => parameter.succ.succ.succ
/-- 在二元模式的两个主变量之后插入一个局部 binder。 -/
def binaryUnderOne {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 3) :=
  fin_cases 0 <| fin_cases 1 fun parameter => parameter.succ.succ.succ
/-- 在二元模式的两个主变量之后插入两个局部 binder。 -/
def binaryUnderTwo {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 4) :=
  fin_cases 0 <| fin_cases 1 fun parameter => parameter.succ.succ.succ.succ
end BoundEmbedding
end SetTheory
end YesMetaZFC
