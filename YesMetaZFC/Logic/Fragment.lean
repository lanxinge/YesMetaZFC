import YesMetaZFC.Logic.Semantics

/-!
# 逻辑片段描述

这里不实现搜索器，只记录语义核允许哪些表达力。Automation 后续应按 fragment
选择可执行 checker，而不是把所有逻辑能力塞进 ATP 热路径。
-/

namespace YesMetaZFC
namespace Logic

/-- 二阶语义档位：Henkin 可进入自动化主线，full semantics 只作为语义层能力。 -/
inductive SecondOrderMode where
  | none
  | henkin
  | full
  deriving DecidableEq, Repr

/-- 自动化支持等级。`semanticOnly` 表示系统有语义但默认不承诺搜索。 -/
inductive AutomationSupport where
  | native
  | partialAuto
  | semanticOnly
  deriving DecidableEq, Repr

/-- 语义核 fragment 配置。 -/
structure Fragment where
  equality : Bool := true
  functionSymbols : Bool := true
  infinitaryConnectives : Bool := false
  infinitaryQuantifierBlocks : Bool := false
  secondOrder : SecondOrderMode := .none
  deriving Repr

namespace Fragment

/-- 只有隶属原子、没有函数符号和原生等词的纯集合论有限语言。 -/
def pureSetTheory : Fragment where
  equality := false
  functionSymbols := false
  infinitaryConnectives := false
  infinitaryQuantifierBlocks := false
  secondOrder := .none

/-- 纯集合论的 `L_{κ,κ}` 扩展；底层原子语言仍然只有隶属。 -/
def infinitaryPureSetTheory : Fragment where
  equality := false
  functionSymbols := false
  infinitaryConnectives := true
  infinitaryQuantifierBlocks := true
  secondOrder := .none

/-- 当前 ATP/DAG 首要迁移目标：有限一阶等词逻辑。 -/
def firstOrderEq : Fragment where
  equality := true
  functionSymbols := true
  infinitaryConnectives := false
  infinitaryQuantifierBlocks := false
  secondOrder := .none

/-- 后续 `L_{κ,κ}` 研究层的预留档位。 -/
def infinitaryFirstOrder : Fragment where
  equality := true
  functionSymbols := true
  infinitaryConnectives := true
  infinitaryQuantifierBlocks := true
  secondOrder := .none

/-- 二阶 Henkin 语义，适合后续做自动化友好的 replay 规则。 -/
def secondOrderHenkin : Fragment where
  equality := true
  functionSymbols := true
  infinitaryConnectives := false
  infinitaryQuantifierBlocks := false
  secondOrder := .henkin

/-- Full second-order semantics 进入系统，但默认不进入自动化搜索承诺。 -/
def secondOrderFull : Fragment where
  equality := true
  functionSymbols := true
  infinitaryConnectives := false
  infinitaryQuantifierBlocks := false
  secondOrder := .full

/-- 二阶默认档位：Henkin，供证书 replay 和部分自动化优先消费。 -/
def defaultSecondOrder : Fragment :=
  secondOrderHenkin

/-- 片段到自动化承诺的公开策略。 -/
def automationSupport (fragment : Fragment) : AutomationSupport :=
  match fragment.secondOrder with
  | .full => .semanticOnly
  | .henkin => .partialAuto
  | .none =>
      if fragment.infinitaryConnectives || fragment.infinitaryQuantifierBlocks then
        .partialAuto
      else
        .native

end Fragment

end Logic
end YesMetaZFC
