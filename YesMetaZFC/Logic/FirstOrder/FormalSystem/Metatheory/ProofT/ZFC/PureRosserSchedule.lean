import YesMetaZFC.Model.Henkin.SyntaxNatCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.SyntaxCoding
import YesMetaZFC.SetTheory.Language

/-! # Rosser 回传使用的两套固定公平调度

源签名沿用既有函数、关系符号的单射编号；纯签名只有一个排序、一个关系，没有
函数。Henkin 常量和闭句的编码及公平性统一由通用语法编码层提供。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosserSchedule
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation.SyntaxNatCoding
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature

def sourceSymbols : SymbolCoding signature where
  sort := ⟨fun _ => 0, by intro left right _; cases left; cases right; rfl⟩
  function := ⟨QuineEncoding.SyntaxCoding.function_symbol_code,
    QuineEncoding.SyntaxCoding.function_symbol_code_injective⟩
  relation := ⟨QuineEncoding.SyntaxCoding.relation_symbol_code,
    QuineEncoding.SyntaxCoding.relation_symbol_code_injective⟩

def targetSymbols : SymbolCoding ℒ where
  sort := ⟨fun _ => 0, by intro left right _; cases left; cases right; rfl⟩
  function := {
    encode := fun symbol => nomatch symbol
    injective := by intro symbol; cases symbol }
  relation := ⟨fun _ => 0, by intro left right _; cases left; cases right; rfl⟩

/-- 原支撑语言的闭句在任意阶段之后再次出现。 -/
noncomputable def source : Completeness.Henkin.Schedule signature := schedule sourceSymbols

/-- 裸 ZFC 纯隶属语言的固定公平调度。 -/
noncomputable def target : Completeness.Henkin.Schedule ℒ := schedule targetSymbols

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosserSchedule
