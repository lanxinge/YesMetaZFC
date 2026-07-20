import YesMetaZFC.Automation.LogicSoundness

/-!
# 深嵌入语法构造层

这里不再维护旧 MF1 的一阶语法 typeclass，而是直接围绕 `Logic.FirstOrder`
的深嵌入项/公式/理论对象提供轻量构造器。自动化后端和 tactic 层都应优先使用
这些深嵌入构造，而不是先走浅嵌入门户再反射回去。

Lean 的 parser 语法可以后续再补；当前先把可编程构造接口收拢到这里。
-/

namespace YesMetaZFC
namespace Automation
namespace DeepSyntax

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder
open _root_.YesMetaZFC.Automation.LogicSoundness

/-- 深嵌入项的显式变量构造。 -/
def bvar {σ : SetLevel.Signature} (sort : σ.SortSymbol) (idx : Nat) : SetLevel.Term σ :=
  .var (.bvar sort idx)

/-- 深嵌入项的自由变量构造。 -/
def fvar {σ : SetLevel.Signature} (sort : σ.SortSymbol) (id : FreeVarId) : SetLevel.Term σ :=
  .var (.fvar sort id)

/-- 深嵌入项的函数应用构造。 -/
def app {σ : SetLevel.Signature} (f : σ.FuncSymbol) (args : List (SetLevel.Term σ)) :
    SetLevel.Term σ :=
  .app f args

/-- 深嵌入公式的关系原子构造。 -/
def rel {σ : SetLevel.Signature} (r : σ.RelSymbol) (args : List (SetLevel.Term σ)) :
    SetLevel.Formula σ :=
  .rel r args

/-- 深嵌入公式的等词构造。 -/
def equal {σ : SetLevel.Signature} (left right : SetLevel.Term σ) :
    SetLevel.Formula σ :=
  .equal left right

/-- 深嵌入公式的联结词构造。 -/
def falsum {σ : SetLevel.Signature} : SetLevel.Formula σ := .falsum
def truth {σ : SetLevel.Signature} : SetLevel.Formula σ := .truth
def neg {σ : SetLevel.Signature} (φ : SetLevel.Formula σ) : SetLevel.Formula σ := .neg φ
def conj {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .conj φ ψ
def disj {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .disj φ ψ
def imp {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .imp φ ψ
def iff {σ : SetLevel.Signature} (φ ψ : SetLevel.Formula σ) : SetLevel.Formula σ := .iff φ ψ
def forallE {σ : SetLevel.Signature} (sort : σ.SortSymbol) (body : SetLevel.Formula σ) :
    SetLevel.Formula σ :=
  .forallE sort body
def existsE {σ : SetLevel.Signature} (sort : σ.SortSymbol) (body : SetLevel.Formula σ) :
    SetLevel.Formula σ :=
  .existsE sort body

/-- 直接构造深嵌入问题。 -/
def problem {σ : SetLevel.Signature} (premises : List (SetLevel.Formula σ))
    (target : SetLevel.Formula σ) : SetLevel.DeepProblem σ where
  premises := premises
  target := target

/-- 构造空理论 checked 证书对象。 -/
def valid {σ : SetLevel.Signature} [DecidableEq σ.SortSymbol]
    (target : SetLevel.Formula σ)
    (cert : SetLevel.SemanticCertificate SetLevel.Theory.empty target) :
    SetLevel.CheckedValidCertificate (σ := σ) where
  target := target
  cert := cert

/-- 构造一般 checked 证书对象。 -/
def checked {σ : SetLevel.Signature} [DecidableEq σ.SortSymbol]
    (problem : SetLevel.DeepProblem σ)
    (cert : SetLevel.DeepProblem.Certificate problem) :
    SetLevel.CheckedCertificate (σ := σ) where
  problem := problem
  cert := cert

end DeepSyntax
end Automation
end YesMetaZFC
