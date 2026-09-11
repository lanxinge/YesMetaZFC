import YesMetaZFC.Automation.RelationalTransfer

/-! # 已覆盖定义的扩张保持

证书同时记录覆盖范围增长与旧图保持。连续扩张只组合证书，不在每个最终规格处
重新展开整条解释链；函数规格的参数与原正文始终显式保留。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
universe x
variable {σ τ : Signature.{0,0,0}}

/-- 某组参数上的完整函数规格；不加入 guard，也不改变原正文。 -/
abbrev FunctionSpecification {I : Interpretation σ τ} {ℳ : Structure.{0,0,0,x} τ}
    (E : Expansion I ℳ) (symbol : σ.FuncSymbol)
    (spec : Formula σ [] (σ.funcCodomain symbol :: σ.funcDomain symbol))
    (args : Values E.model.Carrier (σ.funcDomain symbol))
    (output : E.model.Carrier (σ.funcCodomain symbol)) : Prop :=
  output = E.function symbol args ↔ spec.satisfies (templateEnv (.cons output args))

variable (I : Interpretation σ τ)
variable (functions : (symbol : σ.FuncSymbol) → Formula τ [] (I.sort (σ.funcCodomain symbol) :: (σ.funcDomain symbol).map I.sort))
variable (relations : (symbol : σ.RelSymbol) → Formula τ [] ((σ.relDomain symbol).map I.sort))

/-- 旧覆盖中的符号在新阶段仍被覆盖，且保留同一实际解释图。 -/
structure CoveredExtension (fc : σ.FuncSymbol → Bool) (rc : σ.RelSymbol → Bool)
    (nextFC : σ.FuncSymbol → Bool) (nextRC : σ.RelSymbol → Bool) : Prop where
  function : ∀ symbol, fc symbol = true → nextFC symbol = true ∧ functions symbol = I.function symbol
  relation : ∀ symbol, rc symbol = true → nextRC symbol = true ∧ relations symbol = I.relation symbol

variable {I functions relations}
variable {fc nextFC finalFC : σ.FuncSymbol → Bool} {rc nextRC finalRC : σ.RelSymbol → Bool}
variable {lastFunctions : (symbol : σ.FuncSymbol) → Formula τ [] (I.sort (σ.funcCodomain symbol) :: (σ.funcDomain symbol).map I.sort)}
variable {lastRelations : (symbol : σ.RelSymbol) → Formula τ [] ((σ.relDomain symbol).map I.sort)}

/-- 覆盖增长与实际图等式一起组合，避免把中间阶段暴露给规格调用者。 -/
theorem CoveredExtension.trans
    (first : CoveredExtension I functions relations fc rc nextFC nextRC)
    (second : CoveredExtension (regraph I functions relations) lastFunctions lastRelations nextFC nextRC finalFC finalRC) :
    CoveredExtension I lastFunctions lastRelations fc rc finalFC finalRC where
  function symbol h :=
    let hFirst := first.function symbol h
    let hSecond := second.function symbol hFirst.1
    ⟨hSecond.1, hSecond.2.trans hFirst.2⟩
  relation symbol h :=
    let hFirst := first.relation symbol h
    let hSecond := second.relation symbol hFirst.1
    ⟨hSecond.1, hSecond.2.trans hFirst.2⟩

/-- 对原覆盖中任意正文复用语法同余，保留所有参数与量词。 -/
theorem CoveredExtension.translation
    (h : CoveredExtension I functions relations fc rc nextFC nextRC)
    {free : SortContext σ} (body : Formula σ [] free) (hCovered : formulaCovered fc rc body = true) :
    openFormula (regraph I functions relations) body = openFormula I body :=
  openFormula_congr I functions relations fc rc
    (fun symbol hSymbol => (h.function symbol hSymbol).2)
    (fun symbol hSymbol => (h.relation symbol hSymbol).2) body hCovered

/-- 实现证书两端图的任意扩张都保持已覆盖正文。 -/
theorem CoveredExtension.transfer {ℳ : Structure.{0,0,0,x} τ}
    (h : CoveredExtension I functions relations fc rc nextFC nextRC)
    (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    {free : SortContext σ} (body : Formula σ [] free) (hCovered : formulaCovered fc rc body = true)
    (args : Values source.model.Carrier free) :
    body.satisfies (templateEnv args : Env source.model [] free) ↔
      body.satisfies (templateEnv args : Env target.model [] free) :=
  transfer_regraph I functions relations source hSource target hTarget body (h.translation body hCovered) args

/-- 函数图和原正文保持时，在原有全部假设下传输整项规格。 -/
theorem specification_regraph {ℳ : Structure.{0,0,0,x} τ}
    (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    (symbol : σ.FuncSymbol) (spec : Formula σ [] (σ.funcCodomain symbol :: σ.funcDomain symbol))
    (hGraph : functions symbol = I.function symbol)
    (hTranslate : openFormula (regraph I functions relations) spec = openFormula I spec)
    (args : Values source.model.Carrier (σ.funcDomain symbol)) (output : source.model.Carrier (σ.funcCodomain symbol))
    (hSpec : FunctionSpecification source symbol spec args output) :
    FunctionSpecification target symbol spec args output := by
  rw [FunctionSpecification, function_regraph I functions relations source hSource target hTarget symbol hGraph args]
  exact hSpec.trans (transfer_regraph I functions relations source hSource target hTarget spec hTranslate (.cons output args))

end YesMetaZFC.Automation.RelationalTranslation
