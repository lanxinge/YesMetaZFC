import YesMetaZFC.Automation.RelationalCongruence

/-! # 已覆盖原公式在模型扩张之间的传输

两份实际解释只须在该正文使用的符号上相同。证明通过纯翻译的语法同余，
不展开选择所得的函数值或递归关系图。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
universe x
variable {σ τ : Signature.{0,0,0}}
variable (I : Interpretation σ τ)
variable (functions : (symbol : σ.FuncSymbol) → Formula τ [] (I.sort (σ.funcCodomain symbol) :: (σ.funcDomain symbol).map I.sort))
variable (relations : (symbol : σ.RelSymbol) → Formula τ [] ((σ.relDomain symbol).map I.sort))
variable {ℳ : Structure.{0,0,0,x} τ}

theorem regraph_mapValues {sorts : SortContext σ}
    (args : Values (fun sort => ℳ.Carrier (I.sort sort)) sorts) :
    mapValues (regraph I functions relations) args = mapValues I args := rfl

/-- 相同实际图的函数值由其实现唯一性保持。 -/
theorem function_regraph (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    (symbol : σ.FuncSymbol) (hGraph : functions symbol = I.function symbol)
    (args : Values source.model.Carrier (σ.funcDomain symbol)) :
    target.function symbol args = source.function symbol args := by
  have hNew := (hTarget.function symbol args _).mpr rfl
  change (functions symbol).satisfies
    (templateEnv (.cons (target.function symbol args) (mapValues (regraph I functions relations) args))) at hNew
  rw [hGraph, regraph_mapValues] at hNew
  exact (hSource.function symbol args _).mp hNew

/-- 任意开放正文的纯翻译相同即可直接跨阶段传输，无须逐层比较模型。 -/
theorem transfer_regraph (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    {free : SortContext σ} (body : Formula σ [] free)
    (hTranslate : openFormula (regraph I functions relations) body = openFormula I body)
    (args : Values source.model.Carrier free) :
    body.satisfies (templateEnv args : Env source.model [] free) ↔
      body.satisfies (templateEnv args : Env target.model [] free) := by
  have hNew := openFormula_correct target hTarget body args
  rw [hTranslate] at hNew
  exact (openFormula_correct source hSource body args).symm.trans hNew

/-- 相同实际关系图的实现直接保持；参数映射已在定义上与扩张层数无关。 -/
theorem relation_regraph (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    (symbol : σ.RelSymbol) (hGraph : relations symbol = I.relation symbol)
    (args : Values source.model.Carrier (σ.relDomain symbol)) :
    target.relation symbol args ↔ source.relation symbol args := by
  have hNew := (hTarget.relation symbol args).symm
  change target.relation symbol args ↔ (relations symbol).satisfies (templateEnv (mapValues I args)) at hNew
  rw [hGraph] at hNew
  exact hNew.trans (hSource.relation symbol args)

theorem transfer_covered (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    (fc : σ.FuncSymbol → Bool) (rc : σ.RelSymbol → Bool)
    (hFunctions : ∀ symbol, fc symbol = true → functions symbol = I.function symbol)
    (hRelations : ∀ symbol, rc symbol = true → relations symbol = I.relation symbol)
    {free : SortContext σ} (body : Formula σ [] free)
    (hCovered : formulaCovered fc rc body = true) (args : Values source.model.Carrier free) :
    body.satisfies (templateEnv args : Env source.model [] free) ↔
      body.satisfies (templateEnv args : Env target.model [] free) := by
  exact transfer_regraph I functions relations source hSource target hTarget body
    (openFormula_congr I functions relations fc rc hFunctions hRelations body hCovered) args

end YesMetaZFC.Automation.RelationalTranslation
