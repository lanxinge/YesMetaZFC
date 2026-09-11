import YesMetaZFC.Model.Interpretation.RelationalEnvironment

/-! # 部分定义图的规范总化

原图有输出时精确保留其输出；没有输出时使用另一个已证明总且单值的图。
存在唯一性与合法输入上的保真性分开陈述，不声称原理论已规定缺省分支。
-/
namespace YesMetaZFC.Automation.TotalizedGraph
open Logic Logic.FirstOrder
set_option autoImplicit false
universe x
variable {σ : Signature.{0, 0, 0}} {bound free : SortContext σ} {sort : σ.SortSymbol}

def formula (body fallback : Formula σ bound (sort :: free)) : Formula σ bound (sort :: free) :=
  .disj body (.conj ((Formula.neg (body.existsFreeTop sort)).weakenFree sort) fallback)

theorem satisfies {ℳ : Structure.{0, 0, 0, x} σ} (env : Env ℳ bound free)
    (body fallback : Formula σ bound (sort :: free)) (output : ℳ.Carrier sort) :
    (formula body fallback).satisfies (env.pushFree output) ↔
      body.satisfies (env.pushFree output) ∨
        ((¬ ∃ value, body.satisfies (env.pushFree value)) ∧ fallback.satisfies (env.pushFree output)) := by
  simp only [formula, Formula.satisfies, Formula.satisfies_weakenFree, Formula.satisfies_existsFreeTop]

/-- 有原始输出的参数上，总化图与原图逐输出等价。 -/
theorem agrees {ℳ : Structure.{0, 0, 0, x} σ} (env : Env ℳ bound free)
    (body fallback : Formula σ bound (sort :: free))
    (hExists : ∃ value, body.satisfies (env.pushFree value)) (output : ℳ.Carrier sort) :
    (formula body fallback).satisfies (env.pushFree output) ↔ body.satisfies (env.pushFree output) := by
  rw [satisfies]
  exact ⟨fun h => h.elim id (fun h => False.elim (h.1 hExists)), Or.inl⟩

/-- 原图无输出的参数上，总化图精确使用缺省图。 -/
theorem fallback_of_absent {ℳ : Structure.{0, 0, 0, x} σ} (env : Env ℳ bound free)
    (body fallback : Formula σ bound (sort :: free))
    (hAbsent : ¬ ∃ value, body.satisfies (env.pushFree value)) (output : ℳ.Carrier sort) :
    (formula body fallback).satisfies (env.pushFree output) ↔ fallback.satisfies (env.pushFree output) := by
  rw [satisfies]
  exact ⟨fun h => h.elim (fun h => False.elim (hAbsent ⟨output, h⟩)) And.right,
    fun h => Or.inr ⟨hAbsent, h⟩⟩

/-- 单值部分图加总且单值缺省图，得到任意参数下的唯一输出。 -/
theorem functional {ℳ : Structure.{0, 0, 0, x} σ} (env : Env ℳ bound free)
    (body fallback : Formula σ bound (sort :: free))
    (hUnique : ∀ left right, body.satisfies (env.pushFree left) →
      body.satisfies (env.pushFree right) → left = right)
    (hFallback : ∃ output, fallback.satisfies (env.pushFree output) ∧
      ∀ other, fallback.satisfies (env.pushFree other) → other = output) :
    ∃ output, (formula body fallback).satisfies (env.pushFree output) ∧
      ∀ other, (formula body fallback).satisfies (env.pushFree other) → other = output := by
  classical
  by_cases hExists : ∃ value, body.satisfies (env.pushFree value)
  · obtain ⟨output, hOutput⟩ := hExists
    have hAgrees := agrees env body fallback ⟨output, hOutput⟩
    exact ⟨output, (hAgrees output).mpr hOutput,
      fun other hOther => hUnique other output ((hAgrees other).mp hOther) hOutput⟩
  · obtain ⟨output, hOutput, hOnly⟩ := hFallback
    have hAgrees := fallback_of_absent env body fallback hExists
    exact ⟨output, (hAgrees output).mpr hOutput,
      fun other hOther => hOnly other ((hAgrees other).mp hOther)⟩

end YesMetaZFC.Automation.TotalizedGraph
