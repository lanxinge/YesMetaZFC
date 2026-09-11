import YesMetaZFC.Model.Interpretation.RelationalEnvironment
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-! # 开放模型规格的全称闭包

把任意环境上的规格组装为原全称闭句，并在值列与环境之间保持精确对应。
-/
namespace YesMetaZFC.Automation.ModelClosure
open Logic Logic.FirstOrder RelationalTranslation
set_option autoImplicit false
universe x
variable {σ : Signature.{0,0,0}} {ℳ : Structure.{0,0,0,x} σ}

/-- 按排序列表逐个接收参数，避免每个闭句重新拆解异质值列。 -/
def Curried : (free : SortContext σ) → (Values ℳ.Carrier free → Prop) → Prop
  | .nil, body => body .nil
  | .cons _ rest, body => ∀ value, Curried rest (fun args => body (.cons value args))

theorem Curried.apply {free : SortContext σ} {body : Values ℳ.Carrier free → Prop}
    (h : Curried free body) (args : Values ℳ.Carrier free) : body args := by
  induction args with
  | nil => exact h
  | cons value args ih => exact ih (h value)

theorem all_environments {free : SortContext σ} (body : Formula σ [] free) :
    (∀ args, body.satisfies (templateEnv args : Env ℳ [] free)) ↔
      ∀ env : Env ℳ [] free, body.satisfies env := by
  constructor
  · intro h env
    have hBody := h (valuesOfAssignment env.freeVal)
    rwa [template_of_env] at hBody
  · intro h args; exact h _

/-- 全称闭包的语义不依赖外部自由变量编号或标准性。 -/
theorem forall_close_iff {free : SortContext σ} (body : Formula σ [] free) :
    (Metatheory.Formula.forall_close body).satisfies (Env.empty : Env ℳ [] []) ↔
      ∀ env : Env ℳ [] free, body.satisfies env := by
  induction free with
  | nil =>
    constructor
    · intro h env
      have hEnv : env = Env.empty := by
        apply Env.ext <;> intro sort entry <;> cases entry
      simpa only [hEnv, Metatheory.Formula.forall_close] using h
    · intro h; exact h Env.empty
  | cons sort free ih =>
    rw [Metatheory.Formula.forall_close_cons, ih]
    constructor
    · intro h env
      let rest : Env ℳ [] free :=
        ⟨env.boundVal, fun entry => env.freeVal (.there entry)⟩
      have hEnv : rest.pushFree (env.freeVal .here) = env := by
        apply Env.ext
        · intro sort entry; cases entry
        · intro sort entry; cases entry <;> rfl
      have hBody := (Formula.satisfies_forallFreeTop rest body).mp (h rest) (env.freeVal .here)
      rwa [hEnv] at hBody
    · intro h env
      exact (Formula.satisfies_forallFreeTop env body).mpr (fun value => h (env.pushFree value))

theorem close_of_values {free : SortContext σ} (body : Formula σ [] free)
    (hBody : ∀ args, body.satisfies (templateEnv args : Env ℳ [] free)) :
    (Metatheory.Formula.forall_close body).satisfies (Env.empty : Env ℳ [] []) :=
  (forall_close_iff body).mpr ((all_environments body).mp hBody)

theorem close_of_curried {free : SortContext σ} (body : Formula σ [] free)
    (hBody : Curried free (fun args => body.satisfies (templateEnv args : Env ℳ [] free))) :
    (Metatheory.Formula.forall_close body).satisfies (Env.empty : Env ℳ [] []) :=
  close_of_values body hBody.apply

end YesMetaZFC.Automation.ModelClosure
