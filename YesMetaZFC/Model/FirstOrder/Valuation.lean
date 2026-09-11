import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 有限值列与类型化环境

从原关系解释层迁入的实际定义，现对任意签名 universe 可用。
值列与赋值互逆，不选择任何模型对象；原消费者直接使用这些定义。
-/

namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
universe u v w x

/-- 异质值列读取成自由变量赋值。 -/
def valuesAssignment {τ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} τ}
    {sorts : SortContext τ} (values : Values M.Carrier sorts) : Assignment M sorts :=
  fun entry => match values, entry with
    | .cons head _, .here => head
    | .cons _ tail, .there previous => valuesAssignment tail previous

/-- 从指定值列构造无绑定变量的环境。 -/
def templateEnv {τ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} τ}
    {sorts : SortContext τ} (values : Values M.Carrier sorts) : Env M [] sorts where
  boundVal := Assignment.empty
  freeVal := valuesAssignment values

end YesMetaZFC.Automation.RelationalTranslation

namespace YesMetaZFC.Automation.ModelClosure
open Logic Logic.FirstOrder RelationalTranslation
universe u v w x
variable {σ : Signature.{u, v, w}} {ℳ : Structure.{u, v, w, x} σ}

theorem templateEnv_nil : templateEnv (Values.nil : Values ℳ.Carrier []) = Env.empty := by
  apply Env.ext <;> intro sort entry <;> cases entry

theorem templateEnv_cons {free : SortContext σ} {sort : σ.SortSymbol}
    (args : Values ℳ.Carrier free) (value : ℳ.Carrier sort) :
    templateEnv (.cons value args) = (templateEnv args).pushFree value := by
  apply Env.ext
  · intro sort entry; cases entry
  · intro sort entry; cases entry <;> rfl

/-- 按有限排序上下文读取赋值的全部分量。 -/
def valuesOfAssignment : {free : SortContext σ} → Assignment ℳ free → Values ℳ.Carrier free
  | .nil, _ => .nil
  | .cons _ _, assignment => .cons (assignment .here)
      (valuesOfAssignment (fun entry => assignment (.there entry)))

theorem assignment_values {free : SortContext σ} (assignment : Assignment ℳ free)
    {sort : σ.SortSymbol} (entry : Variable free sort) :
    valuesAssignment (valuesOfAssignment assignment) entry = assignment entry := by
  induction entry with
  | here => rfl
  | there previous ih => exact ih _

/-- 从值列读取赋值再装配，仍得到原值列。 -/
theorem values_assignment {free : SortContext σ} (a : Values ℳ.Carrier free) :
    valuesOfAssignment (valuesAssignment a) = a := by
  induction a with
  | nil => rfl
  | cons a as h => exact congrArg (Values.cons a) h

theorem template_of_env {free : SortContext σ} (env : Env ℳ [] free) :
    templateEnv (valuesOfAssignment env.freeVal) = env := by
  apply Env.ext
  · intro sort entry; cases entry
  · intro sort entry; exact assignment_values _ entry

end YesMetaZFC.Automation.ModelClosure
