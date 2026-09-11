import YesMetaZFC.Model.Interpretation.PredicateExpansion

/-! # 关系赋值的逐公式同余

把原子层等价按公式结构传输，避免在具体模型中展开大型关系定义。
-/
namespace YesMetaZFC.Automation.PredicateExpansion
open Logic Logic.FirstOrder
set_option autoImplicit false
universe x
variable {σ : Signature.{0,0,0}} {𝒩 : Structure.{0,0,0,x} σ}
theorem evaluate_congr (first second : Relations 𝒩)
    (hSame : ∀ symbol args, first symbol args ↔ second symbol args)
    {bound free : SortContext σ} (env : Env 𝒩 bound free) (body : Formula σ bound free) :
    evaluate first env body ↔ evaluate second env body := by
  induction body with
  | falsum => rfl
  | truth => rfl
  | rel symbol args => exact hSame symbol _
  | equal left right => rfl
  | neg body ih => exact not_congr (ih env)
  | conj left right ihLeft ihRight => exact and_congr (ihLeft env) (ihRight env)
  | disj left right ihLeft ihRight => exact or_congr (ihLeft env) (ihRight env)
  | imp left right ihLeft ihRight => exact imp_congr (ihLeft env) (ihRight env)
  | iff left right ihLeft ihRight => exact iff_congr (ihLeft env) (ihRight env)
  | forallE sort body ih => exact forall_congr' (fun value => ih (env.pushBound value))
  | existsE sort body ih => exact exists_congr (fun value => ih (env.pushBound value))
end YesMetaZFC.Automation.PredicateExpansion
