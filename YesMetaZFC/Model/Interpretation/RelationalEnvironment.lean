import YesMetaZFC.Model.Interpretation.RelationalTranslation
import YesMetaZFC.Model.FirstOrder.Valuation

/-! # 函数图消去的环境与存在见证

同时加入的 bound 块由异质值列解释。模板代入、变量跳过和量词闭合分别在语义上
对应读取参数、保持旧赋值和存在一个值列。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
universe x
variable {σ τ : Signature.{0, 0, 0}}

@[simp] theorem argumentsSubstitution_eval {M : Structure.{0, 0, 0, x} τ}
    {bound free sorts : SortContext τ} (env : Env M bound free)
    (args : Arguments τ bound free sorts) {sort : τ.SortSymbol} (entry : Variable sorts sort) :
    (argumentsSubstitution args entry).eval env = valuesAssignment (args.eval env) entry := by
  cases args with
  | nil => cases entry
  | cons head tail => cases entry with
    | here => rfl
    | there previous => exact argumentsSubstitution_eval env tail previous

theorem pullback_arguments {M : Structure.{0, 0, 0, x} τ}
    {bound free sorts : SortContext τ} (env : Env M bound free)
    (args : Arguments τ bound free sorts) :
    env.pullback (Substitution.map VariableSubstitution.empty (argumentsSubstitution args)) =
      templateEnv (args.eval env) := by
  apply Env.ext
  · intro sort entry; exact nomatch entry
  · intro sort entry; exact argumentsSubstitution_eval env args entry

theorem pullback_free_arguments {M : Structure.{0, 0, 0, x} τ}
    {free sorts : SortContext τ} (env : Env M [] free)
    (args : Arguments τ [] free sorts) :
    env.pullback (Substitution.free_map (argumentsSubstitution args)) =
      templateEnv (args.eval env) := by
  apply Env.ext
  · intro sort entry; exact nomatch entry
  · intro sort entry; exact argumentsSubstitution_eval env args entry

/-- 固定关系模板的语义只依赖实际参数值。 -/
theorem applyTemplate_satisfies {M : Structure.{0, 0, 0, x} τ}
    {bound free sorts : SortContext τ} (env : Env M bound free)
    (body : Formula τ [] sorts) (args : Arguments τ bound free sorts) :
    (applyTemplate body args).satisfies env ↔ body.satisfies (templateEnv (args.eval env)) := by
  have h := Formula.satisfies_substitute env
    (Substitution.map VariableSubstitution.empty (argumentsSubstitution args)) body
  change (applyTemplate body args).satisfies env ↔ _ at h
  rwa [pullback_arguments] at h

/-- 在旧环境前加入一个异质 bound 值块。 -/
def pushBlock {M : Structure.{0, 0, 0, x} τ} {bound free sorts : SortContext τ}
    (env : Env M bound free) (values : Values M.Carrier sorts) : Env M (sorts ++ bound) free :=
  match values with
  | .nil => env
  | .cons head tail => (pushBlock env tail).pushBound head

@[simp] theorem pushBlock_skip {M : Structure.{0, 0, 0, x} τ}
    {bound free sorts : SortContext τ} (env : Env M bound free) (values : Values M.Carrier sorts)
    {sort : τ.SortSymbol} (entry : Variable bound sort) :
    (pushBlock env values).boundVal (skip sorts entry) = env.boundVal entry := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact ih

@[simp] theorem pushBlock_free {M : Structure.{0, 0, 0, x} τ}
    {bound free sorts : SortContext τ} (env : Env M bound free) (values : Values M.Carrier sorts)
    {sort : τ.SortSymbol} (entry : Variable free sort) :
    (pushBlock env values).freeVal entry = env.freeVal entry := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact ih

@[simp] theorem weakenTerm_eval {M : Structure.{0, 0, 0, x} τ}
    {bound free sorts : SortContext τ} (env : Env M bound free) (values : Values M.Carrier sorts)
    {sort : τ.SortSymbol} (input : Term τ bound free sort) :
    (weakenTerm sorts input).eval (pushBlock env values) = input.eval env := by
  have h := Term.eval_rename (pushBlock env values) (Renaming.map (skip sorts) VariableRenaming.id) input
  change (weakenTerm sorts input).eval (pushBlock env values) = _ at h
  rw [h]
  congr 1
  apply Env.ext
  · intro sort entry
    exact pushBlock_skip env values entry
  · intro sort entry
    exact pushBlock_free env values entry

@[simp] theorem witnesses_eval {M : Structure.{0, 0, 0, x} τ}
    {bound free sorts : SortContext τ} (env : Env M bound free) (values : Values M.Carrier sorts) :
    (witnesses sorts).eval (pushBlock env values) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [witnesses, pushBlock, Arguments.eval, Term.eval, Env.pushBound_bound_here,
      Arguments.eval_weakenBound, ih]

/-- 存在量词块精确对应一个任意对象值列。 -/
theorem existsBlock_satisfies {M : Structure.{0, 0, 0, x} τ}
    {bound free : SortContext τ} (env : Env M bound free) (sorts : SortContext τ)
    (body : Formula τ (sorts ++ bound) free) :
    (existsBlock sorts body).satisfies env ↔
      ∃ values : Values M.Carrier sorts, body.satisfies (pushBlock env values) := by
  induction sorts with
  | nil =>
    constructor
    · intro h
      exact ⟨.nil, h⟩
    · rintro ⟨values, h⟩
      cases values
      exact h
  | cons sort rest ih =>
    rw [existsBlock, ih]
    constructor
    · rintro ⟨tail, head, h⟩
      exact ⟨.cons head tail, h⟩
    · rintro ⟨values, h⟩
      cases values with
      | cons head tail => exact ⟨tail, head, h⟩

/-- 参数列的递归只依赖排序映射，不携带函数图、关系图或所选扩张。 -/
def mapSortValues (sortMap : σ.SortSymbol → τ.SortSymbol) {M : Structure.{0, 0, 0, x} τ}
    {sorts : SortContext σ} (values : Values (fun sort => M.Carrier (sortMap sort)) sorts) :
    Values M.Carrier (sorts.map sortMap) :=
  match values with
  | .nil => .nil
  | .cons head tail => .cons head (mapSortValues sortMap tail)

/-- 沿源到目标的排序映射转换语义参数列。 -/
def mapValues (I : Interpretation σ τ) {M : Structure.{0, 0, 0, x} τ} {sorts : SortContext σ}
    (values : Values (fun sort => M.Carrier (I.sort sort)) sorts) : Values M.Carrier (sorts.map I.sort) :=
  mapSortValues I.sort values

end YesMetaZFC.Automation.RelationalTranslation
