import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra

/-! # 类型化存在见证块

见证沿现有 `Arguments` 的排序列表携带；一次性替换新增槽位，保留外部自由参数。
量词引入和穿过 binder 的替换只在公共规则中归纳，不要求调用方按元数展开。
-/
namespace YesMetaZFC.Logic.FirstOrder

universe u v w
variable {σ : Signature.{u, v, w}}

set_option autoImplicit false

/-- 参数列占据替换的前缀槽位，剩余槽位由给定映射处理。 -/
def Arguments.substitutionWith {bound free tail : SortContext σ}
    (rest : VariableSubstitution σ tail bound free) :
    {slots : SortContext σ} → Arguments σ bound free slots →
      VariableSubstitution σ (slots ++ tail) bound free
  | _, .nil => rest
  | _, .cons head remaining =>
      VariableSubstitution.cons head (remaining.substitutionWith rest)

/-- 仅关闭指定前缀；列表头是最内层的新增自由槽。 -/
def Formula.existsFreePrefix {bound free : SortContext σ} :
    (slots : SortContext σ) → Formula σ bound (slots ++ free) → Formula σ bound free
  | [], body => body
  | sort :: remaining, body => existsFreePrefix remaining (body.existsFreeTop sort)

/-- 提升后的槽位替换再实例化首槽，等于一次性添加该见证。 -/
theorem Formula.instantiateFreeTop_substituteFree_liftFree
    {bound sourceFree targetFree : SortContext σ} {sort : σ.SortSymbol}
    (body : Formula σ bound (sort :: sourceFree))
    (substitution : VariableSubstitution σ sourceFree bound targetFree)
    (witness : Term σ bound targetFree sort) :
    (body.substituteFree (VariableSubstitution.liftFree sort substitution)).instantiateFreeTop
        witness = body.substituteFree (VariableSubstitution.cons witness substitution) := by
  change (body.substituteFree _).substituteFree _ = _
  rw [Formula.substituteFree_comp]
  congr 1
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      exact Term.substituteMapped_weakenFree_instantiateFreeTop _ _ _

/-- 任意长度、任意排序的存在见证一次性装配；外部自由参数保持原值。 -/
theorem Derives.existsFreePrefix_intro
    {T : Theory σ} {free slots : SortContext σ} {Γ : Context σ free}
    (witnesses : Arguments σ [] free slots)
    {body : OpenFormula σ (slots ++ free)}
    (hBody : Derives T Γ
      (body.substituteFree (witnesses.substitutionWith VariableSubstitution.freeId))) :
    Derives T Γ (body.existsFreePrefix slots) := by
  induction slots with
  | nil =>
      cases witnesses
      simpa only [Arguments.substitutionWith, Formula.substituteFree,
        Formula.substitute, Substitution.free_map, Formula.substituteMapped_id,
        Formula.existsFreePrefix] using hBody
  | cons sort remaining ih =>
      cases witnesses with
      | cons head tail =>
          apply ih tail (body := body.existsFreeTop sort)
          rw [Formula.substituteFree_existsFreeTop]
          apply Derives.exists_intro head
          rw [Formula.instantiateTop_abstractFreeTop,
            Formula.instantiateFreeTop_substituteFree_liftFree]
          exact hBody

end YesMetaZFC.Logic.FirstOrder
