import YesMetaZFC.SetTheory.Card.Properties.Syntax
import YesMetaZFC.SetTheory.Card.Cofinality.Basic
import YesMetaZFC.SetTheory.SetConstruction
/-!
# 基数基础性质语义
本层解释不可数、极限、正则、奇异与强极限基数，并整理这些性质的基础投影和互斥性。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/-- `κ` 是严格大于给定 `ω` 的基数。 -/
def IsUncountableCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω κ : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 κ ∧
    ℳ.mem ω κ
/-- `κ` 是极限基数：每个较小序数上方仍有严格较小的基数。 -/
def IsLimitCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (κ : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 κ ∧
    ∀ α, ℳ.mem α κ →
      ∃ μ, ℳ.mem μ κ ∧
        ℳ.IsCardinal 𝕀 μ ∧
          ℳ.mem α μ
/-- `κ` 是正则基数，即 `cf(κ) = κ`。 -/
def IsRegularCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (κ : ℳ.Domain) : Prop :=
  ℳ.IsCofinality 𝕀 κ κ
/-- `κ` 是奇异基数，即其共尾度严格小于自身。 -/
def IsSingularCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (κ : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 κ ∧
    ∃ cf, ℳ.mem cf κ ∧
      ℳ.IsCofinality 𝕀 cf κ
/-- `κ` 是强极限基数：每个 `α < κ` 的幂集基数仍严格小于 `κ`。 -/
def IsStrongLimitCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (κ : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 κ ∧
    ∀ α, ℳ.mem α κ →
      ∀ power, ℳ.IsPowerSetOf power α →
        ℳ.CardinalLess 𝕀 power κ
namespace IsRegularCardinal
/-- 正则基数首先是基数。 -/
theorem isCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {κ : ℳ.Domain} (hRegular : ℳ.IsRegularCardinal 𝕀 κ) :
    ℳ.IsCardinal 𝕀 κ :=
  hRegular.1
/-- 正则基数在当前共尾度定义下是极限序数。 -/
theorem isLimitOrdinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {κ : ℳ.Domain} (hRegular : ℳ.IsRegularCardinal 𝕀 κ) :
    ℳ.IsLimitOrdinal κ := by
  rcases hRegular.hasCofinalSequence with
    ⟨sequence, hSequence⟩
  exact hSequence.isLimitOrdinal
end IsRegularCardinal
namespace IsSingularCardinal
/-- 奇异基数不可能同时正则。 -/
theorem not_regular {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {κ : ℳ.Domain} (hSingular : ℳ.IsSingularCardinal 𝕀 κ) :
    ¬ ℳ.IsRegularCardinal 𝕀 κ := by
  intro hRegular
  rcases hSingular.2 with ⟨cf, hcfκ, hCofinality⟩
  have hEq : cf = κ := by
    exact IsCofinality.eq hCofinality hRegular
  subst cf
  exact hRegular.isCardinal.1.wellOrder.linear.irrefl
    κ hcfκ hcfκ
end IsSingularCardinal
end Structure
namespace Definitional
namespace Project
namespace Formula
/-- 不可数基数公式与相对 `ω` 的严格序数比较语义一致。 -/

theorem satisfies_isUncountableCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (ω κ : Term depth) :
    satisfies env (isUncountableCardinal 𝒞 ω κ) ↔
      ℳ.IsUncountableCardinal 𝕀 (ω.eval env) (κ.eval env) := by
  simp only [isUncountableCardinal,
    Structure.IsUncountableCardinal,
    satisfies_conj_iff, satisfies_mem_iff,
    satisfies_isCardinal_iff 𝕀 hExt]
/-- 极限基数公式与较小基数无上界的模型内部语义一致。 -/

theorem satisfies_isLimitCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (κ : Term depth) :
    satisfies env (isLimitCardinal 𝒞 κ) ↔
      ℳ.IsLimitCardinal 𝕀 (κ.eval env) := by
  simp only [isLimitCardinal, Structure.IsLimitCardinal,
    satisfies_conj_iff, satisfies_forallMem_iff,
    satisfies_existsMem_iff, satisfies_mem_iff,
    satisfies_isCardinal_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
/-- 正则基数公式与 `cf(κ) = κ` 的模型内部语义一致。 -/

theorem satisfies_isRegularCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (κ : Term depth) :
    satisfies env (isRegularCardinal 𝒞 κ) ↔
      ℳ.IsRegularCardinal 𝕀 (κ.eval env) := by
  simp only [isRegularCardinal, Structure.IsRegularCardinal,
    satisfies_isCofinality_iff 𝕀 hExt]
/-- 奇异基数公式与“小于自身的共尾度”语义一致。 -/

theorem satisfies_isSingularCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (κ : Term depth) :
    satisfies env (isSingularCardinal 𝒞 κ) ↔
      ℳ.IsSingularCardinal 𝕀 (κ.eval env) := by
  simp only [isSingularCardinal, Structure.IsSingularCardinal,
    satisfies_conj_iff, satisfies_existsMem_iff,
    satisfies_isCardinal_iff 𝕀 hExt,
    satisfies_isCofinality_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
/-- 强极限基数公式与所有较小幂集的基数界语义一致。 -/

theorem satisfies_isStrongLimitCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (κ : Term depth) :
    satisfies env (isStrongLimitCardinal 𝒞 κ) ↔
      ℳ.IsStrongLimitCardinal 𝕀 (κ.eval env) := by
  simp only [isStrongLimitCardinal,
    Structure.IsStrongLimitCardinal,
    satisfies_conj_iff, satisfies_forallMem_iff,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_isCardinal_iff 𝕀 hExt,
    satisfies_isPowerSet_iff,
    satisfies_cardinalLess_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
