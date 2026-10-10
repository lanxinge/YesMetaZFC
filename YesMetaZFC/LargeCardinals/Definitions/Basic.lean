import YesMetaZFC.LargeCardinals.Definitions.Syntax
import YesMetaZFC.SetTheory.Card.Properties.Basic
/-!
# 不可达基数定义语义
本层只解释弱不可达与强不可达基数，并导出它们在基数性质层中的三个定义分量。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/-- `κ` 是弱不可达基数。 -/
def IsWeaklyInaccessibleCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω κ : ℳ.Domain) : Prop :=
  ℳ.IsUncountableCardinal 𝕀 ω κ ∧
    ℳ.IsRegularCardinal 𝕀 κ ∧
      ℳ.IsLimitCardinal 𝕀 κ
/-- `κ` 是强不可达基数。 -/
def IsStronglyInaccessibleCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω κ : ℳ.Domain) : Prop :=
  ℳ.IsUncountableCardinal 𝕀 ω κ ∧
    ℳ.IsRegularCardinal 𝕀 κ ∧
      ℳ.IsStrongLimitCardinal 𝕀 κ
namespace IsWeaklyInaccessibleCardinal
/-- 弱不可达基数是不可数基数。 -/
theorem isUncountable {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω κ : ℳ.Domain} (hInaccessible :
      ℳ.IsWeaklyInaccessibleCardinal 𝕀 ω κ) :
    ℳ.IsUncountableCardinal 𝕀 ω κ :=
  hInaccessible.1
/-- 弱不可达基数是正则基数。 -/
theorem isRegular {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω κ : ℳ.Domain} (hInaccessible :
      ℳ.IsWeaklyInaccessibleCardinal 𝕀 ω κ) :
    ℳ.IsRegularCardinal 𝕀 κ :=
  hInaccessible.2.1
/-- 弱不可达基数是极限基数。 -/
theorem isLimitCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω κ : ℳ.Domain} (hInaccessible :
      ℳ.IsWeaklyInaccessibleCardinal 𝕀 ω κ) :
    ℳ.IsLimitCardinal 𝕀 κ :=
  hInaccessible.2.2
end IsWeaklyInaccessibleCardinal
namespace IsStronglyInaccessibleCardinal
/-- 强不可达基数是不可数基数。 -/
theorem isUncountable {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω κ : ℳ.Domain} (hInaccessible :
      ℳ.IsStronglyInaccessibleCardinal 𝕀 ω κ) :
    ℳ.IsUncountableCardinal 𝕀 ω κ :=
  hInaccessible.1
/-- 强不可达基数是正则基数。 -/
theorem isRegular {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω κ : ℳ.Domain} (hInaccessible :
      ℳ.IsStronglyInaccessibleCardinal 𝕀 ω κ) :
    ℳ.IsRegularCardinal 𝕀 κ :=
  hInaccessible.2.1
/-- 强不可达基数是强极限基数。 -/
theorem isStrongLimit {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω κ : ℳ.Domain} (hInaccessible :
      ℳ.IsStronglyInaccessibleCardinal 𝕀 ω κ) :
    ℳ.IsStrongLimitCardinal 𝕀 κ :=
  hInaccessible.2.2
end IsStronglyInaccessibleCardinal
end Structure
namespace Definitional
namespace Project
namespace Formula
/-- 弱不可达基数公式与三个定义分量的合取语义一致。 -/

theorem satisfies_isWeaklyInaccessibleCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (ω κ : Term depth) :
    satisfies env (isWeaklyInaccessibleCardinal 𝒞 ω κ) ↔
      ℳ.IsWeaklyInaccessibleCardinal 𝕀 (ω.eval env) (κ.eval env) := by
  simp only [isWeaklyInaccessibleCardinal,
    Structure.IsWeaklyInaccessibleCardinal,
    satisfies_conj_iff,
    satisfies_isUncountableCardinal_iff 𝕀 hExt,
    satisfies_isRegularCardinal_iff 𝕀 hExt,
    satisfies_isLimitCardinal_iff 𝕀 hExt]
/-- 强不可达基数公式与三个定义分量的合取语义一致。 -/

theorem satisfies_isStronglyInaccessibleCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (ω κ : Term depth) :
    satisfies env (isStronglyInaccessibleCardinal 𝒞 ω κ) ↔
      ℳ.IsStronglyInaccessibleCardinal 𝕀 (ω.eval env) (κ.eval env) := by
  simp only [isStronglyInaccessibleCardinal,
    Structure.IsStronglyInaccessibleCardinal,
    satisfies_conj_iff,
    satisfies_isUncountableCardinal_iff 𝕀 hExt,
    satisfies_isRegularCardinal_iff 𝕀 hExt,
    satisfies_isStrongLimitCardinal_iff 𝕀 hExt]
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
