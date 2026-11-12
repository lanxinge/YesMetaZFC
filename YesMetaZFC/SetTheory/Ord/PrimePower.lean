import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison
/-!
# 模型内部的素数幂解析
本模块在集合模型内部定义自然数整除、素数与素数幂关系。编码使用关系式算术：
`power` 是 `prime ^ exponent` 的序数递归值，而不是在元层选择一个全局运算函数。
对同一个素数底数，幂值与指数可以相互唯一恢复。证明直接复用序数幂的存在唯一性与
指数单射定理，因此适用于模型内部任意属于 `ω` 的指数，包括外部看来的非标准元素。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/-- `divisor` 是 `number` 的模型内部自然数因子。 -/
def IsNaturalDivisor
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω divisor number : ℳ.Domain) : Prop :=
  ℳ.mem divisor ω ∧
    ∃ quotient,
      ℳ.mem quotient ω ∧
        ℳ.IsOrdinalMultiplication 𝕀 number divisor quotient
/-- `prime` 是 `ω` 中大于一且只有平凡自然数因子的素数。 -/
structure IsPrimeInOmega
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω one prime : ℳ.Domain) : Prop where
  one_is_one : ℳ.IsOrdinalOne one
  prime_mem_omega : ℳ.mem prime ω
  one_mem_prime : ℳ.mem one prime
  only_trivial_divisors :
    ∀ divisor,
      ℳ.IsNaturalDivisor 𝕀 ω divisor prime →
        divisor = one ∨ divisor = prime
/-- `power` 是给定模型内部素数的一个自然数指数幂。 -/
structure IsPrimePower
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω one power prime exponent : ℳ.Domain) : Prop where
  prime_is_prime : ℳ.IsPrimeInOmega 𝕀 ω one prime
  exponent_mem_omega : ℳ.mem exponent ω
  power_spec : ℳ.IsOrdinalExponentiation 𝕀 power prime exponent
namespace IsPrimeInOmega
/-- 模型内部素数首先是一个序数。 -/
theorem prime_isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one prime : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPrime : ℳ.IsPrimeInOmega 𝕀 ω one prime) :
    ℳ.IsOrdinal prime :=
  hω.members_areOrdinals (ZF.modelsKP hZF) prime hPrime.prime_mem_omega
/-- 素数合同中使用的一确实是序数。 -/
theorem one_isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one prime : ℳ.Domain} (hPrime : ℳ.IsPrimeInOmega 𝕀 ω one prime) :
    ℳ.IsOrdinal one :=
  KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hPrime.one_is_one
end IsPrimeInOmega
namespace IsPrimePower
/-- 素数幂的指数是一个序数。 -/
theorem exponent_isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one power prime exponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPower : ℳ.IsPrimePower 𝕀 ω one power prime exponent) :
    ℳ.IsOrdinal exponent :=
  hω.members_areOrdinals (ZF.modelsKP hZF) exponent hPower.exponent_mem_omega
/-- 素数幂的值仍是序数。 -/
theorem power_isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one power prime exponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPower : ℳ.IsPrimePower 𝕀 ω one power prime exponent) :
    ℳ.IsOrdinal power :=
  ZF.ordinalExponentiation_isOrdinal hZF 𝕀 (hPower.prime_is_prime.prime_isOrdinal hZF hω) (hPower.exponent_isOrdinal hZF hω)
    hPower.power_spec
/-- 素数幂的值仍属于模型内部的自然数 `ω`。 -/
theorem power_mem_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one power prime exponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPower : ℳ.IsPrimePower 𝕀 ω one power prime exponent) :
    ℳ.mem power ω :=
  ZF.ordinalExponentiation_mem_omega hZF 𝕀 hω
    hPower.prime_is_prime.prime_mem_omega
    hPower.exponent_mem_omega hPower.power_spec
/-- 固定模型内部素数和指数时，素数幂值存在且唯一。 -/
theorem exists_unique_power
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one prime exponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPrime : ℳ.IsPrimeInOmega 𝕀 ω one prime) (hExponent : ℳ.mem exponent ω) :
    ∃ power,
      ℳ.IsPrimePower 𝕀 ω one power prime exponent ∧
        ∀ other,
          ℳ.IsPrimePower 𝕀 ω one other prime exponent →
            other = power := by
  rcases ZF.ordinalExponentiation_existsUnique hZF 𝕀 (hPrime.prime_isOrdinal hZF hω) (hω.members_areOrdinals (ZF.modelsKP hZF) exponent hExponent) with
    ⟨power, hPower, hUnique⟩
  refine ⟨power, ⟨hPrime, hExponent, hPower⟩, ?_⟩
  intro other hOther
  exact hUnique other hOther.power_spec
/-- 固定素数和指数时，素数幂的模型内部值唯一。 -/
theorem power_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one first second prime exponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hFirst : ℳ.IsPrimePower 𝕀 ω one first prime exponent)
    (hSecond : ℳ.IsPrimePower 𝕀 ω one second prime exponent) :
    first = second := by
  rcases ZF.ordinalExponentiation_existsUnique hZF 𝕀 (hFirst.prime_is_prime.prime_isOrdinal hZF hω) (hFirst.exponent_isOrdinal hZF hω) with
    ⟨selected, _, hUnique⟩
  exact (hUnique first hFirst.power_spec).trans (hUnique second hSecond.power_spec).symm
/-- 固定素数底数时，相同幂值只能来自相同指数。 -/
theorem exponent_eq_of_power_eq
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one firstPower secondPower prime firstExponent secondExponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hFirst :
      ℳ.IsPrimePower 𝕀 ω one firstPower prime firstExponent) (hSecond :
      ℳ.IsPrimePower 𝕀 ω one secondPower prime secondExponent) (hPowerEq : firstPower = secondPower) :
    firstExponent = secondExponent := by
  subst secondPower
  exact ZF.ordinalExponentiation_exponent_injective hZF 𝕀 (hFirst.prime_is_prime.prime_isOrdinal hZF hω)
    hFirst.prime_is_prime.one_is_one
    hFirst.prime_is_prime.one_mem_prime (hFirst.exponent_isOrdinal hZF hω) (hSecond.exponent_isOrdinal hZF hω)
    hFirst.power_spec hSecond.power_spec
/-- 给定模型内部的固定素数幂值，指数解析存在且唯一。 -/
theorem exists_unique_exponent
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one power prime : ℳ.Domain} (hω : ℳ.IsOmega ω) (hExists : ∃ exponent,
      ℳ.IsPrimePower 𝕀 ω one power prime exponent) :
    ∃ exponent,
      ℳ.IsPrimePower 𝕀 ω one power prime exponent ∧
        ∀ other,
          ℳ.IsPrimePower 𝕀 ω one power prime other →
            other = exponent := by
  rcases hExists with ⟨exponent, hExponent⟩
  refine ⟨exponent, hExponent, ?_⟩
  intro other hOther
  exact (hExponent.exponent_eq_of_power_eq hZF hω hOther rfl).symm
/-- 固定素数底数后，幂值相等当且仅当指数相等。 -/
theorem power_eq_iff_exponent_eq
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one firstPower secondPower prime firstExponent secondExponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hFirst :
      ℳ.IsPrimePower 𝕀 ω one firstPower prime firstExponent) (hSecond :
      ℳ.IsPrimePower 𝕀 ω one secondPower prime secondExponent) :
    firstPower = secondPower ↔ firstExponent = secondExponent := by
  constructor
  · exact hFirst.exponent_eq_of_power_eq hZF hω hSecond
  · intro hExponentEq
    subst secondExponent
    exact hFirst.power_unique hZF hω hSecond
end IsPrimePower
end Structure
end SetTheory
end YesMetaZFC
