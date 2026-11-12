import YesMetaZFC.SetTheory.Ord.PrimePower
import YesMetaZFC.SetTheory.Ord.FiniteSequenceParsing
/-!
# 素数幂编码序列的模型内部解析
本模块组合素数幂反演与有限序列解析：固定素数底数后，序列每个位置都可唯一恢复
指数；两条序列若具有相同的逐位置指数视图，则其集合编码函数图相等。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/-- `sequence(index)` 是 `prime ^ exponent` 的模型内部解析关系。 -/
def IsPrimePowerAt
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω one prime sequence index exponent : ℳ.Domain) : Prop :=
  ∃ power,
    ℳ.PairMember 𝕀 index power sequence ∧
      ℳ.IsPrimePower 𝕀 ω one power prime exponent
/-- `sequence` 是固定素数底数的有限素数幂序列。 -/
def IsPrimePowerSequenceOfLength
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω one prime sequence length : ℳ.Domain) : Prop :=
  ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length ∧
    ∀ index,
      ℳ.mem index length →
        ∃ exponent,
          ℳ.IsPrimePowerAt 𝕀 ω one prime sequence index exponent
namespace IsPrimePowerAt
/-- 固定序列位置和素数底数时，解析出的指数唯一。 -/
theorem exponent_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one prime sequence length index first second : ℳ.Domain} (hω : ℳ.IsOmega ω) (hSequence : ℳ.IsFiniteSequenceOfLength 𝕀 ω sequence length)
    (hFirst : ℳ.IsPrimePowerAt 𝕀 ω one prime sequence index first) (hSecond : ℳ.IsPrimePowerAt 𝕀 ω one prime sequence index second) :
    first = second := by
  rcases hFirst with ⟨firstPower, hFirstValue, hFirstPower⟩
  rcases hSecond with ⟨secondPower, hSecondValue, hSecondPower⟩
  have hPowerEq : firstPower = secondPower :=
    hSequence.2.2.1.2 index firstPower secondPower
      hFirstValue hSecondValue
  exact hFirstPower.exponent_eq_of_power_eq
    hZF hω hSecondPower hPowerEq
end IsPrimePowerAt
namespace IsPrimePowerSequenceOfLength
/-- 素数幂序列每个有效位置的指数存在且唯一。 -/
theorem exponent_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one prime sequence length index : ℳ.Domain} (hω : ℳ.IsOmega ω) (hSequence :
      ℳ.IsPrimePowerSequenceOfLength 𝕀 ω one prime sequence length) (hIndex : ℳ.mem index length) :
    ∃ exponent,
      ℳ.IsPrimePowerAt 𝕀 ω one prime sequence index exponent ∧
        ∀ other,
          ℳ.IsPrimePowerAt 𝕀 ω one prime sequence index other →
            other = exponent := by
  rcases hSequence.2 index hIndex with ⟨exponent, hExponent⟩
  refine ⟨exponent, hExponent, ?_⟩
  intro other hOther
  exact (hExponent.exponent_unique hZF hω hSequence.1 hOther).symm
/-- 相同逐位置指数视图唯一决定整条素数幂序列。 -/
theorem sequence_unique_of_exponents
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one prime first second length : ℳ.Domain} (hω : ℳ.IsOmega ω) (hFirst :
      ℳ.IsPrimePowerSequenceOfLength 𝕀 ω one prime first length) (hSecond :
      ℳ.IsPrimePowerSequenceOfLength 𝕀 ω one prime second length) (hExponents : ∀ index exponent,
      ℳ.IsPrimePowerAt 𝕀 ω one prime first index exponent ↔
        ℳ.IsPrimePowerAt 𝕀 ω one prime second index exponent) :
    first = second := by
  apply hFirst.1.eq_of_pairMember_iff hZF.1 hSecond.1
  intro index value
  constructor
  · intro hFirstValue
    have hIndex : ℳ.mem index length := (hFirst.1.2.2.2 index).mpr ⟨value, hFirstValue⟩
    rcases hFirst.2 index hIndex with
      ⟨exponent, firstPower, hFirstPowerValue, hFirstPower⟩
    rcases (hExponents index exponent).mp
        ⟨firstPower, hFirstPowerValue, hFirstPower⟩ with
      ⟨secondPower, hSecondPowerValue, hSecondPower⟩
    have hValueEq : value = firstPower :=
      hFirst.1.2.2.1.2 index value firstPower
        hFirstValue hFirstPowerValue
    have hPowerEq : firstPower = secondPower :=
      hFirstPower.power_unique hZF hω hSecondPower
    simpa [hValueEq, hPowerEq] using hSecondPowerValue
  · intro hSecondValue
    have hIndex : ℳ.mem index length := (hSecond.1.2.2.2 index).mpr ⟨value, hSecondValue⟩
    rcases hSecond.2 index hIndex with
      ⟨exponent, secondPower, hSecondPowerValue, hSecondPower⟩
    rcases (hExponents index exponent).mpr
        ⟨secondPower, hSecondPowerValue, hSecondPower⟩ with
      ⟨firstPower, hFirstPowerValue, hFirstPower⟩
    have hValueEq : value = secondPower :=
      hSecond.1.2.2.1.2 index value secondPower
        hSecondValue hSecondPowerValue
    have hPowerEq : secondPower = firstPower :=
      hSecondPower.power_unique hZF hω hFirstPower
    simpa [hValueEq, hPowerEq] using hFirstPowerValue
end IsPrimePowerSequenceOfLength
end Structure
end SetTheory
end YesMetaZFC
