import YesMetaZFC.SetTheory.Ord.Closure
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion

/-!
# 序数算术的序数值闭包

本文件沿统一的序数值归纳接口证明加法、乘法与幂保持序数。三种运算共享反例分离、
最小反例和极限并闭包，只在各自的零步与后继步提供数学内容。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace ZF

/-- 固定序数左参数的序数加法是序数值类函数。 -/
theorem ordinalAddition_isOrdinalClassFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeft : ℳ.IsOrdinal left) :
    ℳ.IsOrdinalClassFunction
      (fun right sum =>
        ℳ.IsOrdinalAddition 𝕀 sum left right) := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env =
        fun right sum =>
          ℳ.IsOrdinalAddition 𝕀 sum left right := by
    funext right sum
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalAddition_iff
        𝕀 hZF.1 env right sum
  have hSchemaClass :
      ℳ.IsOrdinalClassFunction
        ((Definitional.Project.BinarySchema.ordinalAddition 𝒞).denote env) := by
    apply ordinalClassFunction_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalAddition 𝒞)
    · rw [hRelation]
      exact ordinalAddition_isClassFunctionOnOrdinals
        hZF 𝕀 left
    · intro α hα hPrevious value hValue
      rw [hRelation] at hPrevious hValue
      rcases hα.classify hZF.1 with
        hEmpty | hSuccessor | hLimit
      · have hValueEq :=
          (ordinalAddition_zero_iff
            hZF 𝕀 hEmpty).mp hValue
        simpa [hValueEq] using hLeft
      · rcases hSuccessor with
          ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
        rcases (ordinalAddition_successor_iff
            hZF 𝕀 hPredecessorOrdinal hSuccessor).mp
            hValue with
          ⟨previous, hPreviousValue, hValueSuccessor⟩
        have hPredecessorMem : ℳ.mem predecessor α :=
          (hSuccessor predecessor).mpr
            (Or.inr fun _ => Iff.rfl)
        exact KP.successor_isOrdinal (ZF.modelsKP hZF)
          (hPrevious predecessor hPredecessorMem
            previous hPreviousValue)
          hValueSuccessor
      · rcases (ordinalAddition_limit_iff
            hZF 𝕀 hLimit).mp hValue with
          ⟨range, hRange, hUnion⟩
        apply Structure.IsOrdinal.of_union
          (ZF.modelsKP hZF) hUnion
        intro member hMember
        rcases (hRange member).mp hMember with
          ⟨index, hIndex, hMemberValue⟩
        exact hPrevious index hIndex member hMemberValue
  rw [hRelation] at hSchemaClass
  exact hSchemaClass

/-- 两个序数的序数加法值仍是序数。 -/
theorem ordinalAddition_isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sum left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hRight : ℳ.IsOrdinal right)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum left right) :
    ℳ.IsOrdinal sum :=
  (ordinalAddition_isOrdinalClassFunction
    hZF 𝕀 hLeft).2 right sum hRight hSum

/-- 固定序数左参数的序数乘法是序数值类函数。 -/
theorem ordinalMultiplication_isOrdinalClassFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left : ℳ.Domain} (hLeft : ℳ.IsOrdinal left) :
    ℳ.IsOrdinalClassFunction
      (fun right product =>
        ℳ.IsOrdinalMultiplication 𝕀 product left right) := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env =
        fun right product =>
          ℳ.IsOrdinalMultiplication 𝕀 product left right := by
    funext right product
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalMultiplication_iff
        𝕀 hZF.1 env right product
  have hSchemaClass :
      ℳ.IsOrdinalClassFunction
        ((Definitional.Project.BinarySchema.ordinalMultiplication 𝒞).denote env) := by
    apply ordinalClassFunction_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalMultiplication 𝒞)
    · rw [hRelation]
      exact ordinalMultiplication_isClassFunctionOnOrdinals
        hZF 𝕀 left
    · intro α hα hPrevious value hValue
      rw [hRelation] at hPrevious hValue
      rcases hα.classify hZF.1 with
        hEmpty | hSuccessor | hLimit
      · have hValueEmpty :=
          (ordinalMultiplication_zero_iff
            hZF 𝕀 hLeft hEmpty).mp hValue
        exact Structure.IsOrdinal.of_no_members hValueEmpty
      · rcases hSuccessor with
          ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
        rcases (ordinalMultiplication_successor_iff
            hZF 𝕀 hLeft hPredecessorOrdinal
              hSuccessor).mp hValue with
          ⟨previous, hPreviousValue, hValueAddition⟩
        have hPredecessorMem : ℳ.mem predecessor α :=
          (hSuccessor predecessor).mpr
            (Or.inr fun _ => Iff.rfl)
        have hPreviousOrdinal :=
          hPrevious predecessor hPredecessorMem
            previous hPreviousValue
        exact ordinalAddition_isOrdinal hZF 𝕀
          hPreviousOrdinal hLeft hValueAddition
      · rcases (ordinalMultiplication_limit_iff
            hZF 𝕀 hLeft hLimit).mp hValue with
          ⟨range, hRange, hUnion⟩
        apply Structure.IsOrdinal.of_union
          (ZF.modelsKP hZF) hUnion
        intro member hMember
        rcases (hRange member).mp hMember with
          ⟨index, hIndex, hMemberValue⟩
        exact hPrevious index hIndex member hMemberValue
  rw [hRelation] at hSchemaClass
  exact hSchemaClass

/-- 两个序数的序数乘法值仍是序数。 -/
theorem ordinalMultiplication_isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {product left right : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left) (hRight : ℳ.IsOrdinal right)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left right) :
    ℳ.IsOrdinal product :=
  (ordinalMultiplication_isOrdinalClassFunction
    hZF 𝕀 hLeft).2 right product hRight hProduct

/-- 固定序数底数的序数幂是序数值类函数。 -/
theorem ordinalExponentiation_isOrdinalClassFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {base : ℳ.Domain} (hBase : ℳ.IsOrdinal base) :
    ℳ.IsOrdinalClassFunction
      (fun exponent power =>
        ℳ.IsOrdinalExponentiation 𝕀 power base exponent) := by
  let env : Env ℳ 1 := {
    bound := fun _ => base
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env =
        fun exponent power =>
          ℳ.IsOrdinalExponentiation 𝕀 power base exponent := by
    funext exponent power
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_ordinalExponentiation_iff
        𝕀 hZF.1 env exponent power
  have hSchemaClass :
      ℳ.IsOrdinalClassFunction
        ((Definitional.Project.BinarySchema.ordinalExponentiation 𝒞).denote env) := by
    apply ordinalClassFunction_of_progressive hZF env
      (Definitional.Project.BinarySchema.ordinalExponentiation 𝒞)
    · rw [hRelation]
      exact ordinalExponentiation_isClassFunctionOnOrdinals
        hZF 𝕀 hBase
    · intro α hα hPrevious value hValue
      rw [hRelation] at hPrevious hValue
      rcases hα.classify hZF.1 with
        hEmpty | hSuccessor | hLimit
      · have hValueOne :=
          (ordinalExponentiation_zero_iff
            hZF 𝕀 hBase hEmpty).mp hValue
        exact KP.ordinalOne_isOrdinal
          (ZF.modelsKP hZF) hValueOne
      · rcases hSuccessor with
          ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
        rcases (ordinalExponentiation_successor_iff
            hZF 𝕀 hBase hPredecessorOrdinal
              hSuccessor).mp hValue with
          ⟨previous, hPreviousValue, hValueMultiplication⟩
        have hPredecessorMem : ℳ.mem predecessor α :=
          (hSuccessor predecessor).mpr
            (Or.inr fun _ => Iff.rfl)
        have hPreviousOrdinal :=
          hPrevious predecessor hPredecessorMem
            previous hPreviousValue
        exact ordinalMultiplication_isOrdinal hZF 𝕀
          hPreviousOrdinal hBase hValueMultiplication
      · rcases (ordinalExponentiation_limit_iff
            hZF 𝕀 hBase hLimit).mp hValue with
          ⟨range, hRange, hUnion⟩
        apply Structure.IsOrdinal.of_union
          (ZF.modelsKP hZF) hUnion
        intro member hMember
        rcases (hRange member).mp hMember with
          ⟨index, hIndex, hMemberValue⟩
        exact hPrevious index hIndex member hMemberValue
  rw [hRelation] at hSchemaClass
  exact hSchemaClass

/-- 序数底数与序数指数的幂仍是序数。 -/
theorem ordinalExponentiation_isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {power base exponent : ℳ.Domain}
    (hBase : ℳ.IsOrdinal base) (hExponent : ℳ.IsOrdinal exponent)
    (hPower :
      ℳ.IsOrdinalExponentiation 𝕀 power base exponent) :
    ℳ.IsOrdinal power :=
  (ordinalExponentiation_isOrdinalClassFunction
    hZF 𝕀 hBase).2 exponent power hExponent hPower

end ZF

end SetTheory
end YesMetaZFC
