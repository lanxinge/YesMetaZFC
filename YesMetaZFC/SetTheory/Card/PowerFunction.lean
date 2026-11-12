import YesMetaZFC.SetTheory.Card.Arithmetic.PowerSet
import YesMetaZFC.SetTheory.Card.PowerBound
import YesMetaZFC.SetTheory.Card.InfiniteBound

/-! # 幂集值函数的单个子集编码

特征函数与解柯里化把 D → 𝒫(κ) 编为 κ × D 的子集；D ≤ κ 时，
无限基数的积编号再将代码压入 𝒫(κ)。全部单射都是原模型内部的集合。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 模型内的 `(𝒫 κ)^D ≤ 𝒫 κ`；只需 ZF、无限基数 κ 及 D ≤ κ。 -/
theorem power_function_bound_l (hZF : M.Models ZF) {ω κ D P F : M.Domain}
    (hω : M.IsOmega ω) (hκ : M.IsInfiniteCardinal I ω κ)
    (small : M.CardinalLessOrEqual I D κ) (power : M.IsPowerSetOf P κ)
    (space : M.IsFunctionSpace I F D P) : M.CardinalLessOrEqual I F P := by
  obtain ⟨z,empty,hz⟩ := hω.1.1
  obtain ⟨o,succ,_⟩ := hω.1.2 z hz
  have ne : z ≠ o := fun eq => empty z (eq.symm ▸ succ.predecessor_mem)
  obtain ⟨two,digits⟩ := KP.exists_pair (modelsKP hZF) z o
  obtain ⟨B,binary⟩ := exists_functionSpace hZF I κ two
  obtain ⟨G,nested⟩ := exists_functionSpace hZF I D B
  obtain ⟨K,product⟩ := exists_cartesianProduct hZF I κ D
  obtain ⟨H,flat⟩ := exists_functionSpace hZF I K two
  obtain ⟨Q,powerK⟩ := exists_powerSet hZF K
  have characteristic := equinumerous_powerSet_functionSpace hZF I power digits ne binary
  have first := equinumerous_functionSpace hZF I space nested
    (Structure.Equinumerous.refl hZF I D) characteristic
  have second := equinumerous_nestedFunctionSpace hZF I binary nested product flat
  have third := (equinumerous_powerSet_functionSpace hZF I powerK digits ne flat).symm hZF I
  obtain ⟨f,hf⟩ := (first.trans hZF I second).trans hZF I third
  obtain ⟨id,identity⟩ := exists_identityBijection hZF I κ
  obtain ⟨j,hj⟩ := infinite_product_l I hZF hω hκ ⟨id,identity.1⟩ small product
  obtain ⟨k,hk⟩ := power_injection_l I hZF powerK power hj
  exact exists_compositionInjection hZF I hf.1 hk

end YesMetaZFC.SetTheory.ZF
