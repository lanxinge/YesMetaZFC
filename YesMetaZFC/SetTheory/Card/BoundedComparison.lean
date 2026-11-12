import YesMetaZFC.SetTheory.Card.SmallEnumeration
import YesMetaZFC.SetTheory.Card.SmallBound

/-! # 已有序数单射界的集合比较

只对已可良序的集合取内部基数代表，不加入选择公理。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem bounded_cardinal_l {κ X : M.Domain} (hκ : M.IsOrdinal κ) (bound : M.CardinalLessOrEqual I X κ) :
    ∃ μ F, M.IsCardinal I μ ∧ M.IsSetBijectionFromTo I F μ X := by
  obtain ⟨δ,hδ,κδ⟩ := exists_cardinalAbove hZF I hκ
  obtain ⟨μ,F,_,hμ,bijection⟩ := small_enumeration_l I hZF hδ κδ bound
  exact ⟨μ,F,hμ,bijection⟩

theorem bounded_compare_l {κ X Y : M.Domain} (hκ : M.IsOrdinal κ)
    (hx : M.CardinalLessOrEqual I X κ) (hy : M.CardinalLessOrEqual I Y κ) :
    M.CardinalLessOrEqual I X Y ∨ M.CardinalLessOrEqual I Y X := by
  obtain ⟨μ,F,hμ,fx⟩ := bounded_cardinal_l I hZF hκ hx
  obtain ⟨ν,G,hν,gy⟩ := bounded_cardinal_l I hZF hκ hy
  have transport {μ ν X Y F G} (fx : M.IsSetBijectionFromTo I F μ X) (gy : M.IsSetBijectionFromTo I G ν Y)
      (sub : M.MemberSubset μ ν) : M.CardinalLessOrEqual I X Y := by
    obtain ⟨J,j⟩ := exists_inverseBijection hZF I fx
    obtain ⟨K,k⟩ := exists_inclusionInjection hZF I sub
    obtain ⟨L,l⟩ := exists_compositionInjection hZF I j.1 k
    exact exists_compositionInjection hZF I l gy.1
  rcases hμ.1.trichotomy hZF.1 hν.1 (KP.difference_exists_d (modelsKP hZF))
      (KP.intersection_exists_d (modelsKP hZF) μ ν) with same | μν | νμ
  · exact Or.inl (transport fx gy (fun x hx => (same x).mp hx))
  · exact Or.inl (transport fx gy (hν.1.transitive μ μν))
  · exact Or.inr (transport gy fx (hμ.1.transitive ν νμ))

theorem small_infinite_bound_l {ω κ X : M.Domain} (hκ : M.IsUncountableCardinal I ω κ)
    (bound : M.CardinalLessOrEqual I X κ) (small : ¬ M.CardinalLessOrEqual I κ X) :
    ∃ μ, M.mem μ κ ∧ M.IsInfiniteCardinal I ω μ ∧ M.CardinalLessOrEqual I X μ := by
  have strict : M.CardinalLess I X κ := ⟨bound,fun eq => small (by
    obtain ⟨F,fn⟩ := eq.symm hZF I
    exact ⟨F,fn.1⟩)⟩
  obtain ⟨α,hα,xα⟩ := ordinal_small_bound_l I hZF hκ.1.1 strict
  obtain ⟨μ,hμ,inf,αμ,_⟩ := common_cardinal_l I hZF hκ.1.1 hκ.2 hα hα
  obtain ⟨F,fn⟩ := xα
  obtain ⟨G,gn⟩ := αμ
  exact ⟨μ,hμ,inf,exists_compositionInjection hZF I fn gn⟩

theorem cardinal_not_le_member_l {κ μ : M.Domain} (hκ : M.IsCardinal I κ) (hμ : M.mem μ κ) :
    ¬ M.CardinalLessOrEqual I κ μ := by
  intro bound
  exact hκ.2 μ hμ (equinumerous_of_cardinalLessOrEqual hZF I
    (exists_inclusionInjection hZF I (hκ.1.transitive μ hμ)) bound)

end YesMetaZFC.SetTheory.ZF
