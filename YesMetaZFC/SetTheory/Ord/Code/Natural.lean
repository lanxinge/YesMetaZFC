import YesMetaZFC.SetTheory.Ord.Code.Pair
import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication

/-! # 规范序数配对在内部自然数上的封闭性

自然数对的全部前驱落在某个内部有限方块；前驱序型因而仍属于 ω。
不把模型内部有限性替换为外部自然数归纳。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem oc_pair_natural_l (hZF : M.Models ZF) {ω a b c} (hω : M.IsOmega ω)
    (ha : M.mem a ω) (hb : M.mem b ω) (h : Oc_pair_d I a b c) : M.mem c ω := by
  obtain ⟨t, p, hp, hc⟩ := h
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨R, hr, ho⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I (hω.isOrdinal hZF) hX
  have hpX := (hX p).mpr ⟨a, ha, b, hb, hp⟩
  have hv := oc_at_value_l I hZF (hω.isOrdinal hZF) hr hpX hc
  obtain ⟨P, hP, he⟩ := hv.predecessorSet_equinumerous hZF I ho
  obtain ⟨x, y, m, s, W, _, hx, hy, hm, hs, hW, hPW⟩ :=
    hr.predecessorSet_boundedByMaximumSquare hZF (hω.isOrdinal hZF) hpX hP
  obtain ⟨s', hs', hsω⟩ := hω.1.2 m (hm.mem hx hy)
  have eq := Structure.SuccessorOf.eq hZF.1 hs hs'; subst s'
  obtain ⟨n, hn, J, hJ⟩ := ZF.cartesianSquare_bounded_in_omega hZF I hω hsω hW
  obtain ⟨F, hF⟩ := he.symm hZF I
  obtain ⟨G, hG⟩ := ZF.exists_inclusionInjection hZF I hPW
  obtain ⟨H, hH⟩ := ZF.exists_compositionInjection hZF I hF.1 hG
  obtain ⟨K, hK⟩ := ZF.exists_compositionInjection hZF I hH hJ
  have hcO := oc_at_ordinal_l I hZF hc
  rcases hcO.trichotomy hZF.1 (hω.isOrdinal hZF) (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) c ω) with eq | hcω | hωc
  · exact (ZF.omega_not_le_finite_l I hZF hω n hn (hZF.1.eq_of_same_members c ω eq ▸ ⟨K, hK⟩)).elim
  · exact hcω
  · obtain ⟨L, hL⟩ := ZF.exists_inclusionInjection hZF I (hcO.transitive ω hωc)
    exact (ZF.omega_not_le_finite_l I hZF hω n hn (ZF.exists_compositionInjection hZF I hL hK)).elim

end YesMetaZFC.SetTheory
