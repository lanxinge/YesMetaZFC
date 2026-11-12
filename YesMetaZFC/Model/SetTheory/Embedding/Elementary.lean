import YesMetaZFC.Model.SetTheory.Internal.TarskiVaught
import YesMetaZFC.Model.SetTheory.Internal.Theory

/-! # 内部初等性的装配、复合与理论保持

有限参数司寇伦闭性通过已证有限支撑自动提升为完整内部初等性。初等关系
可复合，并把源结构所满足的每个内部编码理论传给目标结构。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 已有司寇伦闭包自动获得实际诱导结构码及完整内部初等性；此步仅需 ZF。 -/
theorem selem_of_skolem_l (hZF : M.Models ZF) {ω c X R u C N} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hC : Scode_d I ω C) (hN : M.MemberSubset N X) (hu : M.mem u N)
    (hs : Ssk_closed_d I ω c X u C N) : ∃ d S, Ssub_d I c d X R N S ∧ Selem_d I ω c d := by
  obtain ⟨d, S, hS⟩ := smdl_substructure_l I hZF hM hN ⟨u, hu⟩
  exact ⟨d, S, hS, selem_of_tv_l I hZF hS hC (ssk_full_l I hZF hω hM hC hN hu hs)⟩

theorem selem_refl_l {ω c X R C} (hM : Smdl_d I c X R) (hC : Scode_d I ω C) : Selem_d I ω c c := by
  refine ⟨X, R, X, R, C, ⟨hM, hM, fun _ h => h, fun x y => ?_⟩, hC, fun _ _ _ _ => Iff.rfl⟩
  exact ⟨fun h => ⟨(hM.2.2.2 x y h).1, (hM.2.2.2 x y h).2, h⟩, And.right ∘ And.right⟩

theorem Selem_d.trans_l {ω c d e} (h : Selem_d I ω c d) (k : Selem_d I ω d e) : Selem_d I ω c e := by
  obtain ⟨X, R, N, S, C, hS, hC, hs⟩ := h
  obtain ⟨Y, T, B, U, D, hU, hD, hu⟩ := k
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hS.target hU.source
  refine ⟨X, R, B, U, C, ⟨hS.source, hU.target, fun x hx => hS.subset x (hU.subset x hx), ?_⟩,
    hC, fun a f ha hf => (hs a f ha (hf.mono_target_l I hU.subset)).trans
      (hu a f ((hD a).mpr ((hC a).mp ha)) hf)⟩
  intro x y
  exact (hU.relation x y).trans ⟨fun h => ⟨h.1, h.2.1, ((hS.relation x y).mp h.2.2).2.2⟩,
    fun h => ⟨h.1, h.2.1, (hS.relation x y).mpr ⟨hU.subset x h.1, hU.subset y h.2.1, h.2.2⟩⟩⟩

/-- 任意实际内部理论集合的模型性沿内部初等子结构保持。 -/
theorem Selem_d.models_l (hZF : M.Models ZF) {ω c d T} (he : Selem_d I ω c d)
    (ht : Smodels_d I ω c T) : Smodels_d I ω d T := by
  obtain ⟨X, R, N, S, C, hS, hC, he⟩ := he
  obtain ⟨Y, Q, E, D, hM, hE, hD, hTD, hT⟩ := ht
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hS.source hM
  obtain ⟨F, hF⟩ := ZF.exists_functionSpace hZF I ω N
  have hc : M.MemberSubset T C := fun a ha => (hC a).mpr ((hD a).mp (hTD a ha))
  refine ⟨N, S, F, C, hS.target, hF, hC, hc, fun a ha f hf => ?_⟩
  have hn := (hF f).mp hf
  exact (he a f (hc a ha) hn).mp (hT a ha f ((hE f).mpr (hn.mono_target_l I hS.subset)))

end YesMetaZFC.SetTheory.Internal
