import YesMetaZFC.Model.SetTheory.Internal.SeparationHull
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism

/-! # 初等映射精确搬运全内部公式的分离集

把指定集合在原关系中的成员方程编译成一条内部公式。初等性于是同时控制像外的新元素，
而不仅控制旧元素逐点的像；这是跨模型超幂复制所需的真值集合对应。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smap_d.separation_l (hZF : M.Models ZF) {ω c d X R Y S q E K F n r i f g D D' A A' : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hE : M.IsFunctionSpace I E ω X) (hK : M.IsFunctionSpace I K ω Y)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω)
    (hf : M.mem f E) (hg : M.mem g K) (assign : Smap_assign_d I ω q f g)
    (hD : M.PairMember I D D' q) (hA : M.PairMember I A A' q)
    (sep : Sr_sep_d I X R E F n r i f D A) : Sr_sep_d I Y S K F n r i g D' A' := by
  obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, _, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hi
  obtain ⟨m, G, k, build, read⟩ := sfm_sep_test_raw_l I hZF hω hF hr hi hs ht hsi hti
  obtain ⟨f₁, u₁, hf₁⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs (hq.1.1.input_mem_of_pairMember hD)
  obtain ⟨f₂, u₂, hf₂⟩ := senv_update_exists_l I hZF hf₁ ht (hq.1.1.input_mem_of_pairMember hA)
  obtain ⟨g₁, v₁, hg₁⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs (hq.1.1.output_mem_of_pairMember hD)
  obtain ⟨g₂, v₂, hg₂⟩ := senv_update_exists_l I hZF hg₁ ht (hq.1.1.output_mem_of_pairMember hA)
  have old := sr_sep_agree_l I hZF (R := R) (D := D) (A := A) hF hb hr hi hE hf ((hE f₂).mpr hf₂)
    (fun i x hi => (u₁.agree_l I hsb i x hi).trans (u₂.agree_l I htb i x hi))
  have next := sr_sep_agree_l I hZF (R := S) (D := D') (A := A') hF hb hr hi hK hg ((hK g₂).mpr hg₂)
    (fun i x hi => (v₁.agree_l I hsb i x hi).trans (v₂.agree_l I htb i x hi))
  have source := (read X R E f₂ D A hE ((hE f₂).mpr hf₂)
    ((u₂.2 s D).mpr (Or.inr ⟨hst, (u₁.2 s D).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
    ((u₂.2 t A).mpr (Or.inl ⟨rfl, rfl⟩))).mpr (old.mp sep)
  have target := (hq.ssat_l I hZF.1 hm hn build.program build.root hE hK
    ((hE f₂).mpr hf₂) ((hK g₂).mpr hg₂)
    ((assign.update_l I hq.1.1.1 hD u₁ v₁).update_l I hq.1.1.1 hA u₂ v₂)).mp source
  exact next.mpr ((read Y S K g₂ D' A' hK ((hK g₂).mpr hg₂)
    ((v₂.2 s D').mpr (Or.inr ⟨hst, (v₁.2 s D').mpr (Or.inl ⟨rfl, rfl⟩)⟩))
    ((v₂.2 t A').mpr (Or.inl ⟨rfl, rfl⟩))).mp target)

end YesMetaZFC.SetTheory.Internal
