import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.TarskiVaughtSyntax
import YesMetaZFC.SetTheory.CountableChain

/-! # 从有限参数司寇伦闭性到完整内部见证闭性

把任意赋值限制到程序的内部有限坐标界，再按基点延拓。真值一致性允许在该
有限参数列上选择见证，随后把见证搬回原完整赋值。整个转换只需 ZF。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ssk_full_l (hZF : M.Models ZF) {ω c X R u C N} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) (hC : Scode_d I ω C) (hN : M.MemberSubset N X) (hu : M.mem u N)
    (hs : Ssk_closed_d I ω c X u C N) : Stv_d I ω c X C N := by
  rintro a i f ha hi hf ⟨x, g, hx, hg, ht⟩
  obtain ⟨n, F, k, hCode⟩ := (hC a).mp ha
  obtain ⟨b, hb, hBound⟩ := sbound_exists_l I hZF hω hCode.2.1
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have agree {p q} (hp : M.IsSetFunctionFromTo I p ω X) (hq : M.IsSetFunctionFromTo I q ω X)
      (he : Senv_agree_d I b p q) : Satisfies_d I ω c a p ↔ Satisfies_d I ω c a q :=
    (satisfies_decode_l I hZF.1 hM hCode hE).trans
      ((ssat_agree_l I hZF hCode.2.1 hBound hE hCode.2.2 ((hE p).mpr hp) ((hE q).mpr hq) he).trans
        (satisfies_decode_l I hZF.1 hM hCode hE).symm)
  obtain ⟨s, hRestr⟩ := ZF.exists_restriction hZF I f b
  have hbw := hω.transitive hZF b hb
  have hsN := hRestr.isSetFunctionFromTo hf hbw
  obtain ⟨f₀, hFill, hf₀⟩ := senv_fill_exists_l I hZF (ω := ω) hsN hu
  have he := senv_fill_agree_l I hbw hRestr hFill
  have hfX := hf.mono_target_l I hN
  have hf₀X := hf₀.mono_target_l I hN
  obtain ⟨g₀, hg₀, hG₀⟩ := senv_update_exists_l I hZF hf₀X hi hx
  have ht₀ := (agree (hg.function_l I hfX hi hx) hG₀ (he.update_l I hg hg₀)).mp ht
  obtain ⟨y, hy, hys⟩ := hs a i b s ha hi hb hsN
    ⟨x, hx, b, f₀, g₀, hb, hsN.mono_target_l I hN, hFill, hg₀, ht₀⟩
  obtain ⟨q₀, hq₀, hQ₀⟩ := senv_update_exists_l I hZF hf₀ hi hy
  have hyt := (ssk_wit_decode_l I hZF.1 hb (hsN.mono_target_l I hN) hFill hq₀).mp hys
  obtain ⟨q, hq, hQ⟩ := senv_update_exists_l I hZF hf hi hy
  exact ⟨y, q, hy, hq,
    (agree (hQ.mono_target_l I hN) (hQ₀.mono_target_l I hN) (he.update_l I hq hq₀)).mpr hyt⟩

end YesMetaZFC.SetTheory.Internal
