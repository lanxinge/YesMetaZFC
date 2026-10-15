import YesMetaZFC.Model.Forcing.Internal.Ground.FiniteSequence
import YesMetaZFC.SetTheory.Descriptive.Prefix

/-! # 新无限列的每个内部有限前缀都有真实地原像 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem ground_prefix_l {ω A k : M.Domain} {f : N.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (ff : N.IsSetFunctionFromTo J f (e ω) (e A)) (hk : M.mem k ω) :
    ∃ s, M.IsSetFunctionFromTo I s k A ∧ N.IsRestrictionOf J (e s) f (e k) := by
  obtain ⟨F, space⟩ := ZF.fseq_space_exists_l I hM hw A
  obtain ⟨s, fs, cut, _⟩ := ds_prefix_l J hN hw' ff ((image_member_l e hi he).mpr hk)
  have hs := (image_fseq_l hM hN e hi he hw hw' space s).mpr ⟨e k, (image_member_l e hi he).mpr hk, fs⟩
  obtain ⟨s₀, hs₀, eq⟩ := (he F s).mp hs; subst s
  obtain ⟨n, _, fn⟩ := (space s₀).mp hs₀
  have fn' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fn
  have eq := hi (fn'.2.1.eq hN.1 fs.2.1); subst n
  exact ⟨s₀, fn, cut⟩

end YesMetaZFC.Model.Forcing.Internal
