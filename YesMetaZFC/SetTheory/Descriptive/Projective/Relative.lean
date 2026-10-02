import YesMetaZFC.SetTheory.Descriptive.Projective.Code
import YesMetaZFC.SetTheory.Descriptive.Trace

/-! # 相对射影点类的补对偶 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- Σ、Π 层的补对偶与对子空间取迹相容。 -/
theorem rclass_compl_l (hKP : M.Models KP) {ω A B J n X S P K L}
    (hX : M.MemberSubset X B) (hS : ∀ C, M.mem C S ↔ Ps_d I ω A B J n C)
    (hP : ∀ C, M.mem C P ↔ Pp_d I ω A B J n C) (hK : M.MemberSubset K X) (h : Cm_d X K L) :
    Rclass_d X S K ↔ Rclass_d X P L := by
  constructor
  · rintro ⟨C, hc, hk⟩
    obtain ⟨D, hd⟩ := cm_exists_l hKP B C
    obtain ⟨V, hv⟩ := tr_exists_l hKP X D
    have e := cm_unique_l hKP.1 (tr_compl_l hX hd hk hv) h
    exact ⟨D, (hP D).mpr ⟨C, (hS C).mp hc, hd⟩, e ▸ hv⟩
  · rintro ⟨D, hd, hl⟩
    obtain ⟨C, hc, hD⟩ := (hP D).mp hd
    obtain ⟨U, hu⟩ := tr_exists_l hKP X C
    have hcU := tr_compl_l hX hD hu hl
    have e := cm_unique_l hKP.1 (cm_symm_l (fun x hx => ((hu x).mp hx).1) hcU) (cm_symm_l hK h)
    exact ⟨C, (hS C).mpr hc, e ▸ hu⟩

end YesMetaZFC.SetTheory.Descriptive
