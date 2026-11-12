import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax

/-! # 原档案保存时的源根切片

切片、内部 ω 及候选高度界全部属于保存时的源模型。原档案向新模型
推进时只保留这份源证书；实际五十四项码的唯一性保证每次读回同一界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_raw_saved_base_d (X₀ R₀ γ₀ D₀ C₀ X R w C U q p : M.Domain) : Prop :=
  ∃ γ V t, Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C p γ V t ∧ Rd_entry_d w V R ∧
    ∀ v : Fin 54 → M.Domain, Tg_saved_code_d X R w U q v →
      ∀ x, Rd_entry_d x γ R → Rd_entry_d x (v 15) R

/-- 同一次源切片和已保存码生产全部以后读取所需的候选界。 -/
theorem Tg_raw_saved_base_d.of_code_l (hE : Extensional M)
    {X₀ R₀ γ₀ D₀ C₀ X R w C U q p γ V t : M.Domain}
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C p γ V t)
    (omega : Rd_entry_d w V R) {v : Fin 54 → M.Domain}
    (code : Tg_saved_code_d X R w U q v)
    (bound : ∀ x, Rd_entry_d x γ R → Rd_entry_d x (v 15) R) :
    Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ X R w C U q p := by
  refine ⟨γ,V,t,slice,omega,?_⟩
  intro a ca x hx
  have eq : v 15 = a 15 := congrFun (code.inj_l I hE ca) 17
  exact eq ▸ bound x hx

end YesMetaZFC.SetTheory.LargeCardinal
