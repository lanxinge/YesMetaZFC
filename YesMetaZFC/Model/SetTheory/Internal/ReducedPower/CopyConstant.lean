import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Constant
import YesMetaZFC.Model.SetTheory.Internal.SourceTransport

/-! # 常值代表在源映射下的实际保持 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_constant_image_l {ω c d X R Y S π D D' x x' f f' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hD : Rd_entry_d D D' π) (hx : Rd_entry_d x x' π) (hf : Rd_entry_d f f' π)
    (constant : Rs_const_d D x f) : Rs_const_d D' x' f' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hπ (n := 3)
    (Formula.forallMem (.bound 2) (rd_entry0_m .newest (.bound 2) (.bound 1)))
    (by simp -implicitDefEqProofs) (.forallMem _ (rd_entry0_delta_l ..))
    ⟨Fin.cases f (Fin.cases x (fun _ => D)), fun _ => D⟩
    ⟨Fin.cases f' (Fin.cases x' (fun _ => D')), fun _ => D'⟩ (Fin.cases hf (Fin.cases hx (fun _ => hD)))
  simp only [Formula.satisfies_forallMem_iff, rd_entry0_sat_l hZF.1] at tr
  exact tr.mp constant

end YesMetaZFC.SetTheory.Internal
