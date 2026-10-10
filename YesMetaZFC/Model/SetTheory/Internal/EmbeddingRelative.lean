import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax
import YesMetaZFC.Model.SetTheory.LevyReflection.Bounded

/-! # 拥有集合中的原公式沿外层初等图回拉

先对原公式作全量词有界化，再由外层图传输。反射只用于给定有限原公式，
不把外部逐公式保持当作全内部初等性的替代。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.reflected_l {ω b B R u U S π C V : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) (hCV : Rd_entry_d C V π)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (reflect : Lr_reflect_d φ V)
    (ρ : Env (rt_model_l C nc) n) (η : Env M n)
    (images : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i) π) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  have inhabited := nc
  obtain ⟨x⟩ := inhabited
  obtain ⟨c, Q, code⟩ := smdl_membership_l I hZF ⟨x.val, x.property⟩
  let σ : Env M n := ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩
  have small := sc_relative_sat_l I code ct nc φ hc ρ (σ.push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have tr := smap_delta_l I hZF hω bt ut mb mu hj (lr_rel_m φ .newest (fun i => .bound i.succ))
    (lr_rel_closed_l φ hc _ _ rfl (fun _ => rfl)) (lr_rel_delta_l ..)
    (σ.push C) (η.push V) (Fin.cases hCV images)
  exact small.symm.trans (tr.trans (reflect η (fun i =>
    (hj.member_l I hZF hω mb mu (images i) hCV).mp (ρ.bound i).property)).symm)

end YesMetaZFC.SetTheory.Internal
