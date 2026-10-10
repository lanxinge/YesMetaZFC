import YesMetaZFC.Model.SetTheory.Internal.PredicateSource
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Closure

/-! # 传递成员结构间的有界公式与自然数保持

空谓词把纯成员嵌入接到既有公式传输。ω 的 Δ₀ 遗传有限性刻画保证其像
仍是背景的同一个 ω，不要求模型在外部标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smem_d.empty_pred_l {c X R z : M.Domain} (hm : Smem_d I c X R)
    (hz : ∀ x, ¬ M.mem x z) : Spred_d I c X z R :=
  ⟨hm.1, fun x hx => (hz x hx).elim, fun x y => (hm.2 x y).trans (and_congr_right fun _ => and_congr_right fun _ =>
    ⟨Or.inl, fun h => h.elim id (fun h => (hz x h.2).elim)⟩)⟩

theorem smap_delta_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    {n} (φ : Formula 1 n) (hf : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, M.PairMember I (ρ.bound i) (η.bound i) q) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact spred_delta_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hq⟩ hX hY φ hf hd ρ η hp

theorem Smap_d.omega_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) : M.PairMember I ω ω q := by
  obtain ⟨ω₀, hω₀, finite⟩ := KPi.exists_omega_l (ZF.models_kpi_l hZF)
  have eq := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  obtain ⟨Ω, _, hωΩ⟩ := hq.1.1.2.2 ω hωX
  have transfer := smap_delta_l I hZF hω hX hY hm hn hq (n := 1) (omega0_m (.bound 0))
    (by simp -implicitDefEqProofs) (omega0_delta_l _) ⟨fun _ => ω, fun _ => ω⟩ ⟨fun _ => Ω, fun _ => Ω⟩ (fun _ => hωΩ)
  simp only [omega0_sat_l hZF.1] at transfer
  have hΩ := transfer.mp ⟨hω.1, fun n hn => (finite n).mp hn⟩
  have eq := hZF.1.eq_of_same_members Ω ω (fun n =>
    ⟨fun hn => KPi.n0_in_inductive_l (ZF.models_kpi_l hZF) hω.1 (hΩ.2 n hn), hω.2 Ω hΩ.1 n⟩)
  exact eq ▸ hωΩ

end YesMetaZFC.SetTheory.Internal
