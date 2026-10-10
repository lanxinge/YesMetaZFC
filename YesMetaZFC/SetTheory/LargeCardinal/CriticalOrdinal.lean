import YesMetaZFC.SetTheory.LargeCardinal.CriticalMeasure

/-! # 临界点严格超过内部 ω

自然数用已有 Δ₀ 谓词 N0 刻画。空集与后继保持排除有限临界点，
“全部成员为自然数”的保持及低于临界点的逐点固定排除 κ=ω。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_critical_omega_l (hZF : M.Models ZF) {ω X A Y B j κ k}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y) (hc : Wd_crit_d I X j κ k) : M.mem ω κ := by
  obtain ⟨v, hv, hn⟩ := KPi.exists_omega_l (ZF.models_kpi_l hZF)
  have he : v = ω := hZF.1.eq_of_same_members v ω (fun n => ⟨hv.2 ω hω.1 n, hω.2 v hv.1 n⟩)
  have hnat x : M.mem x ω ↔ KP.N0_d x := he ▸ hn x
  have hjκ := hc.image
  have hne := hc.moved
  have fixed := hc.fixed
  have hfin : ¬ M.mem κ ω := by
    intro hκ
    rcases ((hnat κ).mp hκ).2.1 with he | ⟨n, hnκ, hs⟩
    · have hk := (ed_empty_l I hZF hω h hX hY hjκ).mp he
      exact hne (hZF.1.eq_of_same_members κ k (fun x => iff_of_false (he x) (hk x)))
    · have tr := spred_delta_l I hZF hω h hX hY (n := 2) (KP.succ0_m (.bound 1) (.bound 0))
        (KP.succ0_m_freeClosed _ _ rfl rfl) (KP.succ0_delta_l ..)
        ⟨Fin.cases n (fun _ => κ), fun _ => n⟩ ⟨Fin.cases n (fun _ => k), fun _ => n⟩
        (Fin.cases (fixed n hnκ) (fun _ => hjκ))
      simp only [KP.succ0_sat_l hZF.1] at tr
      have hk : M.SuccessorOf k n := tr.mp hs
      exact hne (Structure.SuccessorOf.eq hZF.1 hs hk)
  have hωne : κ ≠ ω := by
    intro he
    have tr := spred_delta_l I hZF hω h hX hY (n := 1)
      (Formula.forallMem (.bound 0) (KP.n0_m .newest))
      (by simp -implicitDefEqProofs) (.forallMem _ (KP.n0_delta_l _))
      ⟨fun _ => κ, fun _ => κ⟩ ⟨fun _ => k, fun _ => k⟩ (fun _ => hjκ)
    simp only [Formula.satisfies_forallMem_iff, KP.n0_sat_l hZF.1] at tr
    have hk : ∀ x, M.mem x k → KP.N0_d x := tr.mp (fun x hx => (hnat x).mp (he ▸ hx))
    exact hne (hZF.1.eq_of_same_members κ k (fun x =>
      ⟨fun hx => (ed_member_l I hZF hω h hX hY (fixed x hx) hjκ).mp hx,
        fun hx => he.symm ▸ (hnat x).mpr (hk x hx)⟩))
  rcases Structure.IsOrdinal.trichotomy hZF.1 (hω.isOrdinal hZF) hc.ordinal
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with he | he | he
  · exact (hωne (hZF.1.eq_of_same_members ω κ he).symm).elim
  · exact he
  · exact (hfin he).elim

end YesMetaZFC.SetTheory.LargeCardinal
