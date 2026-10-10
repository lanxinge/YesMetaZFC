import YesMetaZFC.SetTheory.InnerModel.Recursion.LocalCover
import YesMetaZFC.SetTheory.InnerModel.Separation.Bounded

/-! # 层内递归证书对传递前段的限制 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rc_local_restrict_l (hKP : M.Models KP) {C A F T D : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) {n} {φ : S1_binary n} {ρ : Env M n} (h : Rc_cert_d φ ρ A F T)
    (hTC : M.mem T C) (hd : M.TransitiveSet D) (hDA : M.MemberSubset D A)
    (hD : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem D B) :
    ∃ G B, M.mem B C ∧ Rc_cert_d φ ρ D G B ∧ M.IsRestrictionOf (kp_pair_l hKP) G F D := by
  obtain ⟨U, hUC, hu, tu, hL⟩ := rd_finite_enclosed_l hKP hC hTC h.trans [D, T] (by
    intro X hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx.elim (fun e => e ▸ hD) (fun e => e ▸ rd_transitive_enclosed_l hKP hC hTC h.trans))
  let η : Env M 2 := ⟨Fin.cases T (fun _ => D), fun _ => D⟩
  let ψ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2) (kpair0_m (.bound 2) (.bound 1) .newest))
    delta0 := .existsMem _ (.existsMem _ (kpair0_delta_l ..)) }
  have sat p : ψ.toUnarySchema.denote η p ↔ ∃ a, M.mem a D ∧ ∃ y, M.mem y T ∧ KPair_d M p a y := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_existsMem_iff, kpair0_sat_l hKP.1]; rfl
  obtain ⟨G, hGC, hg⟩ := rd_separation_l hKP hC hc hUC hu ψ η
    (Fin.cases (hL T (by simp)) (fun _ => hL D (by simp))) (tu F h.graph)
  have gm p : M.mem p G ↔ M.mem p F ∧ ∃ a, M.mem a D ∧ ∃ y, M.mem y T ∧ KPair_d M p a y :=
    (hg p).trans (and_congr_right fun _ => sat p)
  have gr : Res0_d G F D T := by
    refine ⟨fun p hp => ((gm p).mp hp).1, fun p hp => ((gm p).mp hp).2, fun a ha y hy => ?_⟩
    exact ⟨fun ⟨p, hp, hpG⟩ => ⟨p, hp, ((gm p).mp hpG).1⟩,
      fun ⟨p, hp, hpF⟩ => ⟨p, hp, (gm p).mpr ⟨hpF, a, ha, y, hy, hp⟩⟩⟩
  have res := res0_restriction_l hKP h.function gr
  have fn : Fn0_d D T G := by
    refine ⟨gr.2.1, fun a ha => ?_, fun a ha y hy z hz hxy hxz => ?_⟩
    · obtain ⟨y, hy, he⟩ := h.function.2.1 a (hDA a ha)
      exact ⟨y, hy, (res.2 a y).mpr ⟨ha, he⟩⟩
    · exact h.function.2.2 a (hDA a ha) y hy z hz ((res.2 a y).mp hxy).2 ((res.2 a z).mp hxz).2
  obtain ⟨V, hVC, hv, _, hGV⟩ := rd_bounded_enclosed_l hKP hC hTC h.trans hGC
    (fun p hp => h.trans F h.graph p (gr.1 p hp))
  obtain ⟨B, hBC, hb⟩ := rc_local_cover_l hKP hC hTC h.trans hd fn hD ⟨V, hVC, hv, hGV⟩ φ ρ (by
    intro a ha y hay
    obtain ⟨R, hRT, hr, hs⟩ := h.step a (hDA a ha)
    have hayF := ((res.2 a y).mp hay).2
    obtain ⟨w, hwT, hw⟩ := hs y (h.function.bound_l hayF).2 hayF
    have old := res0_restriction_l hKP h.function hr
    refine ⟨R, hRT, w, hwT, ⟨old.1, fun b z => ?_⟩, hw⟩
    exact (old.2 b z).trans (and_congr_right fun hb =>
      ⟨fun hz => (res.2 b z).mpr ⟨hd a ha b hb, hz⟩, fun hz => ((res.2 b z).mp hz).2⟩))
  exact ⟨G, B, hBC, hb, res⟩

end YesMetaZFC.SetTheory.InnerModel
