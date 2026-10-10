import YesMetaZFC.SetTheory.InnerModel.Recursion.LocalCover

/-! # 在层内递归历史末尾追加一个真实计算

旧限制图及其见证原样复用。新行只需一个层内算子证书，随后有限扩大传递界。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rd_entry_insert_l {F G p a y : M.Domain} (hg : ∀ z, M.mem z G ↔ M.mem z F ∨ z = p)
    (hp : KPair_d M p a y) (b z : M.Domain) : Rd_entry_d b z G ↔ Rd_entry_d b z F ∨ (b = a ∧ z = y) := by
  constructor
  · rintro ⟨q, hq, hqG⟩
    rcases (hg q).mp hqG with hqF | he
    · exact Or.inl ⟨q, hq, hqF⟩
    · subst q; exact Or.inr (kpair_injective_l M hq hp)
  · rintro (⟨q, hq, hqF⟩ | ⟨rfl, rfl⟩)
    · exact ⟨q, hq, (hg q).mpr (Or.inl hqF)⟩
    · exact ⟨p, hp, (hg p).mpr (Or.inr rfl)⟩

theorem rd_insert_enclosed_l (hKP : M.Models KP) {C F p G : M.Domain} (hC : Rd_closed_d C)
    (hF : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem F T)
    (hp : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem p T) (hg : ∀ z, M.mem z G ↔ M.mem z F ∨ z = p) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem G T := by
  obtain ⟨P, hP⟩ := KP.exists_pair hKP p p
  have hPe := rd_fun_enclosed_l hKP hC hp hp hp (k := .pair) hP
  obtain ⟨Z, hZ⟩ := KP.exists_pair hKP F P
  have hZe := rd_fun_enclosed_l hKP hC hF hPe hF (k := .pair) hZ
  apply rd_fun_enclosed_l hKP hC hZe hZe hZe (k := .union)
  intro x; apply (hg x).trans
  constructor
  · rintro (hx | rfl)
    · exact ⟨F, (hZ F).mpr (Or.inl rfl), hx⟩
    · exact ⟨P, (hZ P).mpr (Or.inr rfl), (hP _).mpr (Or.inl rfl)⟩
  · rintro ⟨A, hA, hx⟩
    rcases (hZ A).mp hA with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr (((hP x).mp hx).elim id id)

theorem rc_local_extend_l (hKP : M.Models KP) {C A F T y : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) {n} {φ : S1_binary n} {ρ : Env M n} (h : Rc_cert_d φ ρ A F T)
    (hTC : M.mem T C) (hop : Si_cert_d C φ ρ F y) : Si_cert_d C (rc_value_s φ) ρ A y := by
  have hA : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem A B := ⟨T, hTC, h.trans, h.domain⟩
  have hF : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem F B := ⟨T, hTC, h.trans, h.graph⟩
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total A y
  have hP := rd_fun_enclosed_l hKP hC hA hop.enclosed_l hA (rd_opair_value_l hKP.1 hp)
  have hpC : M.mem p C := hP.elim fun B h => hc B h.1 p h.2.2
  obtain ⟨G, _, hg⟩ := rd_insert_closed_l hKP hC (hc T hTC F h.graph) hpC
  have hG := rd_insert_enclosed_l hKP hC hF hP hg
  obtain ⟨S, hSC, hs⟩ := rd_insert_closed_l hKP hC (hc T hTC A h.domain) (hc T hTC A h.domain)
  have st : M.TransitiveSet S := fun a ha b hb => (hs b).mpr (Or.inl (((hs a).mp ha).elim
    (fun ha => h.hereditary a ha b hb) (fun he => he ▸ hb)))
  have hS := rd_transitive_enclosed_l hKP hC hSC st
  obtain ⟨W, hWC, hwt, hyW, hw⟩ := hop
  obtain ⟨B, hBC, hb, tb, hL⟩ := rd_finite_enclosed_l hKP hC hTC h.trans [T, W] (by
    intro X hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx.elim (fun e => e ▸ rd_transitive_enclosed_l hKP hC hTC h.trans)
      (fun e => e ▸ rd_transitive_enclosed_l hKP hC hWC hwt))
  have hyB := hb W (hL W (by simp)) y hyW
  have entry := rd_entry_insert_l hg hp
  have fn : Fn0_d S B G := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      rcases (hg q).mp hq with hq | rfl
      · obtain ⟨a, ha, z, hz, hq⟩ := h.function.1 q hq
        exact ⟨a, (hs a).mpr (Or.inl ha), z, tb z hz, hq⟩
      · exact ⟨A, (hs A).mpr (Or.inr rfl), y, hyB, hp⟩
    · intro a ha
      rcases (hs a).mp ha with ha | he
      · obtain ⟨z, hz, he⟩ := h.function.2.1 a ha
        exact ⟨z, tb z hz, (entry a z).mpr (Or.inl he)⟩
      · subst a; exact ⟨y, hyB, (entry A y).mpr (Or.inr ⟨rfl, rfl⟩)⟩
    · intro a _ z _ v _ hz hv
      rcases (entry a z).mp hz with hz | hz <;> rcases (entry a v).mp hv with hv | hv
      · exact h.function.2.2 a (h.function.bound_l hz).1 z (h.function.bound_l hz).2 v (h.function.bound_l hv).2 hz hv
      · exact (KP.mem_irrefl_d hKP A (hv.1 ▸ (h.function.bound_l hz).1)).elim
      · exact (KP.mem_irrefl_d hKP A (hz.1 ▸ (h.function.bound_l hv).1)).elim
      · exact hz.2.trans hv.2.symm
  obtain ⟨D, hDC, hd⟩ := rc_local_cover_l hKP hC hBC hb st fn hS hG φ ρ (by
    intro a ha z haz
    rcases (hs a).mp ha with ha | he
    · have hazF : Rd_entry_d a z F := ((entry a z).mp haz).elim id
        (fun he => (KP.mem_irrefl_d hKP A (he.1 ▸ ha)).elim)
      obtain ⟨R, hRT, hr, hrφ⟩ := h.step a ha
      obtain ⟨w, hwT, hw⟩ := hrφ z (h.function.bound_l hazF).2 hazF
      have old := res0_restriction_l hKP h.function hr
      refine ⟨R, tb R hRT, w, tb w hwT, ⟨old.1, fun b v => ?_⟩, hw⟩
      exact (old.2 b v).trans (and_congr_right fun hba =>
        ⟨fun he => (entry b v).mpr (Or.inl he), fun he => ((entry b v).mp he).elim id
          (fun e => (KP.mem_irrefl_d hKP A (e.1 ▸ h.hereditary a ha b hba)).elim)⟩)
    · subst a
      have he : z = y := ((entry A z).mp haz).elim
        (fun he => (KP.mem_irrefl_d hKP A (h.function.bound_l he).1).elim) And.right
      subst z
      refine ⟨F, tb F h.graph, W, hL W (by simp), ⟨(fn0_function_l hKP h.function).1.1, fun b v => ?_⟩, hw⟩
      exact ⟨fun he => ⟨(h.function.bound_l he).1, (entry b v).mpr (Or.inl he)⟩,
        fun ⟨hbA, he⟩ => ((entry b v).mp he).elim id (fun e => (KP.mem_irrefl_d hKP A (e.1 ▸ hbA)).elim)⟩)
  exact hd.in_value_l hKP.1 hDC ((hs A).mpr (Or.inr rfl)) ((entry A y).mpr (Or.inr ⟨rfl, rfl⟩))

end YesMetaZFC.SetTheory.InnerModel
