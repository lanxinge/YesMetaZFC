import YesMetaZFC.Model.Forcing.Stage.Reduction

/-! # 完全嵌入下泛型滤子的回拉

把源集合的阶段像向下闭包为实际目标集合。约减保证所需稠密性，包括两个源
条件的共同加强要求，由此直接验证回拉滤子的全部泛型条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {P R z Q S w F : M.Domain}

def Pull_generic_d (M : SetTheory.Structure.{u}) (F : M.Domain) (V : M.Domain → Prop) (p : M.Domain) : Prop :=
  ∃ q, Entry_d M p q F ∧ V q

private theorem image_down_set_l (hZF : M.Models ZF) (F Q S D : M.Domain) : ∃ E, ∀ x,
    M.mem x E ↔ M.mem x Q ∧ ∃ p y, M.mem p D ∧ Entry_d M p y F ∧ Entry_d M x y S := by
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push S).push D
  let φ : UnarySchema 3 := {
    body := .existsE (.existsE (.conj (.mem (.bound 1) (.bound 3))
      (.conj (entry_m (.bound 1) .newest (.bound 5)) (entry_m (.bound 2) .newest (.bound 4))))) }
  obtain ⟨E, hE⟩ := ZF.separation_exists_d hZF φ ρ Q
  refine ⟨E, fun x => (hE x).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hZF.1]
  rfl

private theorem image_down_dense_l (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (h : Reg_embed_d M P R z Q S w F) {p q D E} (hpq : Entry_d M p q F)
    (hE : ∀ x, M.mem x E ↔ M.mem x Q ∧ ∃ a b, M.mem a D ∧ Entry_d M a b F ∧ Entry_d M x b S)
    (hd : Dense_d M P R z (fun a => M.mem a D) p) : Dense_d M Q S w (fun x => M.mem x E) q := by
  intro x hx
  obtain ⟨r, hr, hred⟩ := reg_reduce_below_l O L h hx.1 hx.2.1 hpq hx.2.2
  obtain ⟨a, ha, haD⟩ := hd r hr
  obtain ⟨b, hab⟩ := h.total a ha.1 ha.2.1
  obtain ⟨y, hy, hyb⟩ := hred a b hab ha.2.2
  exact ⟨y, hy, (hE y).mpr ⟨hy.1, a, b, haD, hab, hyb⟩⟩

/-- 目标泛型沿实际完全嵌入图回拉，自动满足全部源模型内稠密要求。 -/
theorem reg_generic_l (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (hZF : M.Models ZF) (h : Reg_embed_d M P R z Q S w F)
    {V : M.Domain → Prop} (hV : Generic_d M Q S w V) :
    Generic_d M P R z (Pull_generic_d M F V) := by
  have accept {x D E} (hx : V x)
      (hE : ∀ x, M.mem x E ↔ M.mem x Q ∧ ∃ p y, M.mem p D ∧ Entry_d M p y F ∧ Entry_d M x y S)
      (hd : Dense_d M Q S w (fun y => M.mem y E) x) : ∃ p, Pull_generic_d M F V p ∧ M.mem p D := by
    obtain ⟨q, hq, hqE⟩ := hV.meets x hx E hd
    obtain ⟨_, p, y, hpD, hpy, hqy⟩ := (hE q).mp hqE
    exact ⟨p, ⟨y, hpy, hV.upward q y hq (h.domain p y hpy).2.2.1 hqy⟩, hpD⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨q, hpq, _⟩
    exact ⟨(h.domain p q hpq).1, (h.domain p q hpq).2.1⟩
  · obtain ⟨x, hx⟩ := hV.inhabited
    obtain ⟨E, hE⟩ := image_down_set_l hZF F Q S P
    obtain ⟨p, hp, _⟩ := accept hx hE (by
      intro q hq
      obtain ⟨r, hr, hrz, hred⟩ := h.reduction q hq.1 hq.2.1
      obtain ⟨v, hrv⟩ := h.total r hr hrz
      obtain ⟨y, hy, hyv⟩ := hred r v hrv (O.refl r hr)
      exact ⟨y, hy, (hE y).mpr ⟨hy.1, r, v, hr, hrv, hyv⟩⟩)
    exact ⟨p, hp⟩
  · rintro p q ⟨x, hpx, hx⟩ hq hpq
    have hqz : q ≠ z := fun hz => (h.domain p x hpx).2.1 (O.zero p (h.domain p x hpx).1 (hz ▸ hpq))
    obtain ⟨y, hqy⟩ := h.total q hq hqz
    exact ⟨y, hqy, hV.upward x y hx (h.domain q y hqy).2.2.1 ((h.order p q x y hpx hqy).mpr hpq)⟩
  · rintro p q ⟨x, hpx, hx⟩ ⟨y, hqy, hy⟩
    obtain ⟨u, hu, hux, huy⟩ := hV.directed x y hx hy
    let ρ : Env M 5 := ((((⟨fun _ => P, fun _ => P⟩ : Env M 1).push R).push z).push p).push q
    let φ : UnarySchema 5 := {
      body := .conj (below_m (.bound 5) (.bound 4) (.bound 3) .newest (.bound 2))
        (entry_m .newest (.bound 1) (.bound 4)) }
    obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ P
    have hD r : M.mem r D ↔ Below_d M P R z r p ∧ Entry_d M r q R := by
      refine (hD' r).trans ?_
      simp only [φ, Formula.satisfies_conj_iff, below_sat_l M hZF.1, entry_sat_l M hZF.1]
      exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
    obtain ⟨E, hE⟩ := image_down_set_l hZF F Q S D
    obtain ⟨r, hr, hrD⟩ := accept hu hE (by
      intro v hv
      have hvx := L.trans v u x hv.1 (hV.proper u hu).1 (h.domain p x hpx).2.2.1 hv.2.2 hux
      have hvy := L.trans v u y hv.1 (hV.proper u hu).1 (h.domain q y hqy).2.2.1 hv.2.2 huy
      obtain ⟨a, ha, hred⟩ := reg_reduce_below_l O L h hv.1 hv.2.1 hpx hvx
      obtain ⟨b, hb, hbq, hred'⟩ := red_refine_l O L h hv.1 ha.1 ha.2.1 hred hqy hvy
      have hbD := (hD b).mpr ⟨below_trans_l O (h.domain p x hpx).1 hb ha, hbq⟩
      obtain ⟨c, hbc⟩ := h.total b hb.1 hb.2.1
      obtain ⟨j, hj, hjc⟩ := hred' b c hbc (O.refl b hb.1)
      exact ⟨j, hj, (hE j).mpr ⟨hj.1, b, c, hbD, hbc, hjc⟩⟩)
    exact ⟨r, hr, ((hD r).mp hrD).1.2.2, ((hD r).mp hrD).2⟩
  · rintro p ⟨q, hpq, hq⟩ D hd
    obtain ⟨E, hE⟩ := image_down_set_l hZF F Q S D
    exact accept hq hE (image_down_dense_l O L h hpq hE hd)

end YesMetaZFC.Model.Forcing.Internal
