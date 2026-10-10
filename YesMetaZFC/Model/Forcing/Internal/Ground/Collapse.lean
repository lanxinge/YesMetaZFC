import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.SetTheory.Collapse.RelationExistence
import YesMetaZFC.SetTheory.InnerModel.HOD.Relative

/-! # 地嵌入下的坍塌恢复

内部良基性向地模型回拉，实际坍塌图沿成员满嵌入向前保持。再用目标模型内部
的坍塌唯一性识别两个值；源图全部值的可定义性给出遗传可定义的地原像。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
  (hP : ∀ a b, ∃ p, Pair_d M p a b) (hN : Extensional N)
include hi he hP hN

omit hi hP hN in
theorem image_wf_reflect_l {X R} (h : Wf_rel_d (e X) (e R)) : Wf_rel_d X R := by
  intro Y hY hn
  obtain ⟨a, ha⟩ := hn
  obtain ⟨y, hy, hm⟩ := h (e Y) (fun x hx => by
    obtain ⟨b, hb, rfl⟩ := (he Y x).mp hx
    exact (he X (e b)).mpr ⟨b, hY b hb, rfl⟩) ⟨e a, (he Y (e a)).mpr ⟨a, ha, rfl⟩⟩
  obtain ⟨b, hb, rfl⟩ := (he Y y).mp hy
  exact ⟨b, hb, fun c hc ⟨p, hp, hpR⟩ => hm (e c) ((he Y (e c)).mpr ⟨c, hc, rfl⟩)
    ⟨e p, image_kpair_l e he hp, (he R (e p)).mpr ⟨p, hpR, rfl⟩⟩⟩

theorem image_collapse_graph_l {X R F} (h : Wc_graph_d X R F) : Wc_graph_d (e X) (e R) (e F) := by
  have entry a x := image_entry_iff_l e hi he hP hN a x F
  have rel a b := image_entry_iff_l e hi he hP hN a b R
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := (he F p).mp hp
    obtain ⟨a, x, hq⟩ := h.1 q hq
    exact ⟨e a, e x, image_kpair_l e he hq⟩
  · intro a x hax
    obtain ⟨b, y, hby, rfl, rfl⟩ := (image_entries_l e he h.1 a x).mp hax
    obtain ⟨hb, hs⟩ := h.2 b y hby
    refine ⟨(he X (e b)).mpr ⟨b, hb, rfl⟩, ?_, fun z => ?_⟩
    · intro c hc hcb
      obtain ⟨a, ha, rfl⟩ := (he X c).mp hc
      obtain ⟨w, haw⟩ := hs.1 a ha ((rel a b).mpr hcb)
      exact ⟨e w, (entry a w).mp haw⟩
    · constructor
      · intro hz
        obtain ⟨w, hw, rfl⟩ := (he y z).mp hz
        obtain ⟨a, ha, hab, haw⟩ := (hs.2 w).mp hw
        exact ⟨e a, (he X (e a)).mpr ⟨a, ha, rfl⟩, (rel a b).mp hab, (entry a w).mp haw⟩
      · rintro ⟨c, hc, hcb, hcz⟩
        obtain ⟨a, ha, rfl⟩ := (he X c).mp hc
        obtain ⟨a', w, haw, haa, hwz⟩ := (image_entries_l e he h.1 (e a) z).mp hcz
        have eq := hi haa
        subst a'
        exact (he y z).mpr ⟨w, (hs.2 w).mpr ⟨a, ha, (rel a b).mpr hcb, haw⟩, hwz⟩

omit hP hN in
/-- 恢复的代码载体和关系均为 OD[A] 时，总坍塌图的全部值形成遗传 OD[A] 容器。 -/
theorem collapse_hb_recover_l (hZF : M.Models ZF) (hZN : N.Models ZF) {A C R T F}
    (hC : Ob_d A C) (hR : Ob_d A R) (hc : ∀ a, M.mem a C → Ob_d A a)
    (fn : Fn0_d (e C) T F) (hg : Wc_graph_d (e C) (e R) F) {x : N.Domain}
    (hx : ∃ a, Rd_entry_d a x F) : ∃ y, Hb_d A y ∧ e y = x := by
  have hwN := wf_of_collapse_l hZN fn hg
  have hw := image_wf_reflect_l e he hwN
  obtain ⟨S, G, hf, hG, range, trans⟩ := wc_collapse_l hZF hw
  have hGI := image_collapse_graph_l e hi he (KP.exists_pair (ZF.modelsKP hZF)) hZN.1 hG
  have values a y (hay : Rd_entry_d a y G) : Ob_d A y := by
    let ρ : Env M 3 := ((⟨fun _ => C, fun _ => C⟩ : Env M 1).push R).push a
    let φ : UnarySchema 3 := { body := wc_value_m (.bound 3) (.bound 2) (.bound 1) .newest }
    have hy : Wc_value_d C R a y := ⟨G, hG, hay⟩
    exact ob_closed_l hZF A φ ρ (Fin.cases (hc a (hf.bound_l hay).1) (Fin.cases hR (fun _ => hC)))
      (fun z => (wc_value_sat_l hZF.1 (ρ.push z) _ _ _ _).trans
        ⟨fun hz => wc_value_unique_l hZF hw hz hy, fun he => he.symm ▸ hy⟩)
  obtain ⟨a, hax⟩ := hx
  obtain ⟨b, hb, hba⟩ := (he C a).mp (fn.bound_l hax).1
  obtain ⟨y, hy, hby⟩ := hf.2.1 b hb
  have hiy := (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hZF)) hZN.1 b y G).mp hby
  have eq := wc_value_unique_l hZN hwN ⟨e G, hGI, hba ▸ hiy⟩ ⟨F, hg, hax⟩
  exact ⟨y, ⟨S, trans, hy, fun z hz =>
    (range z).mp hz |>.elim fun a haz => oa_bracket_l.mpr (values a z haz)⟩, eq⟩

end YesMetaZFC.Model.Forcing.Internal
