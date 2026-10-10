import YesMetaZFC.SetTheory.LargeCardinal.IterationTag

/-! # 原模型与带标号分量的完整内部同构 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem it_tag_iso_l (hZF : M.Models ZF) {ω B Q A p R D H i c X S d Y V : M.Domain}
    (hω : M.IsOmega ω) (h : It_tag_d B Q A p R) (hq : Fn0_d D H Q)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i d Y V)
    (hc : Rd_entry_d i c Q) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X S) :
    ∃ e u, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c Y X e ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y u ∧
      (∀ a x, Rd_entry_d a x e ↔ M.mem a Y ∧ KPair_d M a i x) ∧
      ∀ x a, Rd_entry_d x a u ↔ M.mem a Y ∧ KPair_d M a i x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨a, ha⟩ := stage.1.2.1
  have hi := (h.projection.bound_l ((stage.2.1 a).mp ha).2).2
  let φ : BinarySchema 1 := { body := kpair_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have sat a x : φ.denote ρ a x ↔ KPair_d M a i x := kpair_sat_l M hZF.1 ..
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := X)
    (fun a ha => by
      obtain ⟨x, hp, _⟩ := h.label_l (((stage.2.1 a).mp ha).2)
      exact ⟨x, (sat a x).mpr hp⟩)
    (fun a _ x y hx hy => (kpair_injective_l M ((sat a x).mp hx) ((sat a y).mp hy)).2)
    (fun a x ha hx => (ep_at_read_l hq hc model.1).mp (h.at_l (((stage.2.1 a).mp ha).1) ((sat a x).mp hx)))
  have read a x : Rd_entry_d a x e ↔ M.mem a Y ∧ KPair_d M a i x :=
    (es a x).trans (and_congr_right fun _ => sat a x)
  have bij : M.IsSetBijectionFromTo I e Y X := by
    refine ⟨⟨he, fun a b x ha hb => I.unique (((read a x).mp ha).2) (((read b x).mp hb).2)⟩, fun x hx => ?_⟩
    obtain ⟨a, hp⟩ := I.total i x
    have ha := (h.nodes a).mpr ⟨i, x, hi, hp, c, X, S, hc, model.1, hx⟩
    have haY := (stage.2.1 a).mpr ⟨ha, (h.index a i x hp).mpr ha⟩
    exact ⟨a, haY, (read a x).mpr ⟨haY, hp⟩⟩
  have rel a b x y (ha : Rd_entry_d a x e) (hb : Rd_entry_d b y e) : Rd_entry_d a b V ↔ Rd_entry_d x y S := by
    obtain ⟨haY, hp⟩ := (read a x).mp ha
    obtain ⟨hbY, hq'⟩ := (read b y).mp hb
    have first : Rd_entry_d a b V ↔ Rd_entry_d a b R := (stage.2.2 a b).trans
      ⟨And.right ∘ And.right, fun hr => ⟨haY, hbY, hr⟩⟩
    have second : Rd_entry_d a b R ↔ Ep_rel_d Q i x y := (h.relation_l hp hq').trans
      ⟨And.right ∘ And.right, fun hr => ⟨((stage.2.1 a).mp haY).1, ((stage.2.1 b).mp hbY).1, hr⟩⟩
    exact first.trans (second.trans (ep_rel_read_l hq hc model.1))
  obtain ⟨u, hu, us⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  exact ⟨e, u, smap_of_iso_l I hZF hω stage.1 model bij rel,
    smap_of_iso_l I hZF hω model stage.1 hu (fun x y a b ha hb =>
      (rel a b x y ((us x a).mp ha) ((us y b).mp hb)).symm), read,
    fun x a => (us x a).trans (read a x)⟩

end YesMetaZFC.SetTheory.LargeCardinal
