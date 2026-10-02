import YesMetaZFC.SetTheory.InnerModel.Order.CoherenceSyntax

/-! # 每个内部微层都是良序，且前层始终是初段

归纳不变量同时保存所有前层微后继的端延拓。任意两项通过其内部序数索引
比较后可用归纳假设连接，因此极限处可直接应用端延拓链的并定理。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_coherence_l (hM : M.Models KPi) {a U R : M.Domain} (ha : M.IsOrdinal a) (h : Js_value_d a U R) :
    M.TransitiveSet U ∧ M.IsSetCodedWellOrder (kp_pair_l (KPi.models_iff_l.mp hM).1) R U ∧
      ∀ b, M.mem b a → ∀ A S V T, Js_value_d b A S → Rw_successor_d A S V T → Rw_end_d V T U R := by
  let hKP := (KPi.models_iff_l.mp hM).1
  apply (js_coherence_sat_l hKP (js_env_l a) a).mp
    ((KPi.models_iff_l.mp hM).2 js_coherence_s (js_env_l a) ?_ a) ha U R h
  intro b ih
  apply (js_coherence_sat_l hKP (js_env_l a) b).mpr
  intro hb V S hv
  have prev c hc A Q (h : Js_value_d c A Q) :=
    (js_coherence_sat_l hKP (js_env_l a) c).mp (ih c hc) (hb.mem hc) A Q h
  obtain ⟨Y, hu, hr, hy⟩ := js_value_equation_l hM hv
  have good A Q (h : Rd_entry_d A Q Y) : M.TransitiveSet A ∧ M.IsSetCodedWellOrder (kp_pair_l hKP) Q A := by
    obtain ⟨c, hc, D, F, hd, hw⟩ := (hy A Q).mp h
    have hi := prev c hc D F hd
    exact ⟨rw_successor_transitive_l hKP hi.1 hw, (rw_successor_correct_l hKP hi.2.1 hw).2.1⟩
  have bound A Q (h : Rd_entry_d A Q Y) x y (hxy : Rd_entry_d x y Q) : M.mem x A ∧ M.mem y A := by
    obtain ⟨_, _, _, _, _, hw⟩ := (hy A Q).mp h
    exact (rw_successor_bounded_l hw).entry_l hxy
  have chain A Q B T (hA : Rd_entry_d A Q Y) (hB : Rd_entry_d B T Y) :
      Rw_end_d A Q B T ∨ Rw_end_d B T A Q := by
    obtain ⟨c, hc, D, F, hd, hw⟩ := (hy A Q).mp hA
    obtain ⟨d, hdB, G, H, hg, hw'⟩ := (hy B T).mp hB
    rcases hb.wellOrder.linear.compare c hc d hdB with he | hcd | hdc
    · have he := hKP.1.eq_of_same_members c d he; subst d
      obtain ⟨rfl, rfl⟩ := js_value_unique_l hM hd hg
      obtain ⟨rfl, rfl⟩ := rw_successor_unique_l hKP.1 hw hw'
      exact Or.inl (rw_end_refl_l (bound _ _ hA))
    · have hi := prev d hdB G H hg
      exact Or.inl (rw_end_trans_l (hi.2.2 c hcd D F A Q hd hw) (rw_successor_correct_l hKP hi.2.1 hw').2.2)
    · have hi := prev c hc D F hd
      exact Or.inr (rw_end_trans_l (hi.2.2 d hdc G H B T hg hw') (rw_successor_correct_l hKP hi.2.1 hw).2.2)
  have wo := rw_join_wellorder_l hKP hu hr (fun A Q h => (good A Q h).2) bound chain
  refine ⟨?_, wo.1, fun c hc A Q B T hA hw => rw_join_end_l hu hr bound chain ((hy B T).mpr ⟨c, hc, A, Q, hA, hw⟩)⟩
  intro x hx y hyx
  obtain ⟨A, Q, hA, hxA⟩ := (rp_union_entry_l hu x).mp hx
  exact (rp_union_entry_l hu y).mpr ⟨A, Q, hA, (good A Q hA).1 x hxA y hyx⟩

theorem js_value_bounded_l (hM : M.Models KPi) {a U R : M.Domain} (h : Js_value_d a U R) : Rw_bound_d U R := by
  obtain ⟨Y, hu, hr, hy⟩ := js_value_equation_l hM h
  intro p hp
  obtain ⟨A, S, hAS, hpS⟩ := (rp_union_entry_l hr p).mp hp
  obtain ⟨_, _, _, _, _, hw⟩ := (hy A S).mp hAS
  obtain ⟨x, hx, y, hy, hp⟩ := rw_successor_bounded_l hw p hpS
  exact ⟨x, (rp_union_entry_l hu x).mpr ⟨A, S, hAS, hx⟩,
    y, (rp_union_entry_l hu y).mpr ⟨A, S, hAS, hy⟩, hp⟩

theorem js_end_l (hM : M.Models KPi) {a b U R V S : M.Domain} (ha : M.IsOrdinal a) (hb : M.mem b a)
    (hu : Js_value_d b U R) (hv : Js_value_d a V S) : Rw_end_d U R V S := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨A, Q, h⟩ := rw_successor_exists_l hKP U R
  exact rw_end_trans_l (rw_successor_correct_l hKP (js_coherence_l hM (ha.mem hb) hu).2.1 h).2.2
    ((js_coherence_l hM ha hv).2.2 b hb U R A Q hu h)

theorem js_value_mem_l (hM : M.Models KPi) {a b U R V S : M.Domain} (ha : M.IsOrdinal a) (hb : M.mem b a)
    (hu : Js_value_d b U R) (hv : Js_value_d a V S) : M.mem U V := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨A, Q, h⟩ := rw_successor_exists_l hKP U R
  obtain ⟨B, hbU, hbA⟩ := (rw_successor_correct_l hKP (js_coherence_l hM (ha.mem hb) hu).2.1 h).1
  exact ((js_coherence_l hM ha hv).2.2 b hb U R A Q hu h).1 U ((hbA U).mpr (Or.inl hbU.predecessor_mem))

end YesMetaZFC.SetTheory.InnerModel
