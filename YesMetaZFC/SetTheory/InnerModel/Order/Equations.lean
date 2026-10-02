import YesMetaZFC.SetTheory.InnerModel.Order.Coherence

/-! # 有序微层级的零、后继与极限方程 -/

namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem js_zero_l (hM : M.Models KPi) {a U R : M.Domain} (ha : ∀ b, ¬ M.mem b a) (h : Js_value_d a U R) :
    (∀ x, ¬ M.mem x U) ∧ (∀ p, ¬ M.mem p R) := by
  obtain ⟨Y, hu, hr, hy⟩ := js_value_equation_l hM h
  have empty A S (h : Rd_entry_d A S Y) : False := ((hy A S).mp h).elim fun b hb => ha b hb.1
  exact ⟨fun x hx => ((rp_union_entry_l hu x).mp hx).elim fun A h => h.elim fun S h => empty A S h.1,
    fun p hp => ((rp_union_entry_l hr p).mp hp).elim fun A h => h.elim fun S h => empty A S h.1⟩

theorem js_successor_l (hM : M.Models KPi) {a b U R V S : M.Domain} (ha : M.IsOrdinal a)
    (hs : M.SuccessorOf b a) (hU : Js_value_d a U R) (hV : Js_value_d b V S) : Rw_successor_d U R V S := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have hi := js_coherence_l hM ha hU
  obtain ⟨A, Q, hw⟩ := rw_successor_exists_l hKP U R
  have he := (rw_successor_correct_l hKP hi.2.1 hw).2.2
  obtain ⟨Y, hv, hr, hy⟩ := js_value_equation_l hM hV
  have bound B T (h : Rd_entry_d B T Y) : Rw_bound_d B T := by
    obtain ⟨_, _, _, _, _, h⟩ := (hy B T).mp h
    exact rw_successor_bounded_l h
  have top B T (h : Rd_entry_d B T Y) : Rw_end_d B T A Q := by
    obtain ⟨c, hc, D, F, hd, h⟩ := (hy B T).mp h
    rcases (hs c).mp hc with hc | hc
    · exact rw_end_trans_l (hi.2.2 c hc D F B T hd h) he
    · have hc := hKP.1.eq_of_same_members c a hc; subst c
      obtain ⟨rfl, rfl⟩ := js_value_unique_l hM hd hU
      obtain ⟨rfl, rfl⟩ := rw_successor_unique_l hKP.1 h hw
      exact rw_end_refl_l (fun _ _ h => (rw_successor_bounded_l hw).entry_l h)
  obtain ⟨rfl, rfl⟩ := rw_join_top_l hKP.1 hv hr bound ((hy A Q).mpr ⟨a, hs.predecessor_mem, U, R, hU, hw⟩) top
  exact hw

theorem js_limit_l (hM : M.Models KPi) {a U R : M.Domain} (ha : M.IsLimitOrdinal a) (h : Js_value_d a U R) (x : M.Domain) :
    M.mem x U ↔ ∃ b, M.mem b a ∧ ∃ V S, Js_value_d b V S ∧ M.mem x V := by
  constructor
  · intro hx
    obtain ⟨Y, hu, _, hy⟩ := js_value_equation_l hM h
    obtain ⟨A, Q, hA, hxA⟩ := (rp_union_entry_l hu x).mp hx
    obtain ⟨b, hb, V, S, hv, hw⟩ := (hy A Q).mp hA
    obtain ⟨c, hc, hbc⟩ := ha.2.2 b hb
    obtain ⟨W, T, ht⟩ := js_value_exists_l hM c
    exact ⟨c, hc, W, T, ht, ((js_coherence_l hM (ha.1.mem hc) ht).2.2 b hbc V S A Q hv hw).1 x hxA⟩
  · rintro ⟨b, hb, V, S, hv, hx⟩
    exact (js_end_l hM ha.1 hb hv h).1 x hx

theorem js_limit_order_l (hM : M.Models KPi) {a U R : M.Domain} (ha : M.IsLimitOrdinal a) (h : Js_value_d a U R) (p : M.Domain) :
    M.mem p R ↔ ∃ b, M.mem b a ∧ ∃ V S, Js_value_d b V S ∧ M.mem p S := by
  let hE := (KPi.models_iff_l.mp hM).1.1
  constructor
  · intro hp
    obtain ⟨Y, _, hr, hy⟩ := js_value_equation_l hM h
    obtain ⟨A, Q, hA, hpQ⟩ := (rp_union_entry_l hr p).mp hp
    obtain ⟨b, hb, V, S, hv, hw⟩ := (hy A Q).mp hA
    obtain ⟨c, hc, hbc⟩ := ha.2.2 b hb
    obtain ⟨W, T, ht⟩ := js_value_exists_l hM c
    exact ⟨c, hc, W, T, ht, ((js_coherence_l hM (ha.1.mem hc) ht).2.2 b hbc V S A Q hv hw).relation_subset_l hE
      (rw_successor_bounded_l hw) p hpQ⟩
  · rintro ⟨b, hb, V, S, hv, hp⟩
    exact (js_end_l hM ha.1 hb hv h).relation_subset_l hE (js_value_bounded_l hM hv) p hp

end YesMetaZFC.SetTheory.InnerModel
