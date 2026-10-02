import YesMetaZFC.SetTheory.InnerModel.Order.Equations

/-! # 微层级极限层的 rud 封闭性

有限多个参数先放进同一个较早层，再取一次微后继。极限索引保证该后继仍被
当前层容纳；这里不要求极限层满足收集或可容许性。
-/

namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem js_finite_stage_l (hM : M.Models KPi) {a U R : M.Domain} (ha : M.IsLimitOrdinal a)
    (hU : Js_value_d a U R) (L : List M.Domain) (hL : ∀ x ∈ L, M.mem x U) :
    ∃ b, M.mem b a ∧ ∃ V S, Js_value_d b V S ∧ ∀ x ∈ L, M.mem x V := by
  let hE := (KPi.models_iff_l.mp hM).1.1
  induction L with
  | nil =>
    obtain ⟨b, hb⟩ := ha.2.1
    obtain ⟨V, S, hv⟩ := js_value_exists_l hM b
    exact ⟨b, hb, V, S, hv, fun _ h => (List.not_mem_nil h).elim⟩
  | cons x L ih =>
    obtain ⟨b, hb, V, S, hv, hL'⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    obtain ⟨c, hc, W, T, hw, hxW⟩ := (js_limit_l hM ha hU x).mp (hL x (List.mem_cons_self ..))
    rcases ha.1.wellOrder.linear.compare b hb c hc with he | hbc | hcb
    · have he := hE.eq_of_same_members b c he; subst c
      obtain ⟨rfl, rfl⟩ := js_value_unique_l hM hv hw
      exact ⟨b, hb, _, _, hv, fun y hy => (List.mem_cons.mp hy).elim (fun he => he ▸ hxW) (hL' y)⟩
    · have inc := (js_end_l hM (ha.1.mem hc) hbc hv hw).1
      exact ⟨c, hc, W, T, hw, fun y hy => (List.mem_cons.mp hy).elim (fun he => he ▸ hxW) (fun hy => inc y (hL' y hy))⟩
    · have hxV := (js_end_l hM (ha.1.mem hb) hcb hw hv).1 x hxW
      exact ⟨b, hb, V, S, hv, fun y hy => (List.mem_cons.mp hy).elim (fun he => he ▸ hxV) (hL' y)⟩

theorem js_limit_closed_l (hM : M.Models KPi) {a U R : M.Domain} (ha : M.IsLimitOrdinal a)
    (hU : Js_value_d a U R) : Rd_closed_d U := by
  let hKP := (KPi.models_iff_l.mp hM).1
  intro k x y z hx hy hz t ht
  obtain ⟨b, hb, V, S, hv, hV⟩ := js_finite_stage_l hM ha hU [x, y, z] (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    exact hw.elim (fun h => h ▸ hx) (fun h => h.elim (fun h => h ▸ hy) (fun h => h ▸ hz)))
  obtain ⟨c, hc, hbc⟩ := ha.2.2 b hb
  obtain ⟨W, T, hw⟩ := js_value_exists_l hM c
  obtain ⟨B, Q, h⟩ := rw_successor_exists_l hKP V S
  obtain ⟨A, haV, haB⟩ := (rw_successor_correct_l hKP (js_coherence_l hM (ha.1.mem hb) hv).2.1 h).1
  have input w hw : M.mem w A := (haV w).mpr (Or.inl (hV w hw))
  have htB := (haB t).mpr (Or.inr ⟨k, x, y, z, input x (by simp), input y (by simp), input z (by simp), ht⟩)
  exact (js_end_l hM ha.1 hc hw hU).1 t
    (((js_coherence_l hM (ha.1.mem hc) hw).2.2 b hbc V S B Q hv h).1 t htB)

end YesMetaZFC.SetTheory.InnerModel
