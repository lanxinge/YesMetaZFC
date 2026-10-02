import YesMetaZFC.SetTheory.InnerModel.Order.HistoryLocal

/-! # 有序微层的局部覆盖与规范序数截口

可见的完整历史把“某微层属于 C”化为 C 上的有界查询。收集这些索引得到
真实序数；若这些微层覆盖 C，便直接识别 C 为该序数处的微层。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Js_rep_d (C : M.Domain) : Prop := ∃ a R, M.IsOrdinal a ∧ Js_value_d a C R
def Js_access_d (C x : M.Domain) : Prop :=
  ∃ a U R, M.IsOrdinal a ∧ Js_value_d a U R ∧ M.mem U C ∧ M.mem x U

theorem js_comparable_l (hM : M.Models KPi) {a b U R V S : M.Domain}
    (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) (hu : Js_value_d a U R) (hv : Js_value_d b V S) :
    Rw_end_d U R V S ∨ Rw_end_d V S U R := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rcases Structure.IsOrdinal.trichotomy hKP.1 ha hb (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP a b) with he | hab | hba
  · have he := hKP.1.eq_of_same_members a b he; subst b
    obtain ⟨rfl, rfl⟩ := js_value_unique_l hM hu hv
    exact Or.inl (rw_end_refl_l (fun _ _ h => (js_value_bounded_l hM hu).entry_l h))
  · exact Or.inl (js_end_l hM hb hab hu hv)
  · exact Or.inr (js_end_l hM ha hba hv hu)

theorem js_access_pair_l (hM : M.Models KPi) {C x y : M.Domain} (hx : Js_access_d C x) (hy : Js_access_d C y) :
    ∃ a U R, M.IsOrdinal a ∧ Js_value_d a U R ∧ M.mem U C ∧ M.mem x U ∧ M.mem y U := by
  obtain ⟨a, U, R, ha, hu, hUC, hx⟩ := hx
  obtain ⟨b, V, S, hb, hv, hVC, hy⟩ := hy
  rcases js_comparable_l hM ha hb hu hv with h | h
  · exact ⟨b, V, S, hb, hv, hVC, h.1 x hx, hy⟩
  · exact ⟨a, U, R, ha, hu, hUC, hx, h.1 y hy⟩

def js_access_s : Delta0UnarySchema 1 where
  body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
      (.conj (js_seen_m (.bound 5) (.bound 3) (.bound 2))
        (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (.mem (.bound 4) (.bound 1)))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (js_seen_delta_l ..) (.conj (kpair0_delta_l ..) (.mem _ _))))))

theorem js_access_sat_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (ρ : Env M 0) (x : M.Domain) :
    js_access_s.toUnarySchema.denote (ρ.push C) x ↔ Js_access_d C x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  simp only [UnarySchema.denote, js_access_s, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, js_seen_sat_l hKP ρ, kpair0_sat_l hKP.1, Formula.satisfies_mem_iff]
  change (∃ a, M.mem a C ∧ ∃ p, M.mem p C ∧ ∃ U, M.mem U C ∧ ∃ R, M.mem R C ∧
    Js_seen_d ρ C a p ∧ KPair_d M p U R ∧ M.mem x U) ↔ _
  constructor
  · rintro ⟨a, _, p, _, U, hU, R, _, h, hp, hx⟩
    exact ⟨a, U, R, h.1, ⟨p, h.state_l, hp⟩, hU, hx⟩
  · rintro ⟨a, U, R, ha, ⟨p, hp, hpUR⟩, hU, hx⟩
    have h := js_seen_of_in_l hKP hc ha (js_state_in_l hM hC hc ρ ha hp hpUR hU)
    exact ⟨a, h.2.1, p, h.2.2.1, U, hU, R, (po_pair_bound_l hc h.2.2.1 hpUR).2, h, hpUR, hx⟩

theorem js_rep_access_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C)
    (h : Js_rep_d C) : ∀ x, M.mem x C → Js_access_d C x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, R, ha, h⟩ := h
  rcases js_ordinal_cases_l hKP.1 ha with he | ⟨b, hb, hs⟩ | hl
  · exact fun x hx => ((js_zero_l hM he h).1 x hx).elim
  · obtain ⟨U, S, hu⟩ := js_value_exists_l hM b
    exact (KP.mem_irrefl_d hKP C (rw_successor_carrier_closed_l hKP hC
      (js_value_mem_l hM ha hb hu h) (js_coherence_l hM (ha.mem hb) hu).1
      (js_successor_l hM (ha.mem hb) hs hu h))).elim
  · intro x hx
    obtain ⟨b, hb, U, S, hu, hx⟩ := (js_limit_l hM hl h x).mp hx
    exact ⟨b, U, S, ha.mem hb, hu, js_value_mem_l hM ha hb hu h, hx⟩

theorem js_cut_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → Js_access_d C x) : Js_rep_d C := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := js_env_l C
  obtain ⟨I, hi⟩ := KP.separation_exists_d hKP js_indices_s (ρ.push C) C
  have ix a : M.mem a I ↔ M.IsOrdinal a ∧ ∃ U R, Js_value_d a U R ∧ M.mem U C := by
    rw [hi a]
    change (M.mem a C ∧ js_indices_s.toUnarySchema.denote (ρ.push C) a) ↔ _
    rw [js_indices_sat_l hKP ρ]
    apply Iff.trans ?_ (js_seen_carrier_l hM hC hc ρ a)
    exact ⟨fun ⟨_, p, _, h⟩ => ⟨p, h⟩, fun ⟨p, h⟩ => ⟨h.2.1, p, h.2.2.1, h⟩⟩
  have it : M.TransitiveSet I := by
    intro a ha b hb
    obtain ⟨ha, U, R, hu, hUC⟩ := (ix a).mp ha
    obtain ⟨V, S, hv⟩ := js_value_exists_l hM b
    exact (ix b).mpr ⟨ha.mem hb, V, S, hv, hc U hUC V (js_value_mem_l hM ha hb hv hu)⟩
  have io := KP.ordinal_of_transitive_l hKP it (fun a ha => ((ix a).mp ha).1)
  obtain ⟨V, S, hv⟩ := js_value_exists_l hM I
  have extend a (ha : M.mem a I) : ∃ b, M.mem b I ∧ M.mem a b := by
    obtain ⟨ha, U, R, hu, hUC⟩ := (ix a).mp ha
    obtain ⟨b, hb, hs⟩ := KP.ordinal_successor_l hKP ha
    obtain ⟨W, T, hw⟩ := js_value_exists_l hM b
    exact ⟨b, (ix b).mpr ⟨hb, W, T, hw, rw_successor_carrier_closed_l hKP hC hUC
      (js_coherence_l hM ha hu).1 (js_successor_l hM ha hs hu hw)⟩, hs.predecessor_mem⟩
  have eq : C = V := by
    classical
    by_cases hn : ∃ a, M.mem a I
    · have hl : M.IsLimitOrdinal I := ⟨io, hn, extend⟩
      apply hKP.1.eq_of_same_members; intro x
      rw [js_limit_l hM hl hv x]
      constructor
      · intro hx
        obtain ⟨a, U, R, ha, hu, hUC, hx⟩ := cover x hx
        exact ⟨a, (ix a).mpr ⟨ha, U, R, hu, hUC⟩, U, R, hu, hx⟩
      · rintro ⟨a, ha, U, R, hu, hx⟩
        obtain ⟨_, W, T, hw, hWC⟩ := (ix a).mp ha
        have he := (js_value_unique_l hM hu hw).1
        exact hc W hWC x (he ▸ hx)
    · have empty a ha := hn ⟨a, ha⟩
      apply hKP.1.eq_of_same_members; intro x
      apply iff_of_false ?_ ((js_zero_l hM empty hv).1 x)
      intro hx
      obtain ⟨a, U, R, ha, hu, hUC, _⟩ := cover x hx
      exact empty a ((ix a).mpr ⟨ha, U, R, hu, hUC⟩)
  exact ⟨I, S, io, eq ▸ hv⟩

end YesMetaZFC.SetTheory.InnerModel
