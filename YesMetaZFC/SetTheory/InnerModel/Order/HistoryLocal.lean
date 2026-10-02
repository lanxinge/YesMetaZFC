import YesMetaZFC.SetTheory.InnerModel.Order.HistoryLimit

/-! # 全部内部序数的短历史局部性

若传递 rud 闭包 C 包含微层 Sₐ 本身，则 a 处的完整状态证书也属于 C。
这比只处理可容许层更强，归纳仅在背景 KPi 中进行。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_ordinal_cases_l (hE : Extensional M) {a : M.Domain} (ha : M.IsOrdinal a) :
    (∀ x, ¬ M.mem x a) ∨ (∃ b, M.mem b a ∧ M.SuccessorOf a b) ∨ M.IsLimitOrdinal a := by
  classical
  by_cases hn : ∃ x, M.mem x a
  · by_cases hl : ∀ b, M.mem b a → ∃ c, M.mem c a ∧ M.mem b c
    · exact Or.inr (Or.inr ⟨ha, hn, hl⟩)
    · have top : ∃ b, M.mem b a ∧ ∀ c, M.mem c a → ¬ M.mem b c := by
        apply Classical.byContradiction
        intro hn
        apply hl
        intro b hb
        apply Classical.byContradiction
        intro hno
        exact hn ⟨b, hb, fun c hc hbc => hno ⟨c, hc, hbc⟩⟩
      obtain ⟨b, hb, ht⟩ := top
      refine Or.inr (Or.inl ⟨b, hb, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩)
      · rcases ha.wellOrder.linear.compare x hx b hb with h | h | h
        · exact Or.inr h
        · exact Or.inl h
        · exact (ht x hx h).elim
      · exact hx.elim (fun hx => ha.transitive b hb x hx) (fun he => (hE.eq_of_same_members x b he).symm ▸ hb)
  · exact Or.inl (fun x hx => hn ⟨x, hx⟩)

theorem js_empty_in_l (hKP : M.Models KP) {C E p : M.Domain} (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (ρ : Env M 0) (hEC : M.mem E C) (he : ∀ x, ¬ M.mem x E) (hp : KPair_d M p E E) :
    Si_cert_d C (rc_value_s rw_op_s) ρ E p := by
  have et : M.TransitiveSet E := fun x hx => (he x hx).elim
  obtain ⟨T, hTC, ht, hET⟩ := rd_transitive_enclosed_l hKP hC hEC et
  have range : Rd_fun_d .range E E E E := fun x => iff_of_false (he x) (fun ⟨_, r, _, hr⟩ => he r hr)
  have image i : Rp_image_d i E E := fun x => iff_of_false (he x) (fun ⟨q, hq, _⟩ => he q hq)
  have un : Rd_fun_d .union E E E E := fun x => iff_of_false (he x) (fun ⟨a, ha, _⟩ => he a ha)
  have op := rw_op_in_l hKP hC hTC ht ρ
    ⟨E, E, E, E, E, E, hET, hET, hET, hET, hET, hET, range, image false, image true, un, un, hp,
      (rw_state_s.image_matrix_l ρ E E T).mpr ⟨fun x hx => (he x hx).elim, fun x hx => (he x hx).elim⟩⟩
  have cert : Rc_cert_d rw_op_s ρ E E T := ⟨ht, hET, hET, et,
    ⟨fun x hx => (he x hx).elim, fun x hx => (he x hx).elim, fun x hx => (he x hx).elim⟩,
    fun x hx => (he x hx).elim⟩
  exact rc_local_extend_l hKP hC hc cert hTC op

def js_here_m {n} (C a p : Term n) : Formula 1 n := Formula.existsMem C
  (.conj (Formula.isTransitive .newest) (.conj (.mem p.weaken .newest) (js_wit_m a.weaken p.weaken .newest)))
derive_free_closed js_here_m
theorem js_here_sat_l (ρ : Env M 0) {n} (η : Env M n) (C a p : Term n) :
    Formula.satisfies η (js_here_m C a p) ↔ Si_cert_d (C.eval η) (rc_value_s rw_op_s) ρ (a.eval η) (p.eval η) := by
  simp only [js_here_m, Si_cert_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff, js_wit_sat_l ρ,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def js_history_s : UnarySchema 0 where
  body := .imp (KP.ord0_m .newest) <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (js_state_m (.bound 4) .newest) <| .imp (kpair0_m .newest (.bound 2) (.bound 1)) <|
      .imp (.mem (.bound 2) (.bound 3)) <| .imp (Formula.isTransitive (.bound 3)) <|
        .imp (rd_closed_m (.bound 3)) (js_here_m (.bound 3) (.bound 4) .newest)
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
theorem js_history_sat_l (hKP : M.Models KP) (ρ : Env M 0) (a : M.Domain) :
    js_history_s.denote ρ a ↔ (M.IsOrdinal a → ∀ C U R p, Js_state_d a p → KPair_d M p U R → M.mem U C →
      M.TransitiveSet C → Rd_closed_d C → Si_cert_d C (rc_value_s rw_op_s) ρ a p) := by
  simp only [UnarySchema.denote, js_history_s, Formula.satisfies_imp_iff, KP.ord0_sat_l hKP,
    Formula.satisfies_forall_iff, js_state_sat_l, kpair0_sat_l hKP.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isTransitive_iff, rd_closed_sat_l hKP, js_here_sat_l ρ]; rfl

theorem js_state_in_l (hM : M.Models KPi) {C a U R p : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (ρ : Env M 0) (ha : M.IsOrdinal a) (hp : Js_state_d a p)
    (hpUR : KPair_d M p U R) (hUC : M.mem U C) : Si_cert_d C (rc_value_s rw_op_s) ρ a p := by
  let hKP := (KPi.models_iff_l.mp hM).1
  apply (js_history_sat_l hKP ρ a).mp ((KPi.models_iff_l.mp hM).2 js_history_s ρ ?_ a) ha C U R p hp hpUR hUC hc hC
  intro a ih
  apply (js_history_sat_l hKP ρ a).mpr
  intro ha C U R p hp hpUR hUC hc hC
  have level : Js_value_d a U R := ⟨p, hp, hpUR⟩
  rcases js_ordinal_cases_l hKP.1 ha with he | ⟨b, hb, hs⟩ | hl
  · have hz := js_zero_l hM he level
    have hU := hKP.1.eq_of_same_members U a (fun x => iff_of_false (hz.1 x) (he x)); subst U
    have hR := hKP.1.eq_of_same_members R a (fun x => iff_of_false (hz.2 x) (he x)); subst R
    exact js_empty_in_l hKP hC hc ρ hUC he hpUR
  · obtain ⟨q, hq⟩ := js_state_exists_l hM b
    obtain ⟨V, S, hqVS⟩ := js_state_pair_l hM hq
    have hv : Js_value_d b V S := ⟨q, hq, hqVS⟩
    have hVC := hc U hUC V (js_value_mem_l hM ha hb hv level)
    have prev := (js_history_sat_l hKP ρ b).mp (ih b hb) (ha.mem hb) C V S q hq hqVS hVC hc hC
    exact js_successor_in_l hM hC hc ρ ha hs prev hp
  · apply js_limit_in_l hM hC hc hUC ρ hl hp hpUR
    intro b hb
    obtain ⟨q, hq⟩ := js_state_exists_l hM b
    obtain ⟨V, S, hqVS⟩ := js_state_pair_l hM hq
    exact ⟨q, (js_history_sat_l hKP ρ b).mp (ih b hb) (ha.mem hb) U V S q hq hqVS
      (js_value_mem_l hM ha hb ⟨q, hq, hqVS⟩ level) (js_coherence_l hM ha level).1 (js_limit_closed_l hM hl level)⟩

theorem js_seen_carrier_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (ρ : Env M 0) (a : M.Domain) :
    (∃ p, Js_seen_d ρ C a p) ↔ M.IsOrdinal a ∧ ∃ U R, Js_value_d a U R ∧ M.mem U C := by
  let hKP := (KPi.models_iff_l.mp hM).1
  constructor
  · rintro ⟨p, h⟩
    obtain ⟨U, R, hp⟩ := js_state_pair_l hM h.state_l
    exact ⟨h.1, U, R, ⟨p, h.state_l, hp⟩, (po_pair_bound_l hc h.2.2.1 hp).1⟩
  · rintro ⟨ha, U, R, ⟨p, hp, hpUR⟩, hUC⟩
    exact ⟨p, js_seen_of_in_l hKP hc ha (js_state_in_l hM hC hc ρ ha hp hpUR hUC)⟩

end YesMetaZFC.SetTheory.InnerModel
