import YesMetaZFC.SetTheory.InnerModel.Order.Access
import YesMetaZFC.SetTheory.InnerModel.Jensen.Hierarchy

/-! # 原 J 层与有序微层的识别

先证明 rud 生成保持局部微层覆盖，再由最小闭包与规范截口识别原宏观层级。
全部索引都属于背景模型；无需外部序数算术或可容许层假设。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem jh_value_closed_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a)
    (h : Jh_value_d a C) : Rd_closed_d C := by
  let hKP := (KPi.models_iff_l.mp hM).1
  intro k x y z hx hy hz v hv
  obtain ⟨b, hb, U, hu, Z, hs, hxZ⟩ := (jh_value_equation_l hM h x).mp hx
  have finite (L : List M.Domain) (hL : ∀ w ∈ L, M.mem w C) :
      ∃ b, M.mem b a ∧ ∃ U Z, Jh_value_d b U ∧ Jh_step_d U Z ∧ ∀ w ∈ L, M.mem w Z := by
    induction L with
    | nil => exact ⟨b, hb, U, Z, hu, hs, fun _ hw => (List.not_mem_nil hw).elim⟩
    | cons w L ih =>
      obtain ⟨c, hc, V, T, hv, ht, hL'⟩ := ih (fun t ht => hL t (List.mem_cons_of_mem _ ht))
      obtain ⟨d, hd, W, hw, Q, hq, hwQ⟩ := (jh_value_equation_l hM h w).mp (hL w (by simp))
      have choose A (hLA : M.MemberSubset T A) (hwA : M.mem w A) : ∀ t ∈ w :: L, M.mem t A :=
        fun t ht => (List.mem_cons.mp ht).elim (fun he => he ▸ hwA) (fun ht => hLA t (hL' t ht))
      rcases ha.wellOrder.linear.compare c hc d hd with he | hcd | hdc
      · have he := hKP.1.eq_of_same_members c d he; subst d
        have he := jh_value_unique_l hM hv hw; subst W
        have he := jh_step_unique_l hM ht hq; subst Q
        exact ⟨c, hc, V, T, hv, ht, choose T (fun _ h => h) hwQ⟩
      · exact ⟨d, hd, W, Q, hw, hq, choose Q (jh_step_le_l hM
          (jh_value_mono_l hM ((ha.mem hd).transitive c hcd) hv hw) (jh_value_mem_l hM hcd hv hw) ht hq) hwQ⟩
      · exact ⟨c, hc, V, T, hv, ht, choose T (fun _ h => h) (jh_step_le_l hM
          (jh_value_mono_l hM ((ha.mem hc).transitive d hdc) hw hv) (jh_value_mem_l hM hdc hw hv) hq ht w hwQ)⟩
  obtain ⟨c, hc, V, T, hv', ht, hL⟩ := finite [x, y, z] (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h <;> subst w <;> assumption)
  exact (jh_value_equation_l hM h v).mpr ⟨c, hc, V, hv', T, ht,
    (jh_step_spec_l hM ht).1 k x y z (hL x (by simp)) (hL y (by simp)) (hL z (by simp)) v hv⟩

theorem js_next_in_l (hM : M.Models KPi) {C a U R : M.Domain} (hC : Rd_closed_d C)
    (ha : M.IsOrdinal a) (hu : Js_value_d a U R) (hUC : M.mem U C) :
    ∃ b V S, M.IsOrdinal b ∧ Js_value_d b V S ∧ M.mem V C ∧ Rw_successor_d U R V S := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨b, hb, hs⟩ := KP.ordinal_successor_l hKP ha
  obtain ⟨V, S, hv⟩ := js_value_exists_l hM b
  have step := js_successor_l hM ha hs hu hv
  exact ⟨b, V, S, hb, hv, rw_successor_carrier_closed_l hKP hC hUC (js_coherence_l hM ha hu).1 step, step⟩

theorem js_access_rud_l (hM : M.Models KPi) {C x y z v : M.Domain} (hC : Rd_closed_d C) (k : Rd_sym)
    (hx : Js_access_d C x) (hy : Js_access_d C y) (hz : Js_access_d C z) (hv : Rd_fun_d k x y z v) : Js_access_d C v := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, U, R, ha, hu, hUC, hx, hy⟩ := js_access_pair_l hM hx hy
  obtain ⟨b, V, S, hb, hw, hVC, hz⟩ := hz
  have generate a U R (ha : M.IsOrdinal a) (hu : Js_value_d a U R) (hUC : M.mem U C)
      (hx : M.mem x U) (hy : M.mem y U) (hz : M.mem z U) : Js_access_d C v := by
    obtain ⟨b, V, S, hb, hw, hVC, step⟩ := js_next_in_l hM hC ha hu hUC
    obtain ⟨A, hs, hd⟩ := (rw_successor_correct_l hKP (js_coherence_l hM ha hu).2.1 step).1
    exact ⟨b, V, S, hb, hw, hVC, (hd v).mpr (Or.inr ⟨k, x, y, z,
      (hs x).mpr (Or.inl hx), (hs y).mpr (Or.inl hy), (hs z).mpr (Or.inl hz), hv⟩)⟩
  exact (js_comparable_l hM ha hb hu hw).elim
    (fun h => generate b V S hb hw hVC (h.1 x hx) (h.1 y hy) hz)
    (fun h => generate a U R ha hu hUC hx hy (h.1 z hz))

theorem js_hull_access_l (hM : M.Models KPi) {U C : M.Domain} (hu : Js_rep_d U) (h : Jh_step_d U C) :
    ∀ x, M.mem x C → Js_access_d C x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, R, ha, hu⟩ := hu
  have hC := (jh_step_spec_l hM h).1
  have hc := jh_step_transitive_l hM (js_coherence_l hM ha hu).1 h
  let ρ := js_env_l C
  obtain ⟨D, hd⟩ := KP.separation_exists_d hKP js_access_s (ρ.push C) C
  have dm x : M.mem x D ↔ M.mem x C ∧ Js_access_d C x :=
    (hd x).trans (and_congr_right fun _ => js_access_sat_l hM hC hc ρ x)
  have dc : Rd_closed_d D := fun k x y z hx hy hz v hv => (dm v).mpr
    ⟨hC k x y z ((dm x).mp hx).1 ((dm y).mp hy).1 ((dm z).mp hz).1 v hv,
      js_access_rud_l hM hC k ((dm x).mp hx).2 ((dm y).mp hy).2 ((dm z).mp hz).2 hv⟩
  obtain ⟨b, V, S, hb, hv, hVC, step⟩ := js_next_in_l hM hC ha hu (jh_step_spec_l hM h).2.2
  obtain ⟨A, hs, hdV⟩ := (rw_successor_correct_l hKP (js_coherence_l hM ha hu).2.1 step).1
  obtain ⟨B, hB, h⟩ := h
  have seed : M.MemberSubset B D := by
    intro x hx
    have hxV := (hdV x).mpr (Or.inl ((hs x).mpr ((hB x).mp hx)))
    exact (dm x).mpr ⟨hc V hVC x hxV, b, V, S, hb, hv, hVC, hxV⟩
  exact fun x hx => ((dm x).mp ((rd_closure_spec_l hM h).2.2 D dc seed x hx)).2

def js_rep_m {n} (C : Term n) : Formula 1 n := .existsE (.existsE
  (.conj (KP.ord0_m (.bound 1)) (js_value_m (.bound 1) C.weaken.weaken .newest)))
derive_free_closed js_rep_m
theorem js_rep_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (C : Term n) :
    Formula.satisfies ρ (js_rep_m C) ↔ Js_rep_d (C.eval ρ) := by
  simp only [js_rep_m, Js_rep_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, js_value_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 每个原 J 层都是上述同一有序微层级的实际一层。 -/
theorem jh_order_rep_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a)
    (h : Jh_value_d a C) : Js_rep_d C := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let φ : UnarySchema 0 := { body := (.imp (KP.ord0_m .newest)
    (.forallE (.imp (jh_value_m (.bound 1) .newest) (js_rep_m .newest)))) }
  have sat b : φ.denote (js_env_l a) b ↔ (M.IsOrdinal b → ∀ C, Jh_value_d b C → Js_rep_d C) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.ord0_sat_l hKP,
      Formula.satisfies_forall_iff, jh_value_sat_l, js_rep_sat_l hKP]; rfl
  apply (sat a).mp ((KPi.models_iff_l.mp hM).2 φ (js_env_l a) ?_ a) ha C h
  intro a ih
  apply (sat a).mpr
  intro ha C h
  rcases js_ordinal_cases_l hKP.1 ha with he | ⟨b, hb, hs⟩ | hl
  · obtain ⟨U, R, hu⟩ := js_value_exists_l hM a
    have eq := hKP.1.eq_of_same_members C U (fun x => iff_of_false (jh_zero_l hM he h x) ((js_zero_l hM he hu).1 x))
    exact ⟨a, R, ha, eq ▸ hu⟩
  · obtain ⟨U, hu⟩ := jh_value_exists_l hM b
    exact js_cut_l hM (jh_value_closed_l hM ha h) (jh_value_transitive_l hM h)
      (js_hull_access_l hM ((sat b).mp (ih b hb) (ha.mem hb) U hu) (jh_successor_l hM (ha.mem hb) hs hu h))
  · apply js_cut_l hM (jh_value_closed_l hM ha h) (jh_value_transitive_l hM h)
    intro x hx
    obtain ⟨b, hb, U, hu, hx⟩ := (jh_limit_l hM hl h x).mp hx
    obtain ⟨c, R, hc, hr⟩ := (sat b).mp (ih b hb) (ha.mem hb) U hu
    exact ⟨c, U, R, hc, hr, jh_value_mem_l hM hb hu h, hx⟩

end YesMetaZFC.SetTheory.InnerModel
