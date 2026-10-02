import YesMetaZFC.SetTheory.InnerModel.Order.InternalState

/-! # 从有序微层重新识别原 J 层

传递 rud 闭包的可见微层截口先给出一个微层。反向识别使用原宏观层级的
内部归纳：严格位于某宏后继之间的微层不可能已经 rud 封闭。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Jc_level_d (C : M.Domain) : Prop := ∃ a, J_d a C
def jc_level_m {n} (C : Term n) : Formula 1 n :=
  .existsE (.conj (KP.ord0_m .newest) (jh_value_m .newest C.weaken))
derive_free_closed jc_level_m
theorem jc_level_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (C : Term n) :
    Formula.satisfies ρ (jc_level_m C) ↔ Jc_level_d (C.eval ρ) := by
  simp only [jc_level_m, Jc_level_d, J_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, jh_value_sat_l, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem jc_rud_macro_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C)
    (h : Js_rep_d C) : Jc_level_d C := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨b, R, hb, hr⟩ := h
  obtain ⟨a, V, ha, hCV⟩ := (js_value_constructible_l hM hb hr).1
  let φ : UnarySchema 0 := { body := (.imp (KP.ord0_m .newest) <| .forallE <|
    .imp (jh_value_m (.bound 1) .newest) <| .forallE <| .forallE <| .forallE <|
      .imp (KP.ord0_m (.bound 2)) <| .imp (js_value_m (.bound 2) (.bound 1) .newest) <|
        .imp (rd_closed_m (.bound 1)) <| .imp (.mem (.bound 1) (.bound 3)) (jc_level_m (.bound 1))) }
  have sat a : φ.denote (js_env_l C) a ↔ (M.IsOrdinal a → ∀ V, Jh_value_d a V →
      ∀ b D S, M.IsOrdinal b → Js_value_d b D S → Rd_closed_d D → M.mem D V → Jc_level_d D) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, KP.ord0_sat_l hKP,
      Formula.satisfies_forall_iff, jh_value_sat_l, js_value_sat_l hKP.1, rd_closed_sat_l hKP,
      Formula.satisfies_mem_iff, jc_level_sat_l hKP]; rfl
  apply (sat a).mp ((KPi.models_iff_l.mp hM).2 φ (js_env_l C) ?_ a) ha.1 V ha.2 b C R hb hr hC hCV
  intro a ih
  apply (sat a).mpr
  intro ha V hv b D S hb hd hD hDV
  rcases js_ordinal_cases_l hKP.1 ha with he | ⟨c, hc, hs⟩ | hl
  · exact (jh_zero_l hM he hv D hDV).elim
  · obtain ⟨W, hw⟩ := jh_value_exists_l hM c
    obtain ⟨d, Q, ho, hq⟩ := jh_order_rep_l hM (ha.mem hc) hw
    rcases Structure.IsOrdinal.trichotomy hKP.1 hb ho (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP b d) with he | hbd | hdb
    · have he := hKP.1.eq_of_same_members b d he; subst d
      have he := (js_value_unique_l hM hd hq).1
      subst D
      exact ⟨c, ha.mem hc, hw⟩
    · exact (sat c).mp (ih c hc) (ha.mem hc) W hw b D S hb hd hD (js_value_mem_l hM ho hbd hd hq)
    · have hWD := js_value_mem_l hM hb hdb hq hd
      have sub := (js_end_l hM hb hdb hq hd).1
      obtain ⟨A, hsA, hHull⟩ := jh_successor_l hM (ha.mem hc) hs hw hv
      have hVD := (rd_closure_spec_l hM hHull).2.2 D hD (fun x hx =>
        ((hsA x).mp hx).elim (sub x) (fun he => (hKP.1.eq_of_same_members x W he).symm ▸ hWD))
      exact (KP.mem_irrefl_d hKP D (hVD D hDV)).elim
  · obtain ⟨c, hc, W, hw, hDW⟩ := (jh_limit_l hM hl hv D).mp hDV
    exact (sat c).mp (ih c hc) (ha.mem hc) W hw b D S hb hd hD hDW

theorem jc_cut_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → Js_access_d C x) : Jc_level_d C :=
  jc_rud_macro_l hM hC (js_cut_l hM hC hc cover)

end YesMetaZFC.SetTheory.InnerModel
