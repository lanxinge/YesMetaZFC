import YesMetaZFC.SetTheory.InnerModel.Rudimentary.FamilyBound

/-! # 一步扩张自身属于 rud 闭包

先在共同传递界上建立成员真值表，再沿 U³ 收集参数纤维。因此不仅逐个输出，
整个函数像以及 s(U) 都是有限基构造出的集合；证明不要求闭包满足 KP。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rd_family_image_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) (k : Rd_sym) :
    ∃ Y, M.mem Y C ∧ ∀ z, M.mem z Y ↔
      ∃ a b c, M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ Rd_fun_d k a b c z := by
  classical
  by_cases hn : Nonempty {x : M.Domain // M.mem x U}
  · obtain ⟨T, hTC, ht, ut, hb⟩ := rd_family_bound_l hKP hC hU hu
    have hnT : Nonempty {x : M.Domain // M.mem x T} := hn.elim fun ⟨a, ha⟩ => ⟨⟨a, ut a ha⟩⟩
    let φ : Formula 1 4 := rd_member_m k (.bound 1) (.bound 2) (.bound 3) (.bound 0)
    obtain ⟨R, hRC, hR⟩ := rt_delta_l hKP hC hTC ht hnT φ
      (by simp -implicitDefEqProofs [φ]) (rd_member_delta_l ..) id
    have hR : Rt_table_d T (fun e => Rd_mem_d k (e 1).val (e 2).val (e 3).val (e 0).val) R :=
      hR.congr_l fun e => rd_member_sat_l hKP _ k _ _ _ _
    obtain ⟨P, hPC, hP⟩ := rt_power_l hKP hC hU 2
    obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .fibers hRC hPC hRC
    have fiber (e : Rt_env U 2) {p z} (hp : Rt_tuple_d (fun i => (e i).val) p) :
        Rd_fiber_d R p z ↔ Rd_fun_d k (e 0).val (e 1).val (e 2).val z := by
      let f : Rt_env T 2 := fun i => ⟨(e i).val, ut _ (e i).property⟩
      apply (hR.fiber_l hKP f hp).trans
      apply forall_congr'; intro x; apply iff_congr Iff.rfl
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hb k _ _ _ x (e 0).property (e 1).property (e 2).property h, h⟩⟩
    refine ⟨Y, hYC, fun z => (hY z).trans ?_⟩
    constructor
    · rintro ⟨p, hp, hz⟩
      obtain ⟨e, he, _⟩ := (hP p).mp hp
      exact ⟨(e 0).val, (e 1).val, (e 2).val, (e 0).property, (e 1).property, (e 2).property, (fiber e he).mp hz⟩
    · rintro ⟨a, b, c, ha, hb, hc, hz⟩
      let e : Rt_env U 2 := Fin.cases ⟨a, ha⟩ (Fin.cases ⟨b, hb⟩ (fun _ => ⟨c, hc⟩))
      obtain ⟨p, hp⟩ := rt_tuple_exists_l hKP (fun i => (e i).val)
      exact ⟨p, (hP p).mpr ⟨e, hp, trivial⟩, (fiber e hp).mpr hz⟩
  · obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .diff hU hU hU
    exact ⟨Y, hYC, fun z => iff_of_false (fun hz => ((hY z).mp hz).2 ((hY z).mp hz).1)
      (fun ⟨a, _, _, ha, _⟩ => hn ⟨⟨a, ha⟩⟩)⟩

theorem rd_step_closed_l (hKP : M.Models KP) {C U V : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) (hv : Rd_step_d U V) : M.mem V C := by
  have collect (L : List Rd_sym) : ∃ Y, M.mem Y C ∧ ∀ z, M.mem z Y ↔
      M.mem z U ∨ ∃ k, k ∈ L ∧ ∃ a b c, M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ Rd_fun_d k a b c z := by
    induction L with
    | nil => exact ⟨U, hU, fun z => by simp⟩
    | cons k L ih =>
      obtain ⟨A, hAC, hA⟩ := ih
      obtain ⟨B, hBC, hB⟩ := rd_family_image_l hKP hC hU hu k
      obtain ⟨Y, hYC, hY⟩ := hC.union_l hKP hAC hBC
      refine ⟨Y, hYC, fun z => (hY z).trans ?_⟩
      rw [hA z, hB z]
      simp only [List.mem_cons, exists_eq_or_imp]
      exact ⟨fun h => h.elim (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h))) (fun h => Or.inr (Or.inl h)),
        fun h => h.elim (fun h => Or.inl (Or.inl h)) (fun h => h.elim Or.inr (fun h => Or.inl (Or.inr h)))⟩
  obtain ⟨Y, hYC, hY⟩ := collect rd_menu_l
  have hY : Rd_step_d U Y := fun z => (hY z).trans (or_congr Iff.rfl
    ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, rd_menu_mem_l k, h⟩⟩)
  exact rd_step_unique_l hKP.1 hY hv ▸ hYC

end YesMetaZFC.SetTheory.InnerModel
