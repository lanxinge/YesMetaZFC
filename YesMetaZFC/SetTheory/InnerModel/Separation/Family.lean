import YesMetaZFC.SetTheory.InnerModel.Separation.Formula

/-! # 真值表的参数纤维族

把首坐标的真值切片读成一个集合，再用 F₈ 一次收集整个参数族。
这里构造无序对族及关系纤维族，为一步 rud 扩张提供实际集合界。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rt_tuple_closed_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C) {n}
    (e : Fin (n + 1) → M.Domain) (he : ∀ i, M.mem (e i) C) : ∃ p, M.mem p C ∧ Rt_tuple_d e p := by
  induction n with
  | zero => exact ⟨e 0, he 0, rfl⟩
  | succ n ih =>
    obtain ⟨q, hqC, hq⟩ := ih (fun i => e i.succ) (fun i => he i.succ)
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total (e 0) q
    exact ⟨p, hC .opair (e 0) q q (he 0) hqC hqC p (rd_opair_value_l hKP.1 hp), q, hp, hq⟩

theorem Rt_table_d.fiber_l (hKP : M.Models KP) {U R q Z : M.Domain} {n}
    {P : Rt_env U (n + 1) → Prop} (hR : Rt_table_d U P R) (e : Rt_env U n)
    (hq : Rt_tuple_d (fun i => (e i).val) q) :
    Rd_fiber_d R q Z ↔ ∀ x, M.mem x Z ↔ ∃ hx : M.mem x U, P (Fin.cases ⟨x, hx⟩ e) := by
  have entry x : Rd_entry_d x q R ↔ ∃ hx : M.mem x U, P (Fin.cases ⟨x, hx⟩ e) := by
    constructor
    · rintro ⟨p, hp, hpR⟩
      obtain ⟨f, ⟨r, hr, hf⟩, hP⟩ := (hR p).mp hpR
      obtain ⟨hx, hqr⟩ := kpair_injective_l M hp hr
      subst r
      have he := rt_env_inj_l hf hq
      have hf' : f = Fin.cases (f 0) e := funext (Fin.cases rfl (congrFun he))
      exact hx.symm ▸ ⟨(f 0).property, hf' ▸ hP⟩
    · rintro ⟨hx, hP⟩
      obtain ⟨p, hp⟩ := (kp_pair_l hKP).total x q
      let f : Rt_env U (n + 1) := Fin.cases ⟨x, hx⟩ e
      exact ⟨p, hp, (hR p).mpr ⟨f, ⟨q, hp, hq⟩, hP⟩⟩
  exact forall_congr' fun x => iff_congr Iff.rfl (entry x)

theorem Rd_closed_d.union_l {C A B : M.Domain} (hC : Rd_closed_d C) (hKP : M.Models KP)
    (hA : M.mem A C) (hB : M.mem B C) : ∃ V, M.mem V C ∧ M.IsUnionOfTwo V A B := by
  obtain ⟨P, hP, hp⟩ := hC.exists_l hKP .pair hA hB hA
  obtain ⟨V, hV, hv⟩ := hC.exists_l hKP .union hP hP hP
  refine ⟨V, hV, fun x => (hv x).trans ?_⟩
  exact ⟨fun ⟨z, hz, hx⟩ => ((hp z).mp hz).elim (fun h => Or.inl (h ▸ hx)) (fun h => Or.inr (h ▸ hx)),
    fun h => h.elim (fun hx => ⟨A, (hp A).mpr (Or.inl rfl), hx⟩)
      (fun hx => ⟨B, (hp B).mpr (Or.inr rfl), hx⟩)⟩

/-- 无序对族由等式真值表的纤维构造，不调用幂集或层内收集。 -/
theorem rt_pairs_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) :
    ∃ Y, M.mem Y C ∧ ∀ z, M.mem z Y ↔ ∃ a b, M.mem a U ∧ M.mem b U ∧ Pair_d M z a b := by
  classical
  by_cases hn : Nonempty {x : M.Domain // M.mem x U}
  · let φ : Formula 1 3 := .disj (Formula.extensionalEq (.bound 0) (.bound 1))
      (Formula.extensionalEq (.bound 0) (.bound 2))
    obtain ⟨R, hRC, hR⟩ := rt_formula_l hKP hC hU hu hn φ (by simp [φ, Definitional.Formula.FreeClosed]) id
    have hR : Rt_table_d U (fun e => (e 0).val = (e 1).val ∨ (e 0).val = (e 2).val) R :=
      hR.congr_l fun e => by
        simp only [φ, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hKP.1 hu hn)]
        change (e 0 = e 1 ∨ e 0 = e 2) ↔ _
        simp only [Subtype.ext_iff]
    obtain ⟨P, hPC, hP⟩ := hC.exists_l hKP .prod hU hU hU
    obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .fibers hRC hPC hRC
    have fiber (a b : {x : M.Domain // M.mem x U}) {q z} (hq : KPair_d M q a.val b.val) :
        Rd_fiber_d R q z ↔ Pair_d M z a.val b.val := by
      let e : Rt_env U 1 := Fin.cases a (fun _ => b)
      apply (hR.fiber_l hKP e ⟨b.val, hq, rfl⟩).trans
      apply forall_congr'; intro x; apply iff_congr Iff.rfl
      change (∃ hx : M.mem x U, x = a.val ∨ x = b.val) ↔ _
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.elim (fun h => h ▸ a.property) (fun h => h ▸ b.property), h⟩⟩
    refine ⟨Y, hYC, fun z => (hY z).trans ?_⟩
    constructor
    · rintro ⟨q, hq, hz⟩
      obtain ⟨a, b, ha, hb, hq⟩ := (hP q).mp hq
      exact ⟨a, b, ha, hb, (fiber ⟨a, ha⟩ ⟨b, hb⟩ hq).mp hz⟩
    · rintro ⟨a, b, ha, hb, hz⟩
      obtain ⟨q, hq⟩ := (kp_pair_l hKP).total a b
      exact ⟨q, (hP q).mpr ⟨a, b, ha, hb, hq⟩, (fiber ⟨a, ha⟩ ⟨b, hb⟩ hq).mpr hz⟩
  · obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .diff hU hU hU
    exact ⟨Y, hYC, fun z => iff_of_false (fun hz => ((hY z).mp hz).2 ((hY z).mp hz).1)
      (fun ⟨a, _, ha, _⟩ => hn ⟨⟨a, ha⟩⟩)⟩

theorem rt_pair_hull_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) :
    ∃ V, M.mem V C ∧ M.TransitiveSet V ∧ M.MemberSubset U V ∧
      ∀ a b p, M.mem a U → M.mem b U → Pair_d M p a b → M.mem p V := by
  obtain ⟨P, hPC, hP⟩ := rt_pairs_l hKP hC hU hu
  obtain ⟨V, hVC, hV⟩ := hC.union_l hKP hU hPC
  have old x hx := (hV x).mpr (Or.inl hx)
  refine ⟨V, hVC, ?_, old, fun a b p ha hb hp => (hV p).mpr (Or.inr ((hP p).mpr ⟨a, b, ha, hb, hp⟩))⟩
  intro p hp x hx
  rcases (hV p).mp hp with hp | hp
  · exact old x (hu p hp x hx)
  · obtain ⟨a, b, ha, hb, hp⟩ := (hP p).mp hp
    exact old x (((hp x).mp hx).elim (fun h => h ▸ ha) (fun h => h ▸ hb))

theorem rt_fibers_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) :
    ∃ Y, M.mem Y C ∧ ∀ z, M.mem z Y ↔ ∃ a b, M.mem a U ∧ M.mem b U ∧ Rd_fiber_d a b z := by
  classical
  by_cases hn : Nonempty {x : M.Domain // M.mem x U}
  · let φ : Formula 1 3 := rd_entry0_m (.bound 0) (.bound 2) (.bound 1)
    obtain ⟨R, hRC, hR⟩ := rt_delta_l hKP hC hU hu hn φ
      (by simp -implicitDefEqProofs [φ]) (rd_entry0_delta_l ..) id
    have hR : Rt_table_d U (fun e => Rd_entry_d (e 0).val (e 2).val (e 1).val) R :=
      hR.congr_l fun e => rd_entry0_sat_l hKP.1 _ _ _ _
    obtain ⟨P, hPC, hP⟩ := hC.exists_l hKP .prod hU hU hU
    obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .fibers hRC hPC hRC
    have fiber (a b : {x : M.Domain // M.mem x U}) {q z} (hq : KPair_d M q a.val b.val) :
        Rd_fiber_d R q z ↔ Rd_fiber_d a.val b.val z := by
      let e : Rt_env U 1 := Fin.cases a (fun _ => b)
      apply (hR.fiber_l hKP e ⟨b.val, hq, rfl⟩).trans
      apply forall_congr'; intro x; apply iff_congr Iff.rfl
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(rd_entry_transitive_l hu a.property h).1, h⟩⟩
    refine ⟨Y, hYC, fun z => (hY z).trans ?_⟩
    constructor
    · rintro ⟨q, hq, hz⟩
      obtain ⟨a, b, ha, hb, hq⟩ := (hP q).mp hq
      exact ⟨a, b, ha, hb, (fiber ⟨a, ha⟩ ⟨b, hb⟩ hq).mp hz⟩
    · rintro ⟨a, b, ha, hb, hz⟩
      obtain ⟨q, hq⟩ := (kp_pair_l hKP).total a b
      exact ⟨q, (hP q).mpr ⟨a, b, ha, hb, hq⟩, (fiber ⟨a, ha⟩ ⟨b, hb⟩ hq).mpr hz⟩
  · obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .diff hU hU hU
    exact ⟨Y, hYC, fun z => iff_of_false (fun hz => ((hY z).mp hz).2 ((hY z).mp hz).1)
      (fun ⟨a, _, ha, _⟩ => hn ⟨⟨a, ha⟩⟩)⟩

end YesMetaZFC.SetTheory.InnerModel
