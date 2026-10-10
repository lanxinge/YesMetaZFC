import YesMetaZFC.SetTheory.InnerModel.Separation.Boolean

/-! # 以 F₃、F₄ 插入坐标的原子真值表

先构造“首坐标属于第 j+1 坐标”，再用首变量量化构造等同和任意方向的隶属。
所有表都来自固定有限基，未另加分离运算。
-/

namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem rt_mem_graph_l (hKP : M.Models KP) {U E : M.Domain} (he : Rd_fun_d .mem U U U E) (a b : M.Domain) :
    Rd_entry_d a b E ↔ M.mem a U ∧ M.mem b U ∧ M.mem a b := by
  constructor
  · rintro ⟨p, hp, hpE⟩
    obtain ⟨x, y, hx, hy, hxy, hp'⟩ := (he p).mp hpE
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact ⟨hx, hy, hxy⟩
  · rintro ⟨ha, hb, hab⟩
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total a b
    exact ⟨p, hp, (he p).mpr ⟨a, b, ha, hb, hab, hp⟩⟩

theorem rt_first_mem_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C)
    (n : Nat) (j : Fin (n + 1)) :
    ∃ R, M.mem R C ∧ Rt_table_d (n := n + 1) U (fun e => M.mem (e 0).val (e j.succ).val) R := by
  induction n with
  | zero =>
    have hj : j = 0 := by omega
    subst j
    obtain ⟨R, hRC, hR⟩ := hC.exists_l hKP .mem hU hU hU
    refine ⟨R, hRC, fun p => (hR p).trans ?_⟩
    constructor
    · rintro ⟨a, b, ha, hb, hab, hp⟩
      let e : Rt_env U 1 := Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩)
      exact ⟨e, ⟨b, hp, rfl⟩, hab⟩
    · rintro ⟨e, ⟨q, hp, hq⟩, hab⟩
      change q = (e 1).val at hq; subst q
      exact ⟨(e 0).val, (e 1).val, (e 0).property, (e 1).property, hab, hp⟩
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · obtain ⟨E, hEC, hE⟩ := hC.exists_l hKP .mem hU hU hU
      obtain ⟨D, hDC, hD⟩ := rt_power_l hKP hC hU n
      obtain ⟨R, hRC, hR⟩ := hC.exists_l hKP .last hDC hEC hU
      refine ⟨R, hRC, fun p => (hR p).trans ?_⟩
      constructor
      · rintro ⟨a, b, c, hc, hab, q, hq, hp⟩
        obtain ⟨e, he, _⟩ := (hD c).mp hc
        obtain ⟨ha, hb, hab⟩ := (rt_mem_graph_l hKP hE a b).mp hab
        let f : Rt_env U (n + 2) := Fin.cases ⟨a, ha⟩ (Fin.cases ⟨b, hb⟩ e)
        exact ⟨f, ⟨q, hp, ⟨c, hq, he⟩⟩, hab⟩
      · rintro ⟨e, ⟨q, hp, r, hq, he⟩, hab⟩
        exact ⟨(e 0).val, (e 1).val, r, (hD r).mpr ⟨fun i => e i.succ.succ, he, trivial⟩,
          (rt_mem_graph_l hKP hE _ _).mpr ⟨(e 0).property, (e 1).property, hab⟩, q, hq, hp⟩
    · obtain ⟨S, hSC, hS⟩ := ih j
      obtain ⟨R, hRC, hR⟩ := hC.exists_l hKP .mid hU hSC hU
      refine ⟨R, hRC, fun p => (hR p).trans ?_⟩
      constructor
      · rintro ⟨a, b, c, hb, hab, htr⟩
        obtain ⟨z, hz, hzS⟩ := hab
        obtain ⟨q, hq, hp⟩ := htr
        obtain ⟨e, ⟨r, hr, he⟩, hmem⟩ := (hS z).mp hzS
        obtain ⟨ha, hc⟩ := kpair_injective_l M hz hr
        subst a; subst r
        let f : Rt_env U (n + 2) := Fin.cases (e 0) (Fin.cases ⟨b, hb⟩ (fun i => e i.succ))
        exact ⟨f, ⟨q, hp, ⟨c, hq, he⟩⟩, hmem⟩
      · rintro ⟨e, ⟨q, hp, r, hq, he⟩, hmem⟩
        obtain ⟨z, hz⟩ := (kp_pair_l hKP).total (e 0).val r
        let f : Rt_env U (n + 1) := Fin.cases (e 0) (fun i => e i.succ.succ)
        exact ⟨(e 0).val, (e 1).val, r, (e 1).property,
          ⟨z, hz, (hS z).mpr ⟨f, ⟨r, hz, he⟩, hmem⟩⟩, q, hq, hp⟩

theorem rt_subset_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C)
    {n} (i j : Fin (n + 1)) : ∃ R, M.mem R C ∧ Rt_table_d U
      (fun e => ∀ z : {x : M.Domain // M.mem x U}, M.mem z.val (e i).val → M.mem z.val (e j).val) R := by
  obtain ⟨A, hAC, hA⟩ := rt_first_mem_l hKP hC hU n i
  obtain ⟨B, hBC, hB⟩ := rt_first_mem_l hKP hC hU n j
  obtain ⟨T, hTC, hT⟩ := rt_imp_l hKP hC hU hAC hBC hA hB
  exact rt_forall_l hKP hC hU hTC hT

theorem rt_eq_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C)
    (hu : M.TransitiveSet U) {n} (i j : Fin (n + 1)) :
    ∃ R, M.mem R C ∧ Rt_table_d U (fun e => e i = e j) R := by
  obtain ⟨A, hAC, hA⟩ := rt_subset_l hKP hC hU i j
  obtain ⟨B, hBC, hB⟩ := rt_subset_l hKP hC hU j i
  obtain ⟨R, hRC, hR⟩ := rt_and_l hKP hC hAC hBC hA hB
  refine ⟨R, hRC, hR.congr_l fun e => ⟨fun h => ?_, fun he => ?_⟩⟩
  · apply Subtype.ext; apply hKP.1.eq_of_same_members; intro z
    exact ⟨fun hz => h.1 ⟨z, hu _ (e i).property z hz⟩ hz,
      fun hz => h.2 ⟨z, hu _ (e j).property z hz⟩ hz⟩
  · exact ⟨fun _ hz => he ▸ hz, fun _ hz => he.symm ▸ hz⟩

theorem rt_mem_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C)
    (hu : M.TransitiveSet U) {n} (i j : Fin (n + 1)) :
    ∃ R, M.mem R C ∧ Rt_table_d U (fun e => M.mem (e i).val (e j).val) R := by
  obtain ⟨A, hAC, hA⟩ := rt_eq_l hKP hC hU hu (n := n + 1) 0 i.succ
  obtain ⟨B, hBC, hB⟩ := rt_first_mem_l hKP hC hU n j
  obtain ⟨T, hTC, hT⟩ := rt_and_l hKP hC hAC hBC hA hB
  obtain ⟨R, hRC, hR⟩ := rt_exists_l hKP hC hTC hT
  refine ⟨R, hRC, hR.congr_l fun e => ⟨?_, fun h => ⟨e i, rfl, h⟩⟩⟩
  rintro ⟨z, he, hz⟩
  change z = e i at he
  subst z
  exact hz

end YesMetaZFC.SetTheory.InnerModel
