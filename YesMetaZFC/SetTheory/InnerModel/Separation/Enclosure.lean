import YesMetaZFC.SetTheory.InnerModel.Rudimentary.FamilyBound

/-! # 有限基闭包中的局部传递界

这里只对已知有界的对象构造传递界，不假定一般传递闭包运算在 rud 闭包内。
关系和三元组的界来自有限次无序对扩张；有限参数族则取这些界的并。
-/

namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem rd_insert_closed_l (hKP : M.Models KP) {C U a : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (ha : M.mem a C) : ∃ V, M.mem V C ∧ ∀ x, M.mem x V ↔ M.mem x U ∨ x = a := by
  obtain ⟨A, hAC, hA⟩ := hC.exists_l hKP .pair ha ha ha
  obtain ⟨V, hVC, hV⟩ := hC.union_l hKP hU hAC
  exact ⟨V, hVC, fun x => (hV x).trans (or_congr Iff.rfl ((hA x).trans ⟨fun h => h.elim id id, Or.inl⟩))⟩

theorem rd_succ_closed_l (hKP : M.Models KP) {C a s : M.Domain} (hC : Rd_closed_d C)
    (ha : M.mem a C) (hs : M.SuccessorOf s a) : M.mem s C := by
  obtain ⟨V, hVC, hv⟩ := rd_insert_closed_l hKP hC ha ha
  have he := hKP.1.eq_of_same_members V s (fun x => (hv x).trans ((or_congr Iff.rfl
    ⟨fun h => h ▸ (fun _ => Iff.rfl), hKP.1.eq_of_same_members x a⟩).trans (hs x).symm))
  exact he ▸ hVC

theorem rd_bounded_enclosed_l (hKP : M.Models KP) {C U A : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) (hA : M.mem A C) (ha : M.MemberSubset A U) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.MemberSubset U T ∧ M.mem A T := by
  obtain ⟨T, hTC, hT⟩ := rd_insert_closed_l hKP hC hU hA
  have old x hx := (hT x).mpr (Or.inl hx)
  exact ⟨T, hTC, fun x hx y hy => old y (((hT x).mp hx).elim
    (fun hx => hu x hx y hy) (fun he => ha y (he ▸ hy))), old, (hT A).mpr (Or.inr rfl)⟩

theorem rd_transitive_enclosed_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem U T := by
  obtain ⟨T, htC, ht, _, hUT⟩ := rd_bounded_enclosed_l hKP hC hU hu hU (fun _ h => h)
  exact ⟨T, htC, ht, hUT⟩

theorem rd_finite_enclosed_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) (L : List M.Domain)
    (hL : ∀ A ∈ L, ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem A T) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.MemberSubset U T ∧ ∀ A ∈ L, M.mem A T := by
  induction L with
  | nil => exact ⟨U, hU, hu, fun _ h => h, fun _ h => (List.not_mem_nil h).elim⟩
  | cons A L ih =>
    obtain ⟨V, hVC, hv, hUV, hL'⟩ := ih (fun B hb => hL B (List.mem_cons_of_mem _ hb))
    obtain ⟨W, hWC, hw, hAW⟩ := hL A (List.mem_cons_self ..)
    obtain ⟨T, hTC, ht⟩ := hC.union_l hKP hVC hWC
    refine ⟨T, hTC, fun x hx y hy => (ht y).mpr (((ht x).mp hx).elim
      (fun hx => Or.inl (hv x hx y hy)) (fun hx => Or.inr (hw x hx y hy))),
      fun x hx => (ht x).mpr (Or.inl (hUV x hx)), fun B hb => ?_⟩
    exact (ht B).mpr ((List.mem_cons.mp hb).elim (fun he => Or.inr (he ▸ hAW)) (fun hb => Or.inl (hL' B hb)))

theorem rd_finite_bounded_l (hKP : M.Models KP) {C B : M.Domain} (hC : Rd_closed_d C)
    (hBC : M.mem B C) (hb : M.TransitiveSet B) (L : List M.Domain)
    (hL : ∀ A ∈ L, M.mem A C ∧ M.MemberSubset A B) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.MemberSubset B T ∧ ∀ A ∈ L, M.mem A T := by
  apply rd_finite_enclosed_l hKP hC hBC hb L
  intro A ha
  obtain ⟨T, htC, ht, _, hAT⟩ := rd_bounded_enclosed_l hKP hC hBC hb (hL A ha).1 (hL A ha).2
  exact ⟨T, htC, ht, hAT⟩

theorem rd_kpair_bound_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.MemberSubset U T ∧
      ∀ a b p, M.mem a U → M.mem b U → KPair_d M p a b → M.mem p T := by
  obtain ⟨V, hVC, hv, uv, p⟩ := rt_pair_hull_l hKP hC hU hu
  obtain ⟨T, hTC, ht, vt, q⟩ := rt_pair_hull_l hKP hC hVC hv
  exact ⟨T, hTC, ht, fun x hx => vt x (uv x hx), fun _ _ _ ha hb hp => rt_pair_to_opair_l p q ha hb hp⟩

theorem rd_relation_enclosed_l (hKP : M.Models KP) {C U R : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) (hR : M.mem R C)
    (hr : ∀ p, M.mem p R → ∃ a b, M.mem a U ∧ M.mem b U ∧ KPair_d M p a b) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem R T := by
  obtain ⟨B, hBC, hb, _, hp⟩ := rd_kpair_bound_l hKP hC hU hu
  obtain ⟨T, hTC, ht, _, hRT⟩ := rd_bounded_enclosed_l hKP hC hBC hb hR (by
    intro p hpR; obtain ⟨a, b, ha, hb, hq⟩ := hr p hpR; exact hp a b p ha hb hq)
  exact ⟨T, hTC, ht, hRT⟩

theorem rd_triples_enclosed_l (hKP : M.Models KP) {C U P : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) (hP : M.mem P C)
    (hp : ∀ p, M.mem p P → ∃ a b c, M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ Rd_triple_d p a b c) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem P T := by
  obtain ⟨A, hAC, ha, ua, pair⟩ := rd_kpair_bound_l hKP hC hU hu
  obtain ⟨B, hBC, hb, _, pair'⟩ := rd_kpair_bound_l hKP hC hAC ha
  obtain ⟨T, hTC, ht, _, hPT⟩ := rd_bounded_enclosed_l hKP hC hBC hb hP (by
    intro p hpP
    obtain ⟨a, b, c, ha, hb, hc, q, hq, hp⟩ := hp p hpP
    exact pair' a q p (ua a ha) (pair b c q hb hc hq) hp)
  exact ⟨T, hTC, ht, hPT⟩

theorem rd_union_enclosed_l (hKP : M.Models KP) {C A B V : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hA : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem A T)
    (hB : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem B T) (hv : M.IsUnionOfTwo V A B) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem V T := by
  obtain ⟨X, hXC, hx, hAX⟩ := hA
  obtain ⟨Y, hYC, hy, hBY⟩ := hB
  obtain ⟨W, hWC, hw⟩ := hC.union_l hKP (hc X hXC A hAX) (hc Y hYC B hBY)
  have he : W = V := hKP.1.eq_of_same_members _ _ fun x => (hw x).trans (hv x).symm
  subst W
  obtain ⟨U, hUC, hu⟩ := hC.union_l hKP hXC hYC
  have ht : M.TransitiveSet U := fun x hxU y hyx => (hu y).mpr (((hu x).mp hxU).elim
    (fun h => Or.inl (hx x h y hyx)) (fun h => Or.inr (hy x h y hyx)))
  obtain ⟨T, hTC, ht, _, hVT⟩ := rd_bounded_enclosed_l hKP hC hUC ht hWC (fun x hxV =>
    (hu x).mpr (((hv x).mp hxV).elim (fun h => Or.inl (hx A hAX x h)) (fun h => Or.inr (hy B hBY x h))))
  exact ⟨T, hTC, ht, hVT⟩

end YesMetaZFC.SetTheory.InnerModel
