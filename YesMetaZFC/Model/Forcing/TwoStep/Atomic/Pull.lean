import YesMetaZFC.Model.Forcing.TwoStep.Atomic.PullMatch
import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Push

/-! # 嵌套等号反射为原二步等号

先用有限参数反射取得原模型的匹配见证，再在名称闭支撑上分离实际双模拟。
其对称性及两侧匹配均已证明，因此嵌套等号与原二步等号精确等价。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
variable (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
include O hZF h L hT

/-- 泛型中取得的匹配反射回原模型；调用者无需提供任何外部枚举或泛型。 -/
theorem curry_pull_match_l {x y c a d q} (hx : Name_d M C x) (hy : Name_d M C y)
    (hc : M.mem c C) (he : Curry_pull_d M B R z A T C c x y)
    (had : Entry_d M a d x) (hq : Below_d M C S C q c) (hqd : Entry_d M q d S) :
    Curry_pull_wit_d M B R z A T C S q a y := by
  obtain ⟨p, s, hqp, _, hp, _⟩ := (h.conditions q).mp hq.1
  let ρ₀ : Env M 9 := ((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push A).push T).push W).push C).push S
  let ρ := (((((((ρ₀.push x).push y).push c).push a).push d).push q).push p).push s
  let α : Formula 1 17 := .conj
    (two_step_m (.bound 16) (.bound 15) (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8))
    (.conj (cond_order_m (.bound 9) (.bound 8) (.bound 9))
      (.conj (name_m (.bound 16) (.bound 11)) (.conj (name_m (.bound 9) (.bound 7))
        (.conj (name_m (.bound 9) (.bound 6)) (.conj (.mem (.bound 5) (.bound 9))
          (.conj (curry_pull_m (.bound 16) (.bound 15) (.bound 14) (.bound 12) (.bound 11) (.bound 9) (.bound 5) (.bound 7) (.bound 6))
            (.conj (entry_m (.bound 4) (.bound 3) (.bound 7))
              (.conj (below_m (.bound 9) (.bound 8) (.bound 9) (.bound 2) (.bound 5))
                (.conj (entry_m (.bound 2) (.bound 3) (.bound 8)) (kpair_m (.bound 2) (.bound 1) .newest))))))))))
  let β : Formula 1 17 := curry_pull_wit_m (.bound 16) (.bound 15) (.bound 14) (.bound 12) (.bound 11)
    (.bound 9) (.bound 8) (.bound 2) (.bound 4) (.bound 6)
  have hα : α.FreeClosed := by
    simp only [α, Definitional.Formula.FreeClosed]
    exact ⟨two_step_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      cond_order_m_freeClosed _ _ _ rfl rfl rfl, name_m_freeClosed _ _ rfl rfl,
      name_m_freeClosed _ _ rfl rfl, name_m_freeClosed _ _ rfl rfl, ⟨rfl, rfl⟩,
      curry_pull_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      entry_m_freeClosed _ _ _ rfl rfl rfl, below_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
      entry_m_freeClosed _ _ _ rfl rfl rfl, kpair_m_freeClosed _ _ _ rfl rfl rfl⟩
  have hβ : β.FreeClosed := curry_pull_wit_m_freeClosed _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  apply (curry_pull_wit_sat_l hZF.1 ρ (.bound 16) (.bound 15) (.bound 14) (.bound 12) (.bound 11)
    (.bound 9) (.bound 8) (.bound 2) (.bound 4) (.bound 6)).mp
  apply source_of_generics_l α β hα hβ (.bound 16) (.bound 15) (.bound 14) (.bound 1) rfl rfl rfl rfl
    ?_ hZF ρ O hp.1 hp.2.1 ?_
  · intro N hN η K hraw U hU hpU
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, two_step_sat_l hN.1,
      cond_order_sat_l hN.1, name_sat_l N hN.1, curry_pull_sat_l hN.1, entry_sat_l N hN.1,
      below_sat_l N hN.1, kpair_sat_l N hN.1] at hraw
    obtain ⟨hstep, J, hT', hx', hy', hc', he', had', hq', hqd', hqp'⟩ := hraw
    exact (curry_pull_wit_sat_l hN.1 η _ _ _ _ _ _ _ _ _ _).mpr
      (curry_pull_generic_match_l K hN hU hstep J hT' hx' hy' hc' he' had' hq' hqd' hqp' hpU)
  · simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, two_step_sat_l hZF.1,
      cond_order_sat_l hZF.1, name_sat_l M hZF.1, curry_pull_sat_l hZF.1, entry_sat_l M hZF.1,
      below_sat_l M hZF.1, kpair_sat_l M hZF.1]
    exact ⟨h, L, hT, hx, hy, hc, he, had, hq, hqd, hqp⟩

/-- 条件 (p,s) 的嵌套等号证书在原模型内构成实际二步双模拟。 -/
theorem curry_forces_eq_pull_l {x y c p s u v} (hx : Name_d M C x) (hy : Name_d M C y)
    (hc : M.mem c C) (hcp : KPair_d M c p s) (hu : Curry_d M B C x u) (hv : Curry_d M B C y v)
    (he : Iter_eq_d M B R z A T p s u v) : Eq_force_d M C S C c x y := by
  obtain ⟨Z, hxZ, hyZ, hZ⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hx hy
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push A).push T).push C
  let φ : BinarySchema 7 := {
    body := curry_pull_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨F, hF⟩ := rel_separation_l hZF φ ρ C Z
  have hf q a d : Rel_d M F q a d ↔ M.mem q C ∧ M.mem a Z ∧ M.mem d Z ∧ Curry_pull_d M B R z A T C q a d := by
    simpa only [BinarySchema.denote, φ, curry_pull_sat_l hZF.1] using! hF q a d
  have symm {q a d} (had : Rel_d M F q a d) : Rel_d M F q d a := by
    obtain ⟨hq, ha, hd, had⟩ := (hf q a d).mp had
    exact (hf q d a).mpr ⟨hq, hd, ha, curry_pull_symm_l had⟩
  have forth q a d (had : Rel_d M F q a d) : Match_d M false C S C F q a d := by
    obtain ⟨hq, ha, hd, had⟩ := (hf q a d).mp had
    intro e f hef r hr hrf
    obtain ⟨j, v, w, hj, hvw, hjw, hev⟩ := curry_pull_match_l O hZF h L hT ⟨Z, ha, hZ⟩ ⟨Z, hd, hZ⟩ hq had hef hr hrf
    exact ⟨j, v, w, hj, hvw, hjw, (hf j e v).mpr
      ⟨hj.1, (supp_entry_l M hZ ha hef).1, (supp_entry_l M hZ hd hvw).1, hev⟩⟩
  refine ⟨hc, F, ?_, (hf c x y).mpr ⟨hc, hxZ, hyZ, p, s, u, v, hcp, hu, hv, Or.inl he⟩⟩
  intro q a d had
  refine ⟨forth q a d had, ?_⟩
  intro e f hef r hr hrf
  obtain ⟨j, v, w, hj, hvw, hjw, hev⟩ := forth q d a (symm had) e f hef r hr hrf
  exact ⟨j, v, w, hj, hvw, hjw, symm hev⟩

/-- 原二步等号与嵌套等号在每个真实二步条件上精确等价。 -/
theorem curry_forces_eq_iff_l {x y c p s u v} (hx : Name_d M C x) (hy : Name_d M C y)
    (hc : M.mem c C) (hcp : KPair_d M c p s) (hu : Curry_d M B C x u) (hv : Curry_d M B C y v) :
    Eq_force_d M C S C c x y ↔ Iter_eq_d M B R z A T p s u v :=
  ⟨fun he => curry_forces_eq_l O hZF h L hT hx hy he hcp hu hv,
    curry_forces_eq_pull_l O hZF h L hT hx hy hc hcp hu hv⟩

omit hT in
/-- 第一扩张中的等号力迫可反射到首坐标仍被泛型接受的二步加强。 -/
theorem curry_eq_pull_l {U : M.Domain → Prop} (hU : Generic_d M B R z U)
    {Q D q a d : (extension_l M hZF B R z U).Domain} {x y c p s u v}
    (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    (hx : Name_d M C x) (hy : Name_d M C y) (hc : M.mem c C)
    (hcp : KPair_d M c p s) (hp : U p) (hu : Curry_d M B C x u) (hv : Curry_d M B C y v)
    (hsq : Qval_d M B R z U s q) (hua : Qval_d M B R z U u a) (hvd : Qval_d M B R z U v d)
    (he : Eq_force_d (extension_l M hZF B R z U) Q D Q q a d) :
    ∃ w r, Below_d M C S C w c ∧ KPair_d M w r s ∧ U r ∧ Eq_force_d M C S C w x y := by
  obtain ⟨k, hk, hit⟩ := (iter_eq_truth_l O hZF hU hA hT hsq hua hvd).mpr he
  obtain ⟨r, hr, hrk, hrp⟩ := hU.directed k p hk hp
  have hr' := hU.proper r hr
  have hρ : ∀ t : Term 5, Name_d M B (t.eval (iter_eq_env_l A T s u v)) := by
    intro t
    cases t with
    | free _ => exact qval_name_l hA
    | bound i => exact Fin.cases (qval_name_l hvd) (Fin.cases (qval_name_l hua)
        (Fin.cases (qval_name_l hsq) (Fin.cases (qval_name_l hT) (fun _ => qval_name_l hA)))) i
  have hit' : Iter_eq_d M B R z A T r s u v :=
    (forces_regular_l O hZF iter_eq_body_m (iter_eq_env_l A T s u v) hρ).1 k r (hU.proper k hk).1 ⟨hr'.1, hr'.2, hrk⟩ hit
  obtain ⟨w, hwr, hw⟩ := two_step_lift_l O hZF h L (qval_name_l hT) hc hcp ⟨hr'.1, hr'.2, hrp⟩
  exact ⟨w, r, hw, hwr, hr, curry_forces_eq_pull_l O hZF h L (qval_name_l hT) hx hy hw.1 hwr hu hv hit'⟩

end YesMetaZFC.Model.Forcing.Internal
