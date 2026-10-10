import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Match

/-! # 二步等号力迫向嵌套等号力迫传输

对子名称使用原模型内的实际条目归纳；归纳步骤通过有限参数泛型判据提升。
因此结论对任意原 ZF 模型成立，不增加外部可数性或良基性假设。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
variable (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
include O hZF h L hT

private theorem curry_eq_global_step_l {x}
    (ih : ∀ a c, Entry_d M a c x → Curry_eq_d M B R z A T C S a) : Curry_eq_d M B R z A T C S x := by
  intro hx y c p s u v hh
  obtain ⟨hy, hcp, he, hu, hv⟩ := hh
  obtain ⟨hs, hp, _⟩ := (two_step_mem_l h hcp).mp he.1
  have name {x t} (ht : Curry_d M B C x t) : Name_d M B t :=
    curry_name_l M hZF (fun c p s hc hcp => by
      obtain ⟨hs, hp, _⟩ := (two_step_mem_l h hcp).mp hc
      exact ⟨hp.1, W, hs, h.closed⟩) ht
  let α : Formula 1 16 := .conj
    (two_step_m (.bound 10) (.bound 9) (.bound 8) (.bound 6) (.bound 15) (.bound 14) (.bound 5) (.bound 4) (.bound 3))
    (.conj (cond_order_m (.bound 4) (.bound 3) (.bound 4))
      (.conj (name_m (.bound 4) (.bound 2)) (.conj (name_m (.bound 4) (.bound 1))
        (.conj (eq_force_m (.bound 4) (.bound 3) (.bound 4) .newest (.bound 2) (.bound 1))
          (.conj (kpair_m .newest (.bound 7) (.bound 13))
            (.conj (curry_m (.bound 10) (.bound 4) (.bound 2) (.bound 12))
              (.conj (curry_m (.bound 10) (.bound 4) (.bound 1) (.bound 11))
                (curry_children_m (.bound 10) (.bound 9) (.bound 8) (.bound 15) (.bound 14) (.bound 4) (.bound 3) (.bound 2)))))))))
  have hα : α.FreeClosed := by
    simp only [α, Definitional.Formula.FreeClosed]
    exact ⟨two_step_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      cond_order_m_freeClosed _ _ _ rfl rfl rfl, name_m_freeClosed _ _ rfl rfl,
      name_m_freeClosed _ _ rfl rfl, eq_force_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl,
      kpair_m_freeClosed _ _ _ rfl rfl rfl, curry_m_freeClosed _ _ _ _ rfl rfl rfl rfl,
      curry_m_freeClosed _ _ _ _ rfl rfl rfl rfl,
      curry_children_m_freeClosed _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl⟩
  let e : Fin 5 → Term 16 := fun i => .bound ⟨i.val + 11, by omega⟩
  let ρ₀ := iter_eq_env_l A T s u v
  let ρ := (((((((fenv_l ρ₀ B R z p).push b).push W).push C).push S).push x).push y).push c
  apply forces_of_generics_l iter_eq_body_m iter_eq_closed_l α hα e
    (.bound 10) (.bound 9) (.bound 8) (.bound 7) (fun _ => rfl) rfl rfl rfl rfl
    ?_ hZF ρ O (Fin.cases (name hv) (Fin.cases (name hu)
      (Fin.cases (show Name_d M B s from ⟨W, hs, h.closed⟩) (Fin.cases hT (fun _ => ⟨W, h.root, h.closed⟩))))) hp.1 hp.2.1 ?_
  · intro N hN η K _ _ _ hraw U hU hpU ξ hξ
    simp only [α, Formula.satisfies_conj_iff, two_step_sat_l hN.1, cond_order_sat_l hN.1,
      name_sat_l N hN.1, eq_force_sat_l N hN.1, kpair_sat_l N hN.1,
      curry_sat_l N hN.1, curry_children_sat_l hN.1] at hraw
    obtain ⟨hstep, J, hx', hy', he', hpair, hu', hv', hi⟩ := hraw
    let E := extension_l N hN (η.bound 10) (η.bound 9) (η.bound 8) U
    exact (eq_force_sat_l E (extension_ext_l K hN hU) ξ _ _ _ _ _ _).mpr
      (curry_eq_step_l K hN hU hstep J (hξ 4) (hξ 3) hx' hy' he' hpair hpU hu' hv' (hξ 2) (hξ 1) (hξ 0) hi)
  · simp only [α, Formula.satisfies_conj_iff, two_step_sat_l hZF.1, cond_order_sat_l hZF.1,
      name_sat_l M hZF.1, eq_force_sat_l M hZF.1, kpair_sat_l M hZF.1,
      curry_sat_l M hZF.1, curry_children_sat_l hZF.1]
    exact ⟨h, L, hx, hy, he, hcp, hu, hv, ih⟩

/-- 二步条件 (p,s) 迫使原名称相等，则 p 迫使 s 在第二阶段迫使转换名称相等。 -/
theorem curry_forces_eq_l {x y c p s u v} (hx : Name_d M C x) (hy : Name_d M C y)
    (he : Eq_force_d M C S C c x y) (hcp : KPair_d M c p s)
    (hu : Curry_d M B C x u) (hv : Curry_d M B C y v) : Iter_eq_d M B R z A T p s u v := by
  let ρ : Env M 7 := ((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push A).push T).push C).push S
  let φ : UnarySchema 7 := {
    body := curry_eq_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ a : φ.denote ρ a ↔ Curry_eq_d M B R z A T C S a := curry_eq_sat_l hZF.1 (ρ.push a) _ _ _ _ _ _ _ _
  have hall := entry_ind_l (check_ind_l M hZF) φ ρ (fun a ih => (hφ a).mpr
    (curry_eq_global_step_l O hZF h L hT (fun d f hd => (hφ d).mp (ih d f hd))))
  exact (hφ x).mp (hall x) hx y c p s u v ⟨hy, hcp, he, hu, hv⟩

omit hT in
/-- 首坐标进入泛型后，二步等号成为第一扩张内第二阶段的实际等号力迫。 -/
theorem curry_eq_push_l {U : M.Domain → Prop} (hU : Generic_d M B R z U)
    {Q D q a d : (extension_l M hZF B R z U).Domain} {x y c p s u v}
    (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    (hx : Name_d M C x) (hy : Name_d M C y) (he : Eq_force_d M C S C c x y)
    (hcp : KPair_d M c p s) (hp : U p) (hu : Curry_d M B C x u) (hv : Curry_d M B C y v)
    (hsq : Qval_d M B R z U s q) (hua : Qval_d M B R z U u a) (hvd : Qval_d M B R z U v d) :
    Eq_force_d (extension_l M hZF B R z U) Q D Q q a d :=
  (iter_eq_truth_l O hZF hU hA hT hsq hua hvd).mp
    ⟨p, hp, curry_forces_eq_l O hZF h L (qval_name_l hT) hx hy he hcp hu hv⟩

end YesMetaZFC.Model.Forcing.Internal
