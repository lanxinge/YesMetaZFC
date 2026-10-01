import YesMetaZFC.Model.Forcing.TwoStep.Flatten.RoundMatch

/-! # 摊平后求值还原的全局证明

把第二阶段名称性作为目标公式的前提，按三层原条目作内部归纳。泛型判据只在
根条件以下应用，保证实际摊平的二步条件能覆盖所有第二阶段条目。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
variable (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
include O hZF h L hT

private theorem flat_round_global_step_l {x}
    (ih : ∀ y, Entry_path_d M 3 x y → Flat_round_d M B R z b A T C y) : Flat_round_d M B R z b A T C x := by
  rintro hx f t p ⟨hf, ht, hp⟩
  have htN : Name_d M B t := curry_name_l M hZF (fun c p s hc hcp => by
    obtain ⟨hs, hp, _⟩ := (two_step_mem_l h hcp).mp hc
    exact ⟨hp.1, W, hs, h.closed⟩) ht
  let α : Formula 1 13 := .conj
    (two_step_m (.bound 8) (.bound 7) (.bound 6) (.bound 4) (.bound 12) (.bound 11) (.bound 3) (.bound 2) (.bound 1))
    (.conj (cond_order_m (.bound 2) (.bound 1) (.bound 2))
      (.conj (flat_m (.bound 8) (.bound 7) (.bound 6) (.bound 2) (.bound 10) .newest)
        (.conj (curry_m (.bound 8) (.bound 2) .newest (.bound 9))
          (.conj (below_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4))
            (flat_round_children_m (.bound 8) (.bound 7) (.bound 6) (.bound 4) (.bound 12) (.bound 11) (.bound 2) (.bound 10))))))
  have hα : α.FreeClosed := by
    simp only [α, Definitional.Formula.FreeClosed]
    exact ⟨two_step_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      cond_order_m_freeClosed _ _ _ rfl rfl rfl, flat_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl,
      curry_m_freeClosed _ _ _ _ rfl rfl rfl rfl, below_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl,
      flat_round_children_m_freeClosed _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl⟩
  let e : Fin 4 → Term 13 := fun i => .bound ⟨i.val + 9, by omega⟩
  let ρ := (((((fenv_l (round_env_l A T x t) B R z p).push b).push W).push C).push S).push f
  apply forces_of_generics_l round_body_m round_closed_l α hα e
    (.bound 8) (.bound 7) (.bound 6) (.bound 5) (fun _ => rfl) rfl rfl rfl rfl
    ?_ hZF ρ O (Fin.cases htN (Fin.cases hx (Fin.cases hT (fun _ => ⟨W, h.root, h.closed⟩)))) hp.1 hp.2.1 ?_
  · intro N hN η K _ _ _ hraw U hU hpU ξ hξ
    simp only [α, Formula.satisfies_conj_iff, two_step_sat_l hN.1, cond_order_sat_l hN.1,
      flat_sat_l N hN.1, curry_sat_l N hN.1, below_sat_l N hN.1, flat_round_children_sat_l hN.1] at hraw
    obtain ⟨hstep, J, hf', ht', hp', hi⟩ := hraw
    have hbU := hU.upward (η.bound 5) (η.bound 4) hpU hstep.base hp'.2.2
    exact (round_body_sat_l (extension_ext_l K hN hU) ξ).mpr (fun hx' q hq =>
      flat_round_step_l K hN hU hstep J hbU (hξ 3) (hξ 2) (qval_name_l (hξ 1)) hf' ht' (hξ 1) (hξ 0) hx' hi q hq)
  · simp only [α, Formula.satisfies_conj_iff, two_step_sat_l hZF.1, cond_order_sat_l hZF.1,
      flat_sat_l M hZF.1, curry_sat_l M hZF.1, below_sat_l M hZF.1, flat_round_children_sat_l hZF.1]
    exact ⟨h, L, hf, ht, hp, ih⟩

/-- 任意首阶段名称在根以下都被迫使：若它是第二阶段名称，则摊平后解释还原。 -/
theorem flat_round_force_l {x f t p} (hx : Name_d M B x) (hf : Flat_d M B R z C x f)
    (ht : Curry_d M B C f t) (hp : Below_d M B R z p b) : Round_force_d M B R z A T p x t := by
  let ρ : Env M 7 := ((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push A).push T).push C
  let φ : UnarySchema 7 := {
    body := flat_round_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ x : φ.denote ρ x ↔ Flat_round_d M B R z b A T C x := flat_round_sat_l hZF.1 (ρ.push x) _ _ _ _ _ _ _ _
  have hall := entry_path_ind_l hZF.1 (check_ind_l M hZF) 3 (by decide) φ ρ (fun x ih => (hφ x).mpr
    (flat_round_global_step_l O hZF h L hT (fun y hy => (hφ y).mp (ih y hy))))
  exact (hφ x).mp (hall x) hx f t p ⟨hf, ht, hp⟩

omit hT in
/-- 摊平后转换的名称，与原第二阶段名称在所有第二阶段条件上被迫使相等。 -/
theorem flat_round_l {U : M.Domain → Prop} (hU : Generic_d M B R z U) (hb : U b)
    {Q D a d : (extension_l M hZF B R z U).Domain} {x f t}
    (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    (hf : Flat_d M B R z C x f) (ht : Curry_d M B C f t)
    (hxa : Qval_d M B R z U x a) (htd : Qval_d M B R z U t d)
    (ha : Name_d (extension_l M hZF B R z U) Q a) (q) (hq : q ∈ Q) :
    Eq_force_d (extension_l M hZF B R z U) Q D Q q a d :=
  (round_force_truth_l O hZF hU hA hT hxa htd).mp
    ⟨b, hb, flat_round_force_l O hZF h L (qval_name_l hT) (qval_name_l hxa) hf ht
      (below_refl_l O (hU.proper b hb).1 (hU.proper b hb).2)⟩ ha q hq

end YesMetaZFC.Model.Forcing.Internal
