import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePositionIssue

/-! # 任意内部轮号上的实数落子与下一轮

偶数轮使用给定的对手字母，奇数轮读取原 II 策略。两种情况都在同一
反射层内追加历史并增加轮号，随后读取原策略的下一辅助走法和原程序表，
返回阶段零位置及下一份完整辅助记录。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include I hE

theorem tg_position_next_l (ρ : Env M 22) (valid : Formula.satisfies ρ (tg_position0_m 2))
    (x : M.Domain) (hx : M.mem x (ρ.bound 6)) :
    ∃ v t j n, M.mem v (ρ.bound 6) ∧
      (Formula.satisfies ρ (gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v = x) ∧
      (¬ Formula.satisfies ρ (gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
        Rd_entry_d (ρ.bound 20) v (ρ.bound 17)) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, t, ρ.bound 20, v].get i, fun _ => v⟩ : Env M 4)
        (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
      M.SuccessorOf n (ρ.bound 19) ∧
      Formula.satisfies (tg_position_env_d
        ⟨fun i => ρ.bound (i.castAdd 3), fun _ => ρ.bound 0⟩ n t j) (tg_position0_m 0) ∧
      ∃ θ : Env M 46, (∀ i : Fin 19, θ.bound (i.castAdd 27) = ρ.bound (i.castAdd 3)) ∧
        θ.bound 19 = n ∧ Formula.satisfies θ tg_issued0_m ∧ Rd_entry_d t (θ.bound 21) (ρ.bound 17) ∧
        Formula.satisfies (⟨fun i => [ρ.bound 0, θ.bound 20, t, θ.bound 21].get i,
          fun _ => θ.bound 21⟩ : Env M 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
  classical
  have state := (tg_position_sat_l I hE 2 ρ).mp valid
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have digit := control.2.2.2.2.2.2.2.1
  simp only [tg_digit_control_m, tg_digit_end_m, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_isOrdinalDivision_iff I hE, gm_even_sat_l I hE, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, fseq_end_sat_l I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hE, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken] at digit
  have step := digit (ρ.bound 21) state.time (ρ.bound 19) state.round (ρ.bound 20)
    state.position state.history state.clock
  let χ : Env M 19 := ⟨fun i => ρ.bound (i.castAdd 3), fun _ => ρ.bound 0⟩
  have issue (n t j : M.Domain) (next : Formula.satisfies (tg_position_env_d χ n t j) (tg_position0_m 0)) :
      ∃ θ : Env M 46, (∀ i : Fin 19, θ.bound (i.castAdd 27) = ρ.bound (i.castAdd 3)) ∧
        θ.bound 19 = n ∧ Formula.satisfies θ tg_issued0_m ∧ Rd_entry_d t (θ.bound 21) (ρ.bound 17) ∧
        Formula.satisfies (⟨fun i => [ρ.bound 0, θ.bound 20, t, θ.bound 21].get i,
          fun _ => θ.bound 21⟩ : Env M 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
    obtain ⟨θ, head, num, valid, value, hist⟩ := tg_position_issue_l I hE _ next
    have left (i : Fin 19) : (tg_position_env_d χ n t j).bound (i.castAdd 3) = χ.bound i := by
      simp only [tg_position_env_d, Fin.addCases_left]
    have right (i : Fin 3) : (tg_position_env_d χ n t j).bound (Fin.natAdd 19 i) = [n, t, j].get i := by
      simp only [tg_position_env_d, Fin.addCases_right]
    have e₀ : (tg_position_env_d χ n t j).bound 0 = ρ.bound 0 := left 0
    have e₁₇ : (tg_position_env_d χ n t j).bound 17 = ρ.bound 17 := left 17
    have e₁₉ : (tg_position_env_d χ n t j).bound 19 = n := right 0
    have e₂₀ : (tg_position_env_d χ n t j).bound 20 = t := right 1
    refine ⟨θ, fun i => (head i).trans (left i), num.trans e₁₉, valid, e₂₀ ▸ e₁₇ ▸ value, ?_⟩
    apply (Formula.closed_env_l _ (by simp -implicitDefEqProofs) (ρ := _) (η := _) ?_).mp hist
    funext i
    exact Fin.cases e₀ (Fin.cases rfl (Fin.cases e₂₀ (Fin.cases rfl (fun a => Fin.elim0 a)))) i
  by_cases even : Gm_even_d I (ρ.bound 0) (ρ.bound 19)
  · obtain ⟨t, j, n, endt, hj, hn, _, succ, fn, position, clock, _⟩ := step.1 even x hx
    have next := tg_position_build_l I hE 0 χ n t j state.control hn hj fn position clock
    exact ⟨x, t, j, n, hx, fun _ => rfl, fun no => (no ((gm_even_sat_l I hE ..).mpr even)).elim,
      (fseq_end_sat_l I hE ..).mpr endt, succ,
      next, issue n t j next⟩
  · obtain ⟨v, hv, value, t, j, n, endt, hj, hn, _, succ, fn, position, clock, _⟩ := step.2 even
    have next := tg_position_build_l I hE 0 χ n t j state.control hn hj fn position clock
    exact ⟨v, t, j, n, hv, fun yes => (even ((gm_even_sat_l I hE ..).mp yes)).elim, fun _ => value,
      (fseq_end_sat_l I hE ..).mpr endt, succ,
      next, issue n t j next⟩

end YesMetaZFC.SetTheory.LargeCardinal
