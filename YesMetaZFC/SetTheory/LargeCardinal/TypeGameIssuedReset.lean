import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssued

/-! # 任意已发出重置走法的实际更新输入

从同一份原历史取回辅助合法性，再调用原控制记录中的全称重置定理。
因此零轮和以后所有重置轮使用同一个构造，反射层只需外延性与配对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include I hE

theorem tg_issued_reset_l (ρ : Env M 46) (valid : Formula.satisfies ρ tg_issued0_m)
    (empty : ρ.bound 23 = ρ.bound 1) :
    ∃ ε : Env M 38, Formula.satisfies ε tg_seed0_m ∧
      (∀ i : Fin 5, ε.bound (i.castAdd 33) = [ρ.bound 0, ρ.bound 1, ρ.bound 5, ρ.bound 7, ρ.bound 8].get i) ∧
      ε.bound 6 = ρ.bound 1 ∧ ε.bound 23 = ε.bound 5 ∧ ε.bound 24 = ρ.bound 1 ∧
      ε.bound 25 = ρ.bound 1 ∧ ε.bound 26 = ρ.bound 1 ∧
      Tg_aux_data_d (ρ.bound 21) (ρ.bound 22) (ε.bound 25) (ε.bound 5) (ε.bound 18) ∧
      Tg_ee_data_d (ρ.bound 9) (ε.bound 5) (ε.bound 7) (ε.bound 14) (ε.bound 15) (ε.bound 16)
        ⟨ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30⟩ ∧
      Tg_program_data_d (ρ.bound 10) (ε.bound 7) (ε.bound 20) (ε.bound 22)
        (Fin.cases (ε.bound 31) (Fin.cases (ε.bound 32) (Fin.cases (ε.bound 33) (Fin.cases (ε.bound 34)
          (Fin.cases (ε.bound 35) (Fin.cases (ε.bound 36) (fun _ => ε.bound 37))))))) ∧
      (ρ.bound 19 = ρ.bound 1 → M.mem (ρ.bound 6) (ε.bound 14)) := by
  have state := (tg_issued_sat_l I hE ρ).mp valid
  have original := state.auxiliary
  simp only [tg_issued_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_aux_m, Formula.satisfies_bind] at original
  obtain ⟨h, _, aux⟩ := original
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have reset := control.2.2.2.2.1
  simp only [tg_reset_control_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, tg_aux_data_sat_l hE, tg_aux_m, Formula.satisfies_bind,
    tg_reset_result_m] at reset
  have move : Tg_aux_data_d (ρ.bound 21) (ρ.bound 22) (ρ.bound 1) (ρ.bound 24) (ρ.bound 25) := empty ▸ state.move
  have prepared := reset (ρ.bound 19) h (ρ.bound 21) (by
    apply (Formula.closed_env_l tg_aux0_m tg_aux0_closed_l (ρ := _) (η := _) ?_).mp aux
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))))))))) i)
    ⟨ρ.bound 22, ρ.bound 24, ρ.bound 25, move⟩
  let χ : Env M 10 := ⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 5, ρ.bound 7, ρ.bound 8,
    ρ.bound 9, ρ.bound 10, ρ.bound 21, ρ.bound 19, ρ.bound 6].get i, ρ.free⟩
  have prepared : Formula.satisfies χ tg_reset_result0_m := by
    apply (Formula.closed_env_l tg_reset_result0_m tg_reset_result0_closed_l (ρ := _) (η := χ) ?_).mp prepared
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))) i
  obtain ⟨v, body⟩ := (rt_exists_sat_l (n := 38) χ tg_reset_body0_m).mp prepared
  obtain ⟨seed, links⟩ := (Formula.satisfies_conj_iff ..).mp body
  have seed : Formula.satisfies (⟨v, ρ.free⟩ : Env M 38) tg_seed0_m :=
    (Formula.closed_env_l tg_seed0_m tg_seed0_closed_l (ρ := _) (η := ⟨v, ρ.free⟩)
      (funext (rt_push_new_l χ v))).mp ((Formula.satisfies_rename ..).mp seed)
  simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, tg_aux_data_sat_l hE, tg_ee_data_sat_l hE, tg_program_data_sat_l hE,
    tt_eval_cases_l, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken] at links
  obtain ⟨hw, he, hd, hS, hν, hk, hb, hs, ht, hg, ⟨ℓ, move⟩, elastic, program, letters⟩ := links
  have eq : ℓ = ρ.bound 22 := (move.unique_l state.move).1
  refine ⟨⟨v, ρ.free⟩, seed, ?_, hk, hb, hs, ht, hg, eq ▸ move, elastic, program, letters⟩
  intro i
  exact Fin.cases hw (Fin.cases he (Fin.cases hd (Fin.cases hS (Fin.cases hν (fun k => Fin.elim0 k))))) i

end YesMetaZFC.SetTheory.LargeCardinal
