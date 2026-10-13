import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssued
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRound

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
      (ρ.bound 19 = ρ.bound 1 → M.mem (ρ.bound 6) (ε.bound 14)) ∧
      ∀ w : Fin 16 → M.Domain, Tg_request_d ρ.bound (tg_round_env_d ε w).bound := by
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
  have he : v 1 = ρ.bound 1 := he
  have hk : v 6 = ρ.bound 1 := hk
  have eq : ℓ = ρ.bound 22 := (move.unique_l state.move).1
  have eκ : v 5 = ρ.bound 24 := (move.unique_l state.move).2.2.1
  have eu : v 18 = ρ.bound 25 := (move.unique_l state.move).2.2.2
  have shape := seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isSuccessor_iff] at shape
  have zero : ∀ x, ¬ M.mem x (ρ.bound 1) := he ▸ shape.2.1
  have ek : ρ.bound 26 = ρ.bound 1 := hE.eq_of_same_members _ _ (fun i => iff_of_false
    (fun hi => (state.labels.2.1 i hi).elim fun _ h => h.2.elim fun p hp => zero p (empty ▸ hp.2)) (zero i))
  have first : M.SuccessorOf (v 7) (v 6) := shape.2.2.2.2.2.2.2.1
  have el : v 7 = ρ.bound 27 := first.eq hE (hk.symm ▸ (ek ▸ state.first))
  have last : M.SuccessorOf (v 8) (v 7) := shape.2.2.2.2.2.2.2.2.1
  have en : v 8 = ρ.bound 28 := last.eq hE (el.symm ▸ state.last)
  have tables := control.1
  simp only [tg_tables_m, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE] at tables
  have ee : Tg_ee_data_d (ρ.bound 9) (ρ.bound 24) (ρ.bound 27)
      (v 14) (v 15) (v 16) ⟨v 27, v 28, v 29, v 30⟩ := eκ ▸ el ▸ elastic
  obtain ⟨_, eU, eD, _⟩ := ee.unique_l hE tables.2.2.1 state.elastic
  have pp : Tg_program_data_d (ρ.bound 10) (ρ.bound 27) (v 20) (v 22)
      (Fin.cases (v 31) (Fin.cases (v 32) (Fin.cases (v 33) (Fin.cases (v 34)
        (Fin.cases (v 35) (Fin.cases (v 36) (fun _ => v 37))))))) := el ▸ program
  obtain ⟨eb, ez, ep⟩ := pp.unique_l hE tables.2.2.2 state.program
  refine ⟨⟨v, ρ.free⟩, seed, ?_, hk, hb, hs, ht, hg, eq ▸ move, elastic, program, letters, ?_⟩
  · intro i
    exact Fin.cases hw (Fin.cases he (Fin.cases hd (Fin.cases hS (Fin.cases hν (fun k => Fin.elim0 k))))) i
  · intro w i
    exact Fin.cases hw (Fin.cases he (Fin.cases (hk.trans ek.symm) (Fin.cases el (Fin.cases en
      (Fin.cases eb (Fin.cases ez (Fin.cases (congrFun ep 0) (Fin.cases (congrFun ep 1)
        (Fin.cases (congrFun ep 2) (Fin.cases (congrFun ep 3) (Fin.cases (congrFun ep 4)
          (Fin.cases (congrFun ep 5) (Fin.cases (congrFun ep 6) (Fin.cases eκ
            (Fin.cases eU (Fin.cases eD (Fin.cases eu (Fin.cases (ht.trans empty.symm)
              (fun j => Fin.elim0 j))))))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
