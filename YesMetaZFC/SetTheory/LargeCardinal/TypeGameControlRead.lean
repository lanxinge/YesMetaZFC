import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssuedStart

/-! # 从控制记录读取真实首轮输入

只解包同一条有限公式的量词。此处仅需传递层已有的外延性与配对解释，
不对反射层假定 ZF；获胜策略、开局合法性和重置构造均已由原模型给出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include hE

theorem tg_control_start_l (ρ : Env M 19) (valid : Formula.satisfies ρ tg_control0_m) :
    ∃ a h j, M.mem a (ρ.bound 12) ∧ Rd_entry_d (ρ.bound 1) a (ρ.bound 17) ∧
      Fseq_end_d I (ρ.bound 0) h (ρ.bound 1) a ∧ M.mem j (ρ.bound 0) ∧
      M.SuccessorOf j (ρ.bound 1) ∧ Fn0_d j (ρ.bound 12) h ∧ M.mem h (ρ.bound 18) ∧
      M.IsOrdinalDivision I j (ρ.bound 4) (ρ.bound 1) (ρ.bound 2) ∧
      Tg_event_d I (ρ.bound 4) (ρ.bound 1) (ρ.bound 1) h a ∧
      ∃ v : Fin 38 → M.Domain, Formula.satisfies (⟨v, ρ.free⟩ : Env M 38) tg_seed0_m ∧
        v 0 = ρ.bound 0 ∧ v 1 = ρ.bound 1 ∧ v 2 = ρ.bound 5 ∧ v 3 = ρ.bound 7 ∧ v 4 = ρ.bound 8 ∧
        v 6 = ρ.bound 1 ∧ v 23 = v 5 ∧ v 24 = ρ.bound 1 ∧ v 25 = ρ.bound 1 ∧ v 26 = ρ.bound 1 ∧
        (∃ ℓ, Tg_aux_data_d a ℓ (v 25) (v 5) (v 18)) ∧
        Tg_ee_data_d (ρ.bound 9) (v 5) (v 7) (v 14) (v 15) (v 16) ⟨v 27, v 28, v 29, v 30⟩ ∧
        Tg_program_data_d (ρ.bound 10) (v 7) (v 20) (v 22) (Fin.cases (v 31) (Fin.cases (v 32) (Fin.cases (v 33)
          (Fin.cases (v 34) (Fin.cases (v 35) (Fin.cases (v 36) (fun _ => v 37))))))) ∧
        M.mem (ρ.bound 6) (v 14) ∧ ∃ ℓ,
          Formula.satisfies (tg_issued_start_env_d ρ ⟨v, ρ.free⟩ a h ℓ j) tg_issued0_m := by
  have control := valid
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at valid
  have start := valid.2.2.2.2.2.1
  simp only [tg_start_control_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hE, fseq_end_sat_l I hE, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_isOrdinalDivision_iff I hE,
    fn0_sat_l hE, tg_event_sat_l I hE, tg_reset_result_m, Formula.satisfies_bind, Definitional.Term.eval_weaken] at start
  obtain ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event, prepared⟩ := start
  let ε : Env M 10 := ⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 5, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10,
    a, ρ.bound 1, ρ.bound 6].get i, ρ.free⟩
  have prepared : Formula.satisfies ε tg_reset_result0_m := by
    apply (Formula.closed_env_l tg_reset_result0_m tg_reset_result0_closed_l (ρ := _) (η := ε) ?_).mp prepared
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))) i
  obtain ⟨v, body⟩ := (rt_exists_sat_l (n := 38) ε tg_reset_body0_m).mp prepared
  obtain ⟨seed, links⟩ := (Formula.satisfies_conj_iff ..).mp body
  have seed : Formula.satisfies (⟨v, ρ.free⟩ : Env M 38) tg_seed0_m :=
    (Formula.closed_env_l tg_seed0_m tg_seed0_closed_l (ρ := _) (η := ⟨v, ρ.free⟩)
      (funext (rt_push_new_l ε v))).mp ((Formula.satisfies_rename ..).mp seed)
  simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, tg_aux_data_sat_l hE, tg_ee_data_sat_l hE, tg_program_data_sat_l hE, tt_eval_cases_l,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken] at links
  obtain ⟨hw, he, hd, hS, hν, hk, hb, hs, ht, hg, move, elastic, program, letters⟩ := links
  obtain ⟨ℓ, move⟩ := move
  refine ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, event, v, seed,
    hw, he, hd, hS, hν, hk, hb, hs, ht, hg, ⟨ℓ, move⟩, elastic, program, letters rfl,
    ℓ, tg_issued_start_l I hE ρ ⟨v, ρ.free⟩ a h ℓ j control hj fn next clock event endt ?_ seed hw he hd hk ht move elastic program⟩
  simp only [tg_aux_m, Formula.satisfies_bind] at aux
  apply (Formula.closed_env_l tg_aux0_m tg_aux0_closed_l (ρ := _) (η := _) ?_).mp aux
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
