import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssued
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswerBuild

/-! # 已发出的辅助走法得到回答后的实际历史

回答沿原表项检查规则 (7)，再用同一控制记录追加历史。这里只需要外延性
及配对解释；因此也适用于不满足 ZF 的后继反射层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include hE

theorem tg_issued_answer_l (ρ : Env M 46) (valid : Formula.satisfies ρ tg_issued0_m)
    {τ w B U D r m b f q : M.Domain}
    (below : M.mem τ (ρ.bound 5))
    (request : Formula.satisfies (⟨fun i => [ρ.bound 0, τ, ρ.bound 26, ρ.bound 1, ρ.bound 1].get i,
      fun _ => ρ.bound 0⟩ : Env M 5) tg_query_request0_m)
    (query : Tg_query_data_d (ρ.bound 11) τ (ρ.bound 26) (ρ.bound 1) (ρ.bound 1) B U D r m b f q)
    (reply : Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 27, ρ.bound 28, ρ.bound 24, τ,
      ρ.bound 30, ρ.bound 31, D, ρ.bound 25, w, ρ.bound 36, ρ.bound 37, r, b, f,
      ρ.bound 38, ρ.bound 39, ρ.bound 40, ρ.bound 41, ρ.bound 42, ρ.bound 43, ρ.bound 44].get i,
      fun _ => ρ.bound 0⟩ : Env M 22) tg_reply0_m) :
    ∃ v t j, KPair_d M v τ w ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 2, ρ.bound 3, ρ.bound 4,
        ρ.bound 5, ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10, ρ.bound 11,
        ρ.bound 19, ρ.bound 20, v].get i, fun _ => ρ.bound 0⟩ : Env M 15) tg_answer0_m ∧
      Fseq_end_d I (ρ.bound 0) t (ρ.bound 20) v ∧ M.mem j (ρ.bound 0) ∧
      M.SuccessorOf j (ρ.bound 45) ∧ Fn0_d j (ρ.bound 12) t ∧ M.mem t (ρ.bound 18) ∧
      M.IsOrdinalDivision I j (ρ.bound 4) (ρ.bound 19) (ρ.bound 3) ∧
      Tg_event_d I (ρ.bound 4) (ρ.bound 19) (ρ.bound 2) t v := by
  have issued := (tg_issued_sat_l I hE ρ).mp valid
  obtain ⟨v, pair⟩ := I.total τ w
  have pair : KPair_d M v τ w := (kpair_sat_l M hE
    (⟨fun i => [v, τ, w].get i, fun _ => v⟩ : Env M 3) (.bound 0) (.bound 1) (.bound 2)).mp
      ((I.satisfies_code_iff ..).mpr pair)
  let p := tg_control_params_d (fun i => ρ.bound (i.castAdd 27))
  have answer := tg_answer_build_l I hE p issued.event issued.move pair issued.labels
    issued.first issued.last issued.elastic below request query issued.program reply
  have control := issued.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have step := control.2.2.2.2.2.2.1
  simp only [tg_answer_control_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, fn0_sat_l hE, Formula.satisfies_isOrdinalDivision_iff I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, fseq_end_sat_l I hE,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hE] at step
  have check := step (ρ.bound 45) issued.time (ρ.bound 19) issued.round
    (ρ.bound 20) issued.position v issued.history issued.clock
  have checked := check (by
    simp only [tg_answer_m, Formula.satisfies_bind]
    apply (Formula.closed_env_l tg_answer0_m tg_answer0_closed_l (ρ := _) (η := _) ?_).mp answer
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun a => Fin.elim0 a))))))))))))))) i)
  obtain ⟨t, j, result⟩ := checked
  exact ⟨v, t, j, pair, answer, result⟩

end YesMetaZFC.SetTheory.LargeCardinal
