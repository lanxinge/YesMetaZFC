import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePosition
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssued

/-! # 任意轮的原策略实际给出下一份辅助记录

在阶段零读取同一个策略值，按原规则解包辅助走法，再从原程序表取得对应
内部元数的全部代码。空根与非空继续均由原合法历史检查，不把零轮专用的
重置输入推广成附加前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include I hE

theorem tg_position_issue_l (ρ : Env M 22) (valid : Formula.satisfies ρ (tg_position0_m 0)) :
    ∃ θ : Env M 46, (∀ i : Fin 19, θ.bound (i.castAdd 27) = ρ.bound (i.castAdd 3)) ∧
      θ.bound 19 = ρ.bound 19 ∧ Formula.satisfies θ tg_issued0_m ∧
      Rd_entry_d (ρ.bound 20) (θ.bound 21) (ρ.bound 17) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, θ.bound 20, ρ.bound 20, θ.bound 21].get i,
        fun _ => θ.bound 21⟩ : Env M 4)
        (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
  have state := (tg_position_sat_l I hE 0 ρ).mp valid
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have next := control.2.2.2.1
  simp only [tg_aux_control_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, Formula.satisfies_isOrdinalDivision_iff I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, fseq_end_sat_l I hE, Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hE] at next
  obtain ⟨a, h, j, _, value, endt, hj, _, fn, position, clock, aux, event⟩ :=
    next (ρ.bound 21) state.time (ρ.bound 19) state.round (ρ.bound 20) state.position state.history state.clock
  have original := aux
  simp only [tg_aux_m, Formula.satisfies_bind, tg_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_aux_data_sat_l hE, Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isSuccessor_iff,
    tg_ee_data_sat_l hE, Definitional.Term.eval_weaken] at aux
  obtain ⟨ℓ, t, κ, u, k, l, N, _, _, _, _, _, _, _, _, _, _, B, U, D, g₀, g₁, g₂, g₃,
    move, bound, labels, first, last, _, _, request, _, _, elastic, _⟩ := aux
  simp only [tg_query_request_m, Formula.satisfies_bind, tg_query_request0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at request
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have omega : M.IsOmega (ρ.bound 0) := (Formula.satisfies_isOmega_iff ..).mp rules.1
  obtain ⟨l', succ, hl'⟩ := omega.1.2 k request.2.1
  have eq : l = l' := first.eq hE succ
  have hl : M.mem l (ρ.bound 0) := eq.symm ▸ hl'
  have tables := control.1
  simp only [tg_tables_m, Formula.satisfies_conj_iff] at tables
  have program := tables.1.2.2.1
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    tg_program_data_sat_l hE] at program
  obtain ⟨b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆, program⟩ := program l hl
  let θ : Env M 46 := ⟨fun i => Fin.addCases (motive := fun _ => M.Domain)
    (fun i : Fin 19 => ρ.bound (i.castAdd 3))
    (fun i : Fin 27 => [ρ.bound 19, h, a, ℓ, t, κ, u, k, l, N, B, U, D,
      g₀, g₁, g₂, g₃, b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆, j].get i) i, ρ.free⟩
  have head : Formula.satisfies
      (⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ : Env M 19) tg_control0_m := by
    apply (Formula.closed_env_l tg_control0_m tg_control0_closed_l (ρ := _) (η := _) ?_).mp state.control
    funext i
    simp only [θ, Fin.addCases_left]
  refine ⟨θ, (fun i => by simp only [θ, Fin.addCases_left]), rfl, ?_, value, (fseq_end_sat_l I hE ..).mpr endt⟩
  apply (tg_issued_sat_l I hE θ).mpr
  refine ⟨head, state.round, hj, fn, position, clock, event, move, bound, labels, first, last, elastic, program, ?_⟩
  simp only [tg_issued_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, tg_aux_m, Formula.satisfies_bind]
  refine ⟨ρ.bound 20, endt, ?_⟩
  simp only [tg_aux_m, Formula.satisfies_bind] at original
  apply (Formula.closed_env_l tg_aux0_m tg_aux0_closed_l (ρ := _) (η := _) ?_).mp original
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
