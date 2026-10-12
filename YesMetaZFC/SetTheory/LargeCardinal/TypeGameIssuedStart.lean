import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssued

/-! # 原首轮直接产生可搬运的阶段记录 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_issued_start_env_d (ρ : Env M 19) (ε : Env M 38) (a h ℓ j : M.Domain) : Env M 46 :=
  ⟨fun i => Fin.addCases (motive := fun _ => M.Domain) ρ.bound (fun i : Fin 27 => [ρ.bound 1, h, a, ℓ, ε.bound 25, ε.bound 5, ε.bound 18,
    ε.bound 6, ε.bound 7, ε.bound 8, ε.bound 14, ε.bound 15, ε.bound 16,
    ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30, ε.bound 20, ε.bound 22,
    ε.bound 31, ε.bound 32, ε.bound 33, ε.bound 34, ε.bound 35, ε.bound 36, ε.bound 37, j].get i) i, ρ.free⟩

theorem tg_issued_start_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 19) (ε : Env M 38) (a h ℓ j : M.Domain)
    (control : Formula.satisfies ρ tg_control0_m) (time : M.mem j (ρ.bound 0))
    (history : Fn0_d j (ρ.bound 12) h) (position : M.mem h (ρ.bound 18))
    (clock : M.IsOrdinalDivision I j (ρ.bound 4) (ρ.bound 1) (ρ.bound 2))
    (event : Tg_event_d I (ρ.bound 4) (ρ.bound 1) (ρ.bound 1) h a)
    (endt : Fseq_end_d I (ρ.bound 0) h (ρ.bound 1) a)
    (aux : Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 2, ρ.bound 3, ρ.bound 4,
      ρ.bound 5, ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10, ρ.bound 11,
      ρ.bound 1, ρ.bound 1, a].get i, ρ.free⟩ : Env M 15) tg_aux0_m)
    (seed : Formula.satisfies ε tg_seed0_m) (hw : ε.bound 0 = ρ.bound 0) (he : ε.bound 1 = ρ.bound 1)
    (hd : ε.bound 2 = ρ.bound 5)
    (hk : ε.bound 6 = ρ.bound 1) (ht : ε.bound 25 = ρ.bound 1)
    (move : Tg_aux_data_d a ℓ (ε.bound 25) (ε.bound 5) (ε.bound 18))
    (elastic : Tg_ee_data_d (ρ.bound 9) (ε.bound 5) (ε.bound 7) (ε.bound 14) (ε.bound 15) (ε.bound 16)
      ⟨ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30⟩)
    (program : Tg_program_data_d (ρ.bound 10) (ε.bound 7) (ε.bound 20) (ε.bound 22)
      (Fin.cases (ε.bound 31) (Fin.cases (ε.bound 32) (Fin.cases (ε.bound 33)
        (Fin.cases (ε.bound 34) (Fin.cases (ε.bound 35) (Fin.cases (ε.bound 36) (fun _ => ε.bound 37)))))))) :
    Formula.satisfies (tg_issued_start_env_d ρ ε a h ℓ j) tg_issued0_m := by
  apply (tg_issued_sat_l I hE _).mpr
  have head : Formula.satisfies
      (⟨fun i => (tg_issued_start_env_d ρ ε a h ℓ j).bound (i.castAdd 27),
        fun _ => (tg_issued_start_env_d ρ ε a h ℓ j).bound 0⟩ : Env M 19) tg_control0_m := by
    apply (Formula.closed_env_l tg_control0_m tg_control0_closed_l (ρ := ρ) (η := _) ?_).mp control
    funext i
    simp only [tg_issued_start_env_d, Fin.addCases_left]
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff] at seed
  obtain ⟨_, empty, hn, _, _, _, below, first, last, _⟩ := seed
  have empty : ∀ x, ¬ M.mem x (ρ.bound 1) := he ▸ empty
  have labels : Fn0_d (ε.bound 6) (ρ.bound 0) (ε.bound 25) := by
    have zero : Fn0_d (ρ.bound 1) (ρ.bound 0) (ρ.bound 1) :=
      ⟨fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim⟩
    exact hk.symm ▸ ht.symm ▸ zero
  have round : M.mem (ρ.bound 1) (ρ.bound 0) := hw ▸ he ▸ hn
  have bound : M.mem (ε.bound 5) (ρ.bound 5) := hd ▸ below
  refine ⟨head, round, time, history, position, clock, event, move, bound, labels, first, last, elastic, program, ?_⟩
  simp only [tg_issued_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, tg_aux_m, Formula.satisfies_bind]
  refine ⟨ρ.bound 1, endt, ?_⟩
  apply (Formula.closed_env_l tg_aux0_m tg_aux0_closed_l (ρ := _) (η := _) ?_).mp aux
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
