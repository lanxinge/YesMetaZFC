import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay

/-! # 用原历史位置与原表项装配规则 (7)

所有表项来自实际固定表，回答真值来自实际超幂。装配只使用外延性和
配对解释，所以同一个接口可直接用于有限反射层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include hE

theorem tg_answer_build_l (p : Tg_params_d M.Domain)
    {n h v a ℓ t κ u τ w k l N B U D C V W r m q f j b z : M.Domain}
    {e : Ee_queries_d M} {σ : Fin 7 → M.Domain}
    (event : Tg_event_d I p.c n p.e h a) (move : Tg_aux_data_d a ℓ t κ u) (pair : KPair_d M v τ w)
    (fn : Fn0_d k p.ω t) (next : M.SuccessorOf l k) (last : M.SuccessorOf N l)
    (elastic : Tg_ee_data_d p.E κ l B U D e) (below : M.mem τ p.δ)
    (request : Formula.satisfies (⟨fun i => [p.ω, τ, k, p.e, p.e].get i, fun _ => p.ω⟩ : Env M 5) tg_query_request0_m)
    (query : Tg_query_data_d p.Q τ k p.e p.e C V W r m q f j)
    (program : Tg_program_data_d p.P l b z σ)
    (reply : Formula.satisfies (⟨fun i => [p.ω, l, N, κ, τ, U, D, W, u, w, b, z, r, q, f,
      σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i, fun _ => p.ω⟩ : Env M 22) tg_reply0_m) :
    Formula.satisfies (⟨fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, n, h, v].get i,
      fun _ => p.ω⟩ : Env M 15) tg_answer0_m := by
  simp only [tg_answer0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_event_sat_l I hE, tg_aux_data_sat_l hE, kpair0_sat_l hE, fn0_sat_l hE,
    Formula.satisfies_isSuccessor_iff, tg_ee_data_sat_l hE, Formula.satisfies_mem_iff,
    tg_query_request_m, tg_query_data_sat_l hE, tg_program_data_sat_l hE, tg_reply_m,
    Formula.satisfies_bind, Definitional.Term.eval_weaken]
  refine ⟨a, ℓ, t, κ, u, τ, w, k, l, N, B, U, D, e.largest, e.domain, e.inaccessible, e.stretch,
    C, V, W, r, m, q, f, j, b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6,
    event, move, pair, fn, next, last, elastic, below, ?_, query, program, ?_⟩
  · apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := _) (η := _) ?_).mp request
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))) i
  · apply (Formula.closed_env_l tg_reply0_m tg_reply0_closed_l (ρ := _) (η := _) ?_).mp reply
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a)))))))))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已发出的辅助走法得到回答后的实际历史

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

/-! ## 同一反射层中的回答、实数落子与下一辅助走法

消费原查询表项和完整回答，实际调用原控制记录的三个阶段。
所属结构只需 KP；反射层只用现成的有限闭包，不假定它满足 KP。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)

theorem tg_answer_advance_l {ω C : M.Domain} (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) (θ : Env (rt_model_l C nc) 46)
    (issued : Formula.satisfies θ tg_issued0_m)
    {τ w B U D r m b f q : (rt_model_l C nc).Domain}
    (below : M.mem τ.val (θ.bound 5).val)
    (request : Formula.satisfies (⟨fun i => [θ.bound 0, τ, θ.bound 26, θ.bound 1, θ.bound 1].get i,
      fun _ => θ.bound 0⟩ : Env (rt_model_l C nc) 5) tg_query_request0_m)
    (query : Tg_query_data_d (θ.bound 11) τ (θ.bound 26) (θ.bound 1) (θ.bound 1) B U D r m b f q)
    (reply : Formula.satisfies (⟨fun i => [θ.bound 0, θ.bound 27, θ.bound 28, θ.bound 24, τ,
      θ.bound 30, θ.bound 31, D, θ.bound 25, w, θ.bound 36, θ.bound 37, r, b, f,
      θ.bound 38, θ.bound 39, θ.bound 40, θ.bound 41, θ.bound 42, θ.bound 43, θ.bound 44].get i,
      fun _ => θ.bound 0⟩ : Env (rt_model_l C nc) 22) tg_reply0_m) :
    let J := rt_pair_l fs.transitive nc hKP.1 fs.pair
    ∃ v t q : (rt_model_l C nc).Domain, KPair_d M v.val τ.val w.val ∧
      Formula.satisfies (tg_position_env_d
        ⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ (θ.bound 19) t q) (tg_position0_m 2) ∧
      Formula.satisfies (⟨fun i => [θ.bound 0, t, θ.bound 20, v].get i, fun _ => v⟩ :
        Env (rt_model_l C nc) 4) (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
      Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) t (θ.bound 23) v ∧
      let ψ := tg_position_env_d
        (⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ : Env (rt_model_l C nc) 19) (θ.bound 19) t q
      ∀ x, (rt_model_l C nc).mem x (ψ.bound 6) → ∃ v' t' j' n',
        (rt_model_l C nc).mem v' (ψ.bound 6) ∧
        (Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v' = x) ∧
        (¬ Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
          Rd_entry_d (ψ.bound 20) v' (ψ.bound 17)) ∧
        Formula.satisfies (⟨fun i => [ψ.bound 0, t', ψ.bound 20, v'].get i, fun _ => v'⟩ : Env (rt_model_l C nc) 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
        (rt_model_l C nc).SuccessorOf n' (ψ.bound 19) ∧
        Formula.satisfies (tg_position_env_d ⟨fun i => ψ.bound (i.castAdd 3), fun _ => ψ.bound 0⟩ n' t' j')
          (tg_position0_m 0) ∧
        ∃ ε : Env (rt_model_l C nc) 46, (∀ i : Fin 19, ε.bound (i.castAdd 27) = ψ.bound (i.castAdd 3)) ∧
          ε.bound 19 = n' ∧ Formula.satisfies ε tg_issued0_m ∧ Rd_entry_d t' (ε.bound 21) (ψ.bound 17) ∧
          Formula.satisfies (⟨fun i => [ψ.bound 0, ε.bound 20, t', ε.bound 21].get i, fun _ => ε.bound 21⟩ :
            Env (rt_model_l C nc) 4)
            (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
          (rt_model_l C nc).mem (θ.bound 24) (ε.bound 24) ∧
          M.MemberSubset (θ.bound 20).val (ε.bound 20).val ∧
          (θ.bound 20).val ≠ (ε.bound 20).val ∧
          Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) (ε.bound 20) (θ.bound 23) v := by
  intro J
  have ext := rt_model_ext_l hKP.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext θ).mp issued
  let χ : Env (rt_model_l C nc) 19 := ⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩
  obtain ⟨v, t, q, pair, _, endt, hq, _, fn, position, clock, event⟩ :=
    tg_issued_answer_l J ext θ issued below request query reply
  have pair' := (kpair0_sat_l hKP.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (kpair0_delta_l (.bound 0) (.bound 1) (.bound 2))
      (⟨fun i => [v, τ, w].get i, fun _ => v⟩ : Env (rt_model_l C nc) 3)).mp
      ((kpair0_sat_l ext ..).mpr pair))
  have next := tg_position_build_l J ext 2 χ (θ.bound 19) t q state.control state.round hq fn position clock
  have trace : Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) t (θ.bound 23) v :=
    ⟨⟨θ.bound 21, θ.bound 22, θ.bound 24, θ.bound 25, state.event.end_l endt, state.move⟩, event⟩
  refine ⟨v, t, q, pair', next, (fseq_end_sat_l J ext ..).mpr endt, trace, ?_⟩
  dsimp only
  intro x hx
  obtain ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux⟩ :=
    tg_position_next_l J ext _ next x hx
  have digit' := (fseq_end_sat_l J ext ..).mp digit
  have aux' := (fseq_end_sat_l J ext ..).mp aux
  have keep : (rt_model_l C nc).MemberSubset t (ε.bound 20) :=
    fun s hs => aux'.subset_l J s (digit'.subset_l J s hs)
  have keep' : (rt_model_l C nc).MemberSubset (θ.bound 20) (ε.bound 20) :=
    fun s hs => keep s (endt.subset_l J s hs)
  have same : ∀ i : Fin 19, ε.bound (i.castAdd 27) = θ.bound (i.castAdd 27) := by
    intro i
    exact (head i).trans (by simp only [tg_position_env_d, Fin.addCases_left, χ])
  have succ' : (rt_model_l C nc).SuccessorOf (ε.bound 19) (θ.bound 19) := num.symm ▸ succ
  have proper : (θ.bound 20).val ≠ (ε.bound 20).val := by
    intro eq
    obtain ⟨_, m, d⟩ := endt
    obtain ⟨r, pair, hr⟩ := d.last_value
    have eq : ε.bound 20 = θ.bound 20 := Subtype.ext eq.symm
    exact KP.mem_irrefl_d hKP m.val
      ((d.prefix_sequence.2.2.2 m).mpr ⟨v, r, pair, eq ▸ keep r hr⟩)
  exact ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux,
    tg_issued_growth_l J ext θ ε issued issued' same succ' keep',
    (fun s hs => keep' ⟨s, fs.transitive _ (θ.bound 20).property s hs⟩ hs), proper,
    trace.mono_l J keep⟩

end YesMetaZFC.SetTheory.LargeCardinal
