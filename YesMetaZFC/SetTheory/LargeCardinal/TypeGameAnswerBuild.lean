import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswer

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
