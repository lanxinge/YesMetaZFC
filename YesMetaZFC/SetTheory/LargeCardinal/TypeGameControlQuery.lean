import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlMove

/-! # 在搬运后的原查询表中读取新键

只解包控制记录中已经证明的全域性。返回字面表项和同一组查询证书，
可直接用来检查原规则 (7)；反射层无需满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hE : Extensional M)
include hE

theorem tg_control_query_l (ρ : Env M 19) (ε : Env M 5)
    (valid : Formula.satisfies ρ tg_control0_m) (hw : ε.bound 0 = ρ.bound 0)
    (hk : M.mem (ε.bound 1) (ρ.bound 5)) (request : Formula.satisfies ε tg_query_request0_m) :
    ∃ B U D r m b h q l n,
      Tg_query_data_d (ρ.bound 11) (ε.bound 1) (ε.bound 2) (ε.bound 3) (ε.bound 4) B U D r m b h q ∧
      M.SuccessorOf l (ε.bound 2) ∧ M.SuccessorOf n l ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, l, n, ε.bound 1, B, U, D, r, b, h].get i,
        ρ.free⟩ : Env M 11) tg_reply_language0_m ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, l, n, ε.bound 2, ε.bound 3, ε.bound 4, r, m, b, h, q].get i,
        ρ.free⟩ : Env M 12) tg_query_row0_m := by
  have tables := (Formula.satisfies_conj_iff ..).mp valid |>.1
  have total := (Formula.satisfies_conj_iff ..).mp tables |>.2
  have total := (Formula.satisfies_conj_iff ..).mp total |>.1
  simp only [tg_query_total_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, tg_query_request_m, Formula.satisfies_bind] at total
  have packet := total (ε.bound 1) hk (ε.bound 2) (ε.bound 3) (ε.bound 4) (by
    apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := ε) (η := _) ?_).mp request
    funext i
    exact Fin.cases hw (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i)
  simp only [Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_quad_sat_l hE, rd_entry0_sat_l hE,
    tg_query_packet_m, Formula.satisfies_isSuccessor_iff, kpair0_sat_l hE,
    tg_reply_language_m, tg_query_base_m, Formula.satisfies_bind, Definitional.Term.eval_weaken] at packet
  obtain ⟨x, c, key, entry, l, n, B, U, D, r, m, b, h, q, a, v, hl, hn, row, codes, tail, language, _, _, base⟩ := packet
  refine ⟨B, U, D, r, m, b, h, q, l, n, ⟨x, c, a, v, key, entry, row, codes, tail⟩, hl, hn, ?_, ?_⟩
  · apply (Formula.closed_env_l tg_reply_language0_m tg_reply_language0_closed_l (ρ := _) (η := _) ?_).mp language
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i
  · apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨?_, (Formula.satisfies_conj_iff ..).mpr ⟨hl, hn⟩⟩
    apply (Formula.closed_env_l tg_query_base0_m tg_query_base0_closed_l (ρ := _) (η := _) ?_).mp base
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
