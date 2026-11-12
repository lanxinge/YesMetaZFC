import YesMetaZFC.SetTheory.LargeCardinal.Demand.ResetControl
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.SeparatedGame

/-! # 重置请求的局部回答与历史对应

先由原辅助走法和重置规则得到 43 项 seed，再调用已经证明的 renewal 句子
取出 19 项新见证。坐标使用 `rt_push_d` 的实际量词栈，因此不会另造新的
枚举或不可计算选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC

theorem Td_setup_d.reset_round_l
    {p : Tg_params_d M.Domain} {X n h a ℓ κ u U₁ U₂ z χ : M.Domain}
    (setup : Td_setup_d hZFC p X)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP hZF)) p.δ)
    (aux : Td_aux_d hZF p n h a) (data : Td_move_d a ℓ p.e κ u)
    (tree : Td_tree_d (kp_pair_l (ZF.modelsKP hZF)) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂) (chosen : M.mem z U₁)
    (hχ : M.mem χ p.δ) (separated : Td_separated_d p.S) :
    ∃ η : Env M 62,
      Formula.satisfies η td_round0_m ∧
      Td_reset_seed_d p a ℓ κ u U₁ U₂ z χ (fun i => η.bound (Fin.natAdd 19 i)) ∧
      η.free = (fun _ => p.ω) := by
  obtain ⟨seed,seed_truth,linked⟩ :=
    setup.reset_input_l hZFC woodin aux data tree alphabet chosen hχ separated
  let ρ : Env M 43 := ⟨seed,fun _ => p.ω⟩
  have renewal := td_renewal_true_l hZFC (fun _ => p.ω)
  have valid := (Formula.satisfies_forallClosure_iff (fun _ => p.ω) _).mp renewal seed
  have result := (Formula.satisfies_imp_iff ..).mp valid seed_truth
  obtain ⟨witness,witness_truth⟩ :=
    (rt_exists_sat_l (n := 19) ρ td_witness0_m).mp result
  let η := rt_push_d ρ 19 witness
  refine ⟨η,?_,?_,?_⟩
  · apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨?_,witness_truth⟩
    apply (Formula.satisfies_rename ..).mpr
    exact (Formula.closed_env_l td_seed0_m td_seed0_closed_l
      (ρ := ρ) (η := η.reindex (fun i => Fin.natAdd 19 i))
      (funext fun i => (rt_push_old_l ρ witness i).symm)).mp seed_truth
  · have old : (fun i => η.bound (Fin.natAdd 19 i)) = seed :=
      funext (rt_push_old_l ρ witness)
    exact old.symm ▸ linked
  · simpa [ρ] using rt_push_free_l ρ witness

/-- 从同一 II 胜策的首个实际请求产生回答见证，保留控制历史与固定表项。
这只是施加扩展器之前的首轮输入；双后继及后续历史仍须实际构造。 -/
theorem Td_game_d.reset_round_l
    {p : Tg_params_d M.Domain} {X F L G J B W O Z g σ U₁ U₂ z χ : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP hZF)) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP hZF)) false p.ω X F J B W σ)
    (tree : Td_tree_d (kp_pair_l (ZF.modelsKP hZF)) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂) (chosen : M.mem z U₁) (hχ : M.mem χ p.δ)
    (separated : Td_separated_d p.S) :
    ∃ R a h j ℓ κ u, ∃ η : Env M 62,
      Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false p.ω p.e X F L G J σ R ∧
      M.mem a X ∧ Rd_entry_d p.e a σ ∧
      Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) p.ω h p.e a ∧
      M.mem j p.ω ∧ M.SuccessorOf j p.e ∧ Fn0_d j X h ∧ M.mem h R ∧
      M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) j p.c p.e p.a ∧
      Td_aux_d hZF p p.e p.e a ∧
      Tg_event_d (kp_pair_l (ZF.modelsKP hZF)) p.c p.e p.e h a ∧
      Formula.satisfies η td_round0_m ∧
      Td_reset_seed_d p a ℓ κ u U₁ U₂ z χ (fun i => η.bound (Fin.natAdd 19 i)) ∧
      η.free = (fun _ => p.ω) := by
  obtain ⟨R, control⟩ := game.control_l hZFC win
  obtain ⟨a,h,j,ha,value,append,hj,succ,fn,hh,clock,aux,event,ℓ,κ,u,data⟩ :=
    (game.rules_l hZFC).start_l hZF control
  obtain ⟨η,round,linked,free⟩ :=
    game.setup.reset_round_l hZFC woodin aux data tree alphabet chosen hχ separated
  exact ⟨R,a,h,j,ℓ,κ,u,η,control,ha,value,append,hj,succ,fn,hh,clock,aux,event,
    round,linked,free⟩

end YesMetaZFC.SetTheory.LargeCardinal
