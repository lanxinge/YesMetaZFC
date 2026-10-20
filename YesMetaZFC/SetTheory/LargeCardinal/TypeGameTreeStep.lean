import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlRoot
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunState

/-! # 在任何原实数落子之前装配统一递归的零轮

根模型、原控制记录、首个辅助请求和空历史同时固定。后续所有轮次均
使用同一 advance_l；零轮不再另写一遍 padding、超幂及回答构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.run_start_l {p : Tg_params_d M.Domain} {A F₀ L₀ G₀ J₀ B₀ W₀ O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p A F₀ L₀ G₀ J₀ B₀ W₀ O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F₀ J₀ B₀ W₀ σ) :
    ∃ θ X R c C γ V, M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      M.IsLimitOrdinal γ ∧ M.mem p.ω V ∧ M.mem p.A V ∧ M.mem p.S X ∧
      ∃ v u, Tg_run_d hZF p.ω c p.e C γ V p.A v u ∧ u 19 = p.e ∧ Rd_entry_d p.S (u 7) (v 16) := by
  obtain ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, nc, ρ, valid, eqρ,
    a, h, _, _, _, _, ε, seed, hw, _, _, hS, _, _, _, _, _, _, _, _, _, limit, letters,
    α, T, Q, G, π, ha, tree, hc, self, iC, anchor, ℓ, issued⟩ := game.root_l hZFC woodin root win
  let ι := tg_issued_start_env_d ρ ε a h ℓ (ρ.bound 2)
  obtain ⟨r', record', values⟩ := rt_record_in_save_l hZF.1 tg_issued0_m tg_issued0_closed_l
    (context.read_l hZF source.source).1.transitive (context.read_l hZF source.source).1.pair nc ι issued
  have values := (rf_tuple_mem_l I hZF.1 source.source.transitive code _).mpr
    ⟨source.source.transitive C context.member r' record'.member_l, values⟩
  have record' := (rf_record_mem_l I source.source.transitive code tg_issued0_m).mpr ⟨context.member, record'⟩
  have zero : (ι.bound 19).val = p.e := eqρ 1
  have high : (ι.bound 24).val = (ε.bound 5).val := rfl
  have memS : M.mem p.S X := hS ▸ source.source.transitive C context.member _ (ε.bound 3).property
  have rootMap := tree.tree.diagram.elementary p.e p.e π c X R c X R self hc hc code.1 code.1
  obtain ⟨S', _, image⟩ := rootMap.1.1.2.2 p.S memS
  have image : Rd_entry_d p.S p.S π := tree.tree.diagram.identity p.e π self p.S S' image ▸ image
  have image : Rd_entry_d p.S (ι.bound 7).val π := (eqρ 7).symm ▸ image
  -- 原所属短扩展器已经断言 ω∈κ；零轮不预先实施一条树边。
  have hwκ : M.mem p.ω (ε.bound 5).val := hw ▸
    tg_successor_omega_l ε ((context.kernel_l (context.read_l hZF source.source).1.transitive nc).renew_l ε seed)
  have omega : M.mem p.ω (ε.bound 14).val := anchor.rank.ordinal_subset_l hZF source.source.transitive anchor.member p.ω hwκ
  have he := num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have below := limit.1.empty_mem_of_nonempty (ZF.modelsKP hZF) limit.2.1 game.setup.empty
  let v : Fin 18 → M.Domain := fun i => [X,R,p.ω,K,η,C,α,p.e,T,Q,G,p.e,p.e,p.e,p.e,c,π,r'].get i
  refine ⟨θ,X,R,c,C,(ε.bound 5).val,(ε.bound 14).val,regular,rank,code,limit,omega,letters,memS,
    v,(fun i => (ι.bound i).val),?_,zero,image⟩
  refine ⟨source,context,he,ha,tree,hc,code,self,iC,anchor,record',values,eqρ 0,eqρ 6,
    fun _ h => h,?_,tg_past_links_empty_l I game.setup.empty,tg_past_roots_empty_l game.setup.empty,
    tg_past_events_empty_l game.setup.empty,below,?_,?_,⟨p.S,image,tg_root_tree_empty_l game.setup.empty⟩,
    tg_past_play_empty_l game.setup.empty, It_critical_bound_d.empty_l game.setup.empty⟩
  · exact zero.symm ▸ tg_past_empty_l hZF game.setup.empty
  · rintro i ν ⟨q,_,hq⟩
    exact (game.setup.empty q hq).elim
  · exact zero.symm ▸ ha.predecessor_mem

end YesMetaZFC.SetTheory.LargeCardinal
