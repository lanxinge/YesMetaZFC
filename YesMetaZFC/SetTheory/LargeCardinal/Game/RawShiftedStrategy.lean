import YesMetaZFC.SetTheory.LargeCardinal.Game.RawBranchProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawTurnStrategy

/-! # 一般原根中的全部良基枝推送策略

同一原响应表先固定本方策略。每份服从对局产生一棵完整原树和根相对
临界点界；量化该树的任意良基枝时，第一坐标是原对局经该枝根腿的
字母推送。实际隶属根的字面读取另行处理，不混入一般原模型的结论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_raw_shifted_d (ω o c X₀ R₀ γ₀ D₀ C₀ Y F S f : M.Domain) : Prop :=
  ∃ T Q G E, It_tree_core_d hZF ω c ω T Q G E ∧
    Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E ∧
    ∀ b, It_wf_branch_d hZF ω ω T Q G b →
      ∃ d N W P j Y' F' S' f', Smem_d I d N W ∧ M.TransitiveSet N ∧ It_source_d hZF ω d ∧
        It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Rd_entry_d o j P ∧ Smap_d I ω c d X₀ N j ∧
        Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
        Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ It_comp_d f j f' ∧ Tg_projection_d hZF ω Y' F' S' f'

/-- 同一原并树同时满足实际临界界与全部良基分支的推送投影。 -/
theorem Tg_raw_iteration_run_d.shifted_l
    {ω c o X₀ R₀ w₀ γ₀ B₀ D₀ C₀ S₀ A₀ A X K r a f H z Y₀ F₀ : M.Domain}
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    (root : Zc_model_d I ω c X₀ R₀)
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (numbers : Rr_layer_d I ω X₀ R₀ w₀ z) (space : Sc_fseq_d I w₀ Y₀ F₀ X₀ R₀)
    (closed : Rr_truth_d I X₀ R₀ (tree_m (.bound 1) .newest) (Fin.cases S₀ (fun _ : Fin 1 => F₀)))
    (input : Fn0_d ω A f)
    (played : ∀ n s q, Rd_entry_d n s H → Rt_coord_d (19 : Fin 66) s q → M.IsRestrictionOf I q f n) :
    Tg_raw_shifted_d hZF ω o c X₀ R₀ γ₀ D₀ C₀ Y₀ F₀ S₀ f :=
  ⟨U 0,U 1,U 2,U 3,u.tree.toIt_tree_core_d,u.critical,
    fun _ wf => h.wf_projection_l hZF u root cut numbers space closed input played wf⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 原辅助胜策自产树根并开始同次运行，给出一般原树的全分支策略。 -/
theorem Tg_game_d.raw_shifted_strategy_l
    {Ω c X R z : M.Domain} (hΩ : M.IsOmega Ω) (certificate : Zc_model_d J Ω c X R)
    {p : Tg_params_d (smdl_structure_l J (R := R) certificate.model.2.1).Domain}
    (numbers : Rr_layer_d J Ω X R p.ω.val z)
    {A F L G D B W O Z g σ Y T : (smdl_structure_l J (R := R) certificate.model.2.1).Domain}
    (game : Tg_game_d (certificate.native_l J hZ hΩ) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l J hZ hΩ)))) p.δ)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l J hZ hΩ)))) false p.ω A F D B W σ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.native_l J hZ hΩ)))) p.ω Y T)
    (closed : Tree_d (M := smdl_structure_l J (R := R) certificate.model.2.1) T p.S) :
    ∃ o γ V Dₛ C A₀ J₀ σ₀, (∀ x, ¬ M.mem x o) ∧
      Tg_root_cut_d J c X R p.ω.val γ V p.A.val Dₛ A₀ ∧ Fseq_space_d J Ω A₀ J₀ ∧
      Gm_strategy_d J false Ω A₀ J₀ σ₀ ∧
      ∀ f, Fn0_d Ω A₀ f → Gm_follows_d J false Ω σ₀ f →
        Tg_raw_shifted_d hZ Ω o c X R γ Dₛ C Y.val T.val p.S.val f := by
  have native := ZFC.models_zf_l (certificate.native_l J hZ hΩ)
  have finite : Sc_fseq_d J p.ω.val Y.val T.val X R :=
    (sc_fseq_native_l J certificate.model.2.1 native.1 p.ω Y T).mpr
      (fun s => (space s).trans ⟨fun ⟨n,hn,fn⟩ => ⟨n,hn,fn0_of_function_l (ZF.modelsKP native) fn⟩,
        fun ⟨n,hn,fn⟩ => ⟨n,hn,fn0_function_l (ZF.modelsKP native) fn⟩⟩)
  let ρ : Env (smdl_structure_l J (R := R) certificate.model.2.1) 2 :=
    ⟨Fin.cases p.S (fun _ => T),fun _ => p.S⟩
  have truth : Rr_truth_d J X R (tree_m (.bound 1) .newest)
      (Fin.cases p.S.val (fun _ : Fin 1 => T.val)) := by
    have moved := (rr_truth_native_l J certificate.model.2.1 (tree_m (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ.bound).mpr ((tree_sat_l ρ (.bound 1) .newest).mpr closed)
    have values : (fun i => (ρ.bound i).val) = Fin.cases p.S.val (fun _ : Fin 1 => T.val) :=
      funext (Fin.cases rfl (fun _ => rfl))
    exact values ▸ moved
  obtain ⟨o,γ,V,Dₛ,C,A₀,F₀,J₀,D₀,t₀,r,Xs,Ds,K,σ₀,empty,cut,_,finites,_,_,_,_,_,strategy,runs⟩ :=
    game.raw_strategy_l hZFC hΩ certificate numbers woodin win
  refine ⟨o,γ,V,Dₛ,C,A₀,J₀,σ₀,empty,cut,finites,strategy,fun f input follows => ?_⟩
  obtain ⟨a,H,U,_,run,tree,played⟩ := runs f input follows
  exact run.shifted_l hZ tree certificate cut numbers finite truth input played

end YesMetaZFC.SetTheory.LargeCardinal
