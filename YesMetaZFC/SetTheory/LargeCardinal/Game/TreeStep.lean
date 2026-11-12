import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch

/-! # 原获胜策略的实际反射初值

控制记录与更新核同时进入同一个有限反射层。原参数和原策略仍是记录的
实际坐标；后继层只搬运这份记录及其所属集合，不重新选择策略。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.control_context_l
    {p : Tg_params_d M.Domain} {A F L G J B W O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p A F L G J B W O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F J B W σ) :
    ∃ H r θ X R c K η C,
      M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      Ic_model_d hZF p.ω p.ω K X R ∧ Tg_context_d I p.ω X R η C ∧
      Rt_record_in_d tg_control0_m C r ∧
      let v : Fin 19 → M.Domain := fun i =>
        [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, J, σ, H].get i
      Rt_tuple_d v r ∧ ∃ nc : Nonempty {x // M.mem x C}, ∃ ρ : Env (rt_model_l C nc) 19,
        (∀ i, (ρ.bound i).val = v i) ∧ Formula.satisfies ρ tg_control0_m := by
  obtain ⟨H, r, tuple, _, valid⟩ := game.control_l hZFC woodin root win
  let φ : Formula 1 1 := rt_record_m tg_control0_m .newest
  have hc : φ.FreeClosed := rt_record_closed_l _ _ tg_control0_closed_l rfl
  obtain ⟨θ, X, R, c, K, η, C, regular, rank, model, source, context, hr, reflect⟩ :=
    tg_context_l hZFC game.setup.omega r [⟨1, φ, hc⟩]
  have reflected := (reflect ⟨1, φ, hc⟩ (List.mem_cons_self ..)
    ((⟨Fin.elim0, fun _ => p.ω⟩ : Env M 0).push r) (Fin.cases hr (fun i => Fin.elim0 i))).mp valid
  have record : Rt_record_in_d tg_control0_m C r := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr, ?_⟩
    exact (Formula.closed_env_l _ (lr_rel_closed_l φ hc .newest (fun i => .bound i.succ)
      rfl (fun _ => rfl)) (ρ := ((⟨Fin.elim0, fun _ => p.ω⟩ : Env M 0).push r).push C)
      (η := ⟨Fin.cases C (fun _ => r), fun _ => C⟩)
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp reflected
  let nc : Nonempty {x // M.mem x C} := ⟨⟨p.ω, (context.omega_l source.source.code)⟩⟩
  obtain ⟨_, v, code, valid⟩ := (rt_record_in_read_l hZF.1 tg_control0_m tg_control0_closed_l
    (context.read_l hZF source.source).1.transitive nc).mp record
  have eq := rt_tuple_inj_l code tuple
  exact ⟨H, r, θ, X, R, c, K, η, C, regular, rank, model, source, context, record, tuple,
    nc, ⟨v, fun _ => v 0⟩, congrFun eq, valid⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从 II 原策略直接构造有限递归的迭代根

首个辅助走法、实际重置输入、工作模型、控制记录和锚点同时产生。
原字母表位于首个临界点以下；没有外加的首轮类型或分支选择参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.root_l {p : Tg_params_d M.Domain} {A F L G J B W O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p A F L G J B W O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F J B W σ) :
    ∃ H r θ X R c K η C, M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      Ic_model_d hZF p.ω p.ω K X R ∧ Tg_context_d I p.ω X R η C ∧ Rt_record_in_d tg_control0_m C r ∧
      ∃ nc : Nonempty {x // M.mem x C}, ∃ ρ : Env (rt_model_l C nc) 19,
        Formula.satisfies ρ tg_control0_m ∧
        (∀ i, (ρ.bound i).val = [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, J, σ, H].get i) ∧
        ∃ a h : (rt_model_l C nc).Domain, Rd_entry_d p.e a.val σ ∧ Fn0_d p.a A h.val ∧ M.mem h.val H ∧
        Formula.satisfies (⟨fun i => [ρ.bound 4, ρ.bound 1, ρ.bound 1, h, a].get i, ρ.free⟩ : Env (rt_model_l C nc) 5)
          (tg_event_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ∧
        ∃ ε : Env (rt_model_l C nc) 38, Formula.satisfies ε tg_seed0_m ∧
          (ε.bound 0).val = p.ω ∧ (ε.bound 1).val = p.e ∧ (ε.bound 2).val = p.δ ∧
          (ε.bound 3).val = p.S ∧ (ε.bound 4).val = p.ν ∧ (ε.bound 6).val = p.e ∧
          ε.bound 23 = ε.bound 5 ∧ (ε.bound 24).val = p.e ∧ (ε.bound 25).val = p.e ∧ (ε.bound 26).val = p.e ∧
          (∃ ℓ, Tg_aux_data_d a ℓ (ε.bound 25) (ε.bound 5) (ε.bound 18)) ∧
          Tg_ee_data_d (ρ.bound 9) (ε.bound 5) (ε.bound 7) (ε.bound 14) (ε.bound 15) (ε.bound 16)
            ⟨ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30⟩ ∧
          Tg_program_data_d (ρ.bound 10) (ε.bound 7) (ε.bound 20) (ε.bound 22)
            (Fin.cases (ε.bound 31) (Fin.cases (ε.bound 32) (Fin.cases (ε.bound 33) (Fin.cases (ε.bound 34)
              (Fin.cases (ε.bound 35) (Fin.cases (ε.bound 36) (fun _ => ε.bound 37))))))) ∧
          M.IsLimitOrdinal (ε.bound 5).val ∧ M.mem p.A (ε.bound 14).val ∧
          ∃ α T Q D π, M.SuccessorOf α p.e ∧ It_pnice_d hZF p.ω c α T Q D p.e p.e ∧
            Rd_entry_d p.e c Q ∧ It_map_d D p.e p.e π ∧ Rd_entry_d C C π ∧
            Tg_anchor_d I (ε.bound 5).val (ε.bound 14).val X R π ∧
            ∃ ℓ, Formula.satisfies (tg_issued_start_env_d ρ ε a h ℓ (ρ.bound 2)) tg_issued0_m := by
  obtain ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, _, nc, ρ, eqρ, valid⟩ :=
    game.control_context_l hZFC woodin root win
  have fs := (context.read_l hZF source.source).1
  let Q := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  obtain ⟨a, h, j, _, value, _, _, succ, fn, next, _, event, v, seed, hw, he, hd, hS, hν, hk, hb, hs, ht, hg, move, elastic, program, letters,
    ℓ, issued⟩ :=
    tg_control_start_l Q ext ρ valid
  let ε : Env (rt_model_l C nc) 38 := ⟨v, ρ.free⟩
  have event : Formula.satisfies
      (⟨fun i => [ρ.bound 4, ρ.bound 1, ρ.bound 1, h, a].get i, ρ.free⟩ : Env (rt_model_l C nc) 5)
      (tg_event_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) :=
    (tg_event_sat_l Q ext ..).mpr event
  have hρe : (ρ.bound 1).val = p.e := eqρ 1
  have hρA : (ρ.bound 12).val = A := eqρ 12
  have hρσ : (ρ.bound 17).val = σ := eqρ 17
  have hρH : (ρ.bound 18).val = H := eqρ 18
  have hρB : (ρ.bound 6).val = p.A := eqρ 6
  have value := (rt_entry_l fs.transitive nc hZF.1 (ρ.bound 1) a (ρ.bound 17)).mp value
  have value : Rd_entry_d p.e a.val σ := hρe ▸ hρσ ▸ value
  have sj := (rt_successor_l fs.transitive nc hZF.1 j (ρ.bound 1)).mp succ
  have ej : j.val = p.a := (show M.SuccessorOf j.val p.e from hρe ▸ sj).eq hZF.1 game.setup.one
  have ej' : j = ρ.bound 2 := Subtype.ext (ej.trans (eqρ 2).symm)
  let ι : Env (rt_model_l C nc) 3 := ⟨Fin.cases j (Fin.cases (ρ.bound 12) (fun _ => h)), ρ.free⟩
  have fn := (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
    ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ι).mp
      ((fn0_sat_l ext ι (.bound 0) (.bound 1) (.bound 2)).mpr fn))
  have fn : Fn0_d p.a A h.val := ej ▸ hρA ▸ fn
  have next : M.mem h.val H := hρH ▸ next
  have letters : M.mem p.A (v 14).val := hρB ▸ letters
  have facts := seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at facts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, language, _⟩ := facts
  let pick : Fin 10 → Term 38 := fun i => [.bound 0, .bound 5, .bound 7, .bound 14, .bound 15,
    .bound 16, .bound 27, .bound 28, .bound 29, .bound 30].get i
  let ζ := Definitional.Env.substitute ε pick
  have language : Formula.satisfies ζ ee_language0_m := (Formula.satisfies_bind ε pick ee_language0_m).mp language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at language
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (v 5)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have inner := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ζ (.bound 1) (.bound 3)).mp language.2.2.1
  have hκ := source.source.transitive C context.member (v 5).val (v 5).property
  have hB := source.source.transitive C context.member (v 14).val (v 14).property
  have relative := (context.rank_l (ZF.modelsKP hZF) source.source.transitive source.source.code).of_rank_l source.source.transitive context.member (v 14).property inner
  obtain ⟨o, α, T, Q₀, D, ho, ha, tree⟩ := it_nice_root_l hZF (it_source_mem_l hZF code source.source)
  have eo := hZF.1.eq_of_same_members o p.e (fun z => iff_of_false (ho z) (game.setup.empty z))
  subst o
  have hc := tree.tree.root p.e game.setup.empty
  obtain ⟨π, self, fixed, anchor⟩ := tree.tree.diagram.anchor_root_l hZF hc code source.source.transitive hκ hB relative
  exact ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, nc, ρ, valid, eqρ,
    a, h, value, fn, next, event, ε, seed, (congrArg Subtype.val hw).trans (eqρ 0),
    (congrArg Subtype.val he).trans (eqρ 1), (congrArg Subtype.val hd).trans (eqρ 5),
    (congrArg Subtype.val hS).trans (eqρ 7), (congrArg Subtype.val hν).trans (eqρ 8),
    (congrArg Subtype.val hk).trans (eqρ 1), hb, (congrArg Subtype.val hs).trans (eqρ 1),
    (congrArg Subtype.val ht).trans (eqρ 1), (congrArg Subtype.val hg).trans (eqρ 1),
    move, elastic, program, limit, letters, α, T, Q₀, D, π, ha, tree.toIt_pnice_d, hc, self, fixed C context.member, anchor,
    ℓ, ej' ▸ issued⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 在任何原实数落子之前装配统一递归的零轮

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
  obtain ⟨_, hZ, rankZ, _⟩ := anchor.read_l (ZF.modelsKP hZF) source.source.transitive code
  let ι := tg_issued_start_env_d ρ ε a h ℓ (ρ.bound 2)
  have fs := (context.read_l hZF source.source).1
  let X₀ := smdl_structure_l I (R := R) code.1.2.1
  let C₀ : X₀.Domain := ⟨C, context.member⟩
  let nd : Nonempty {x : X₀.Domain // X₀.mem x C₀} :=
    ⟨⟨⟨p.ω, source.source.omega_mem⟩,
      (code.2 p.ω C).mpr ⟨source.source.omega_mem, context.member, (context.omega_l source.source.code)⟩⟩⟩
  have inside := source.source.transitive C context.member
  let ι₀ := code.native_env_d I C₀ inside nd nc ι
  obtain ⟨r₀, record', values⟩ := rf_record_save_l I code.1.2.1
    (smem_ext_l I code.1 code.2 source.source.transitive hZF.1) tg_issued0_m tg_issued0_closed_l C₀
      (code.slice_transitive_l I C₀ fs.transitive) (code.slice_pair_l I C₀ inside fs.pair) nd ι₀
      ((code.native_formula_l I C₀ inside nd nc tg_issued0_m ι).mp issued)
  let r' := r₀.val
  have zero : (ι.bound 19).val = p.e := eqρ 1
  have high : (ι.bound 24).val = (ε.bound 5).val := rfl
  have memS : M.mem p.S X := hS ▸ source.source.transitive C context.member _ (ε.bound 3).property
  have rootMap := tree.tree.diagram.elementary p.e p.e π c X R c X R self hc hc code.1 code.1
  obtain ⟨S', _, image⟩ := rootMap.1.1.2.2 p.S memS
  have image : Rd_entry_d p.S p.S π := tree.tree.diagram.identity p.e π self p.S S' image ▸ image
  have image : Rd_entry_d p.S (ι.bound 7).val π := (eqρ 7).symm ▸ image
  -- 原所属短扩展器已经断言 ω∈κ；零轮不预先实施一条树边。
  have hwκ : M.mem p.ω (ε.bound 5).val := hw ▸
    tg_successor_omega_l ε ((context.kernel_mem_l source.source.transitive source.source.code (context.read_l hZF source.source).1.transitive nc).renew_l ε seed)
  have omega : M.mem p.ω (ε.bound 14).val := rankZ.ordinal_subset_l hZF source.source.transitive hZ p.ω hwκ
  have he := num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have below := limit.1.empty_mem_of_nonempty (ZF.modelsKP hZF) limit.2.1 game.setup.empty
  let v : Fin 18 → M.Domain := fun i => [X,R,p.ω,K,η,C,α,p.e,T,Q,G,p.e,p.e,p.e,p.e,c,π,r'].get i
  refine ⟨θ,X,R,c,C,(ε.bound 5).val,(ε.bound 14).val,regular,rank,code,limit,omega,letters,memS,
    v,(fun i => (ι.bound i).val),?_,zero,image⟩
  refine ⟨source,context,he,ha,tree,hc,code,self,iC,anchor,record',values,eqρ 0,eqρ 6,
    fun _ h => h,?_,tg_past_links_empty_l I game.setup.empty,tg_past_roots_empty_l I game.setup.empty,
    tg_past_events_empty_l I game.setup.empty,below,?_,?_,⟨p.S,image,tg_root_tree_empty_l game.setup.empty⟩,
    tg_past_play_empty_l I game.setup.empty, It_critical_bound_d.empty_l I game.setup.empty⟩
  · exact zero.symm ▸ tg_past_empty_l hZF game.setup.empty
  · rintro i ν ⟨q,_,hq⟩
    exact (game.setup.empty q hq).elim
  · exact zero.symm ▸ ha.predecessor_mem

end YesMetaZFC.SetTheory.LargeCardinal
