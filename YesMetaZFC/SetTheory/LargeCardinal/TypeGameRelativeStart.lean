import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRelativeRoot
import YesMetaZFC.Model.SetTheory.Internal.RelationRecord
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlMove
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlRead
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceRelative

/-! # 给定地模型中的实际零轮游戏记录

先解码给定模型的完整内部 ZFC 证书，导出全内部源理论，再在同一模型内
产生并反射控制记录。原模型码、树和策略逐项保留，根上使用同一个恒等图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF hX

theorem Tg_game_d.zero_relative_l {p : Tg_params_d (N).Domain} {c R : M.Domain}
    (hω : M.IsOmega p.ω.val) (model : Smem_d I c X R) (certificate : Zc_model_d I p.ω.val c X R)
    {A F L G D B W O Z g σ : (N).Domain}
    (game : Tg_game_d (certificate.membership_l I hZF hω model nx) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.membership_l I hZF hω model nx)))) p.δ) (root : (N).mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.membership_l I hZF hω model nx)))) false p.ω A F D B W σ) :
    Sc_theory_d I p.ω.val X R ∧ Sc_collection_d I p.ω.val X R ∧ Sc_power_d X ∧
    (∃ K, Ep_source_d hZF p.ω.val p.ω.val K X R) ∧
    ∃ H η C r, M.mem H X ∧ Tg_context_d p.ω.val X η C ∧ Fs_read_d p.ω.val C ∧ Sc_small_d X C ∧
      Sc_power_d C ∧
      Rf_record_d I X R tg_issued0_m C r ∧ ∃ u : Fin 46 → M.Domain, Rf_tuple_d I X R u r ∧
        (∀ i, M.mem (u i) C) ∧
        (∀ i : Fin 19, u (i.castAdd 27) =
          [p.ω.val, p.e.val, p.a.val, p.b.val, p.c.val, p.δ.val, p.A.val, p.S.val, p.ν.val,
            p.E.val, p.P.val, p.Q.val, A.val, F.val, L.val, G.val, D.val, σ.val, H].get i) ∧
        u 19 = p.e.val ∧ u 23 = p.e.val ∧ u 26 = p.e.val ∧
        M.IsLimitOrdinal (u 24) ∧ Vr_d X (u 24) (u 29) ∧ M.mem p.ω.val (u 29) ∧ M.mem p.A.val (u 29) ∧
        ∃ π k, Smap_d I p.ω.val c c X X π ∧
          (∀ x, M.mem x X → Rd_entry_d x x π) ∧ Rr_layer_d I C X R C k ∧
          Rr_closed_d I X R C ∧ Rr_small_d I X R C ∧ Rr_rank_d I X R η C := by
  have ground : (N).Models ZFC := certificate.membership_l I hZF hω model nx
  have power := certificate.power_l hZF hω hX model
  refine ⟨certificate.theory_l hZF hω hX model, certificate.collection_l hZF hω hX model,
    power,
    certificate.source_l hZF hω hX model p.ω.property p.ω.property (hω.isOrdinal hZF) (fun _ h => h), ?_⟩
  -- 在原模型内生成控制记录，再反射原记录公式。
  obtain ⟨H, r, tuple, _, valid⟩ := Tg_game_d.control_l (M := N) ground (p := p) game woodin root win
  let φ : Formula 1 1 := rt_record_m tg_control0_m .newest
  have hc : φ.FreeClosed := rt_record_closed_l _ _ tg_control0_closed_l rfl
  obtain ⟨η, C, context, hr, small, fs, reflect⟩ :=
    tg_context_relative_l hZF hX nx ground p.ω r hω [⟨1, φ, hc⟩]
  let ξ : Env N 1 := (⟨Fin.elim0, fun _ => p.ω⟩ : Env N 0).push r
  have truth : Formula.satisfies ξ φ := (Formula.closed_env_l φ hc
    (ρ := ((⟨Fin.elim0, fun _ => p.ω⟩ : Env N 0).push r)) (η := ξ) rfl).mp valid
  have reflection : Lr_reflect_d φ C := reflect ⟨1, φ, hc⟩ (List.mem_cons_self ..)
  have reflected := (reflection ξ (Fin.cases hr (fun i => Fin.elim0 i))).mp truth
  have record : Rt_record_in_d tg_control0_m C r := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr, ?_⟩
    exact (Formula.closed_env_l _ (lr_rel_closed_l φ hc .newest (fun i => .bound i.succ)
      rfl (fun _ => rfl)) (ρ := ξ.push C)
      (η := ⟨Fin.cases C (fun _ => r), fun _ => C⟩)
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp reflected
  -- 相对记录是有界公式；先作绝对化，再显式识别绑定赋值。
  let θ : Env N 2 := ⟨Fin.cases C (fun _ => r), fun _ => C⟩
  have moved := (rt_model_delta_l hX nx (rt_record_in0_delta_l tg_control0_m) θ).mp record
  have record : Rt_record_in_d (M := M) tg_control0_m C.val r.val := by
    change Formula.satisfies (⟨Fin.cases C.val (fun _ => r.val), fun _ => C.val⟩ : Env M 2)
      (rt_record_in0_m tg_control0_m)
    exact (Formula.closed_env_l (rt_record_in0_m tg_control0_m) (rt_record_in0_closed_l _ tg_control0_closed_l)
      (ρ := @image_env_l N M Subtype.val 2 θ)
      (η := (⟨Fin.cases C.val (fun _ => r.val), fun _ => C.val⟩ : Env M 2))
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp moved
  let v : Fin 19 → (N).Domain := fun i =>
    [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, D, σ, H].get i
  have tuple : Rt_tuple_d (fun i => (v i).val) r.val := (rt_tuple_source_l hZF.1 hX nx v r).mp tuple
  let nc : Nonempty {x // M.mem x C.val} := ⟨⟨p.ω.val, context.omega⟩⟩
  obtain ⟨_, a, code, control⟩ := (rt_record_in_read_l hZF.1 tg_control0_m tg_control0_closed_l fs.transitive nc).mp record
  let ρ : Env (rt_model_l C.val nc) 19 := ⟨a, fun _ => a 0⟩
  have eqρ (i) : (ρ.bound i).val = (v i).val := congrFun (rt_tuple_inj_l code tuple) i
  -- 读取同一个首轮请求，有限配对足以把全部坐标重新保存。
  let Kp := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  obtain ⟨a, h, j, _, _, _, _, _, _, _, _, _, w, seed, hw, _, _, _, _, hk, _, _, ht, _,
    _, _, _, letters, ℓ, issued⟩ := tg_control_start_l Kp ext ρ control
  let ε : Env (rt_model_l C.val nc) 38 := ⟨w, ρ.free⟩
  let ι := tg_issued_start_env_d ρ ε a h ℓ j
  obtain ⟨s, saved, values⟩ := rt_record_in_save_l hZF.1 tg_issued0_m tg_issued0_closed_l fs.transitive fs.pair nc ι issued
  have values := (rf_tuple_mem_l I hZF.1 hX model _).mpr ⟨hX C.val context.member s saved.member_l, values⟩
  have saved := (rf_record_mem_l I hX model tg_issued0_m).mpr ⟨context.member, saved⟩
  -- 原语言给出相对 Vκ；原回答的所属扩展器给出 ω∈κ。
  have facts := seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at facts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, language, _⟩ := facts
  let pick : Fin 10 → Term 38 := fun i => [.bound 0, .bound 5, .bound 7, .bound 14, .bound 15,
    .bound 16, .bound 27, .bound 28, .bound 29, .bound 30].get i
  let ζ := Definitional.Env.substitute ε pick
  have language : Formula.satisfies ζ ee_language0_m := (Formula.satisfies_bind ε pick ee_language0_m).mp language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at language
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (w 5)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have inner := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ζ (.bound 1) (.bound 3)).mp language.2.2.1
  have rank := context.rank.of_rank_l hZF hX context.member (w 14).property inner
  have below : M.mem p.ω.val (w 5).val := (congrArg Subtype.val hw).trans (eqρ 0) ▸
    tg_successor_omega_l ε ((context.kernel_l fs.transitive nc).renew_l ε seed)
  refine ⟨H.val, η.val, C.val, s, H.property, context, fs, small,
    power.rank_l hZF hX context.member context.rank context.limit, saved,
    (fun i => (ι.bound i).val), values, (fun i => (ι.bound i).property), ?_, eqρ 1,
    (congrArg Subtype.val ht).trans (eqρ 1), (congrArg Subtype.val hk).trans (eqρ 1),
    limit, rank, rank.ordinal_subset_l hZF hX (hX C.val C.property _ (w 14).property) p.ω.val below,
    eqρ 6 ▸ letters, context.root_relative_l hZF hω hX small model⟩
  intro i
  simp only [ι, tg_issued_start_env_d, Fin.addCases_left]
  rw [eqρ]
  change Subtype.val (([p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, D, σ, H]).get i) = _
  exact (List.getElem_map Subtype.val
    (l := [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, D, σ, H])
    (i := i.val) (h := i.isLt)).symm

end YesMetaZFC.SetTheory.LargeCardinal
