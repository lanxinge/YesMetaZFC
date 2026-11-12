import YesMetaZFC.SetTheory.LargeCardinal.Game.Recovery
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Relations.RankImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueCandidate
import YesMetaZFC.SetTheory.LargeCardinal.Game.Restart
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawSavedBase
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.RawReturn

/-! # 目标原关系模型内部构造查询池并取得低层实现

实际目标 ZF 在自身极限秩段内构造完整查询池和名字列。旧轮、候选和 subtype
随后直接交给同一反射核，返回带实际高度与排列的完整实现证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.realize_native_l {w X R η C : M.Domain}
    (context : Tg_context_d I w X R η C) (nx : ∃ x, M.mem x X)
    (ground : (smdl_structure_l I (R := R) nx).Models ZF)
    (omega : (smdl_structure_l I (R := R) nx).IsOmega ⟨w, context.omega_mem⟩)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x ⟨C, context.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc) 54)
    (χ : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc) 12)
    (θ : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc) 17)
    (old : Formula.satisfies ρ tg_round0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (subtype : Formula.satisfies θ tg_subtype0_m)
    (program : Formula.satisfies (θ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m)
    (prior : ∀ i : Fin 5, θ.bound ([0,1,2,5,9].get i) = ρ.bound ([16,24,15,13,11].get i))
    (current : ∀ i : Fin 3, θ.bound ([3,4,6].get i) = χ.bound ([3,1,0].get i))
    (hw : (θ.bound 0).val.val = w)
    (finite : (smdl_structure_l I (R := R) nx).mem (χ.bound 1).val ⟨w, context.omega_mem⟩) :
    ∃ W ν : (smdl_structure_l I (R := R) nx).Domain,
      Tt_pool_d (kp_pair_l (ZF.modelsKP ground)) ⟨w, context.omega_mem⟩ (χ.bound 1).val (χ.bound 6).val W ∧
      (smdl_structure_l I (R := R) nx).mem ν (ρ.bound 10).val ∧
      Tg_realized_in_d (M := smdl_structure_l I (R := R) nx) ⟨w, context.omega_mem⟩ (ρ.bound 18).val (ρ.bound 24).val (ρ.bound 29).val
        (χ.bound 1).val (χ.bound 6).val W (χ.bound 0).val ν ⟨C, context.member⟩ := by
  let N := smdl_structure_l I (R := R) nx
  let J := kp_pair_l (ZF.modelsKP ground)
  let w₀ : N.Domain := ⟨w, context.omega_mem⟩
  let C₀ : N.Domain := ⟨C, context.member⟩
  let η₀ : N.Domain := ⟨η, context.height⟩
  have fs := context.finite_l nx ground.1
  have rank := (rr_rank_native_l I nx (ZF.modelsKP ground) η₀ C₀).mp ((rr_rank_truth_l I).mpr context.rank)
  have limit : N.IsLimitOrdinal η₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => η₀)).mp context.limit)
  obtain ⟨W, pool⟩ := tt_pool_exists_l J ground omega (χ.bound 1).val (χ.bound 6).val
  have hW := pool.rank_mem_l (ZF.modelsKP ground) omega rank limit fs.omega_mem finite (χ.bound 6).property
  obtain ⟨A, E, names, seq, product⟩ := pool
  have hA := names.rank_mem_l (ZF.modelsKP ground) omega rank limit fs.omega_mem finite (χ.bound 6).property
  have hE := ZF.v_fseq_mem_l J ground rank limit omega fs.omega_mem hA seq
  let W₀ : (rt_model_l C₀ nc).Domain := ⟨W, hW⟩
  have hw₀ : (θ.bound 0).val = w₀ := Subtype.ext hw
  let σ : Env (rt_model_l C₀ nc) 4 := ⟨fun i => [θ.bound 0,χ.bound 1,χ.bound 6,W₀].get i, χ.free⟩
  have pool' : Formula.satisfies σ (tt_pool_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)) :=
    (fs.pool_sat_l (ZF.modelsKP ground) nc σ (.bound 0) (.bound 1) (.bound 2) (.bound 3) hw₀).mpr
      ⟨A, E, hA, hE, names, seq, product⟩
  obtain ⟨ν, bound, proof⟩ := tg_realize_assemble_l (context.kernel_l nx nc) ρ χ θ W₀
    old candidate subtype program prior current (show N.mem (χ.bound 1).val (θ.bound 0).val from hw₀.symm ▸ finite) pool'
  have hwρ : (ρ.bound 16).val = w₀ := (congrArg Subtype.val (prior 0)).symm.trans hw₀
  let ξ : Env (rt_model_l C₀ nc) 9 :=
    ⟨fun i => [ρ.bound 16,ρ.bound 18,ρ.bound 24,ρ.bound 29,χ.bound 1,χ.bound 6,W₀,χ.bound 0,ν].get i, ρ.free⟩
  let p : Fin 9 → N.Domain := fun i =>
    [w₀,(ρ.bound 18).val,(ρ.bound 24).val,(ρ.bound 29).val,(χ.bound 1).val,(χ.bound 6).val,W,(χ.bound 0).val,ν.val].get i
  have same : ∀ i, p i = (ξ.bound i).val := Fin.cases hwρ.symm (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))
  have members i : N.mem (p i) C₀ := Eq.mpr (congrArg (fun a => N.mem a C₀) (same i)) (ξ.bound i).property
  exact ⟨W, ν.val, ⟨A, E, names, seq, product⟩, bound, members,
    (sc_relative_sat_l fs.transitive nc ts_at0_m ts_at0_closed_l ξ
      ((⟨p, fun _ => w₀⟩ : Env N 9).push C₀) .newest (fun i => .bound i.succ) rfl same).mpr proof⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 固定第一次原后继中的恢复、重启与再次施加

输入是同一次 First 生产的候选、查询和完整 subtype 坐标。代表池单值性
识别它们的共同参数，再实际执行实现、恢复、重启及保存核。新支撑和
新扩展器随同一五十四项回答返回，并立即用于原共同图逆向施加。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.continue_renewal_l
    {Ω c₀ X₀ R₀ c N R w z η C p d P S w' z' η' C' q
      L l U V Γ g Dp tₛ γ₀ D₀ C₀ γ' Vγ' tγ' S₀ : M.Domain}
    (common : Ic_common_d I N R P S L l U V Γ g)
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c₀ X₀ R₀)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (left : Smap_d I Ω c₀ c X₀ N p) (right : Smap_d I Ω c₀ d X₀ P q)
    (numbers : Rr_layer_d I Ω N R w z) (targetNumbers : Rr_layer_d I Ω P S w' z')
    (context : Tg_context_d I w N R η C) (target : Tg_context_d I w' P S η' C')
    (cofinal : Tg_raw_cofinal_d I w N R L) (small : Rr_small_d I N R U)
    (ft : M.IsSetInjectionFromTo I tₛ Dp P) (restrict : M.IsRestrictionOf I g tₛ Γ)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) mp.2.1).Domain //
      (smdl_structure_l I (R := S) mp.2.1).mem x ⟨C',target.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46)
    (ψ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 12)
    (ρₛ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C',target.member⟩ nd) 54)
    (θₛ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C',target.member⟩ nd) 17)
    (ε ζ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C',target.member⟩ nd) 12)
    (issued : Formula.satisfies ι tg_issued0_m) (oldRound : Formula.satisfies ρₛ tg_round0_m)
    (subtype : Formula.satisfies θₛ tg_subtype0_m)
    (program : Formula.satisfies (θₛ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m)
    (prior : ∀ i : Fin 5, θₛ.bound ([0,1,2,5,9].get i) = ρₛ.bound ([16,24,15,13,11].get i))
    (truth : Formula.satisfies ε tg_candidate0_m) (queryTruth : Formula.satisfies ζ tg_query_row0_m)
    (queryCoords : ∀ i : Fin 6, ψ.bound ([0,1,2,3,4,6].get i) = ι.bound ([0,1,27,28,26,23].get i))
    (images : ∀ i : Fin 12, Rd_entry_d (ι.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i)).val.val
      (ε.bound i).val.val g)
    (queryImages : ∀ i, Rd_entry_d (ψ.bound i).val.val (ζ.bound i).val.val g)
    (ew : (ε.bound 2).val.val = w') (qw : (ζ.bound 0).val.val = w')
    (finiteTarget : Rd_entry_d (ε.bound 1).val.val w' S)
    (qnode : Rd_entry_d (ζ.bound 11).val.val (ε.bound 0).val.val S)
    (qmax : Rd_entry_d (ζ.bound 8).val.val (ε.bound 0).val.val S)
    (scopeTarget : Rd_entry_d (ζ.bound 4).val.val (ε.bound 6).val.val S ∧
      Rd_entry_d (ζ.bound 5).val.val (ε.bound 6).val.val S ∧
      Rd_entry_d (ζ.bound 6).val.val (ε.bound 6).val.val S)
    (emptyQuery : ∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain,
      ¬ (smdl_structure_l I (R := S) mp.2.1).mem x (ζ.bound 1).val)
    (pointsₛ : ∀ i : Fin 5, Rd_entry_d (ι.bound ([0,24,28,25,27].get i)).val.val
      (θₛ.bound ([0,3,4,6,1].get i)).val.val tₛ)
    (program_points : ∀ i : Fin 9, Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (θₛ.bound ([7,8,10,11,12,13,14,15,16].get i)).val.val tₛ)
    (high : Rd_entry_d (ι.bound 24).val.val L R)
    (bound : ∀ x, Rd_entry_d x l S → Rd_entry_d x (ρₛ.bound 15).val.val S)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S C' q γ' Vγ' tγ')
    (omegaSlice : Rd_entry_d w' Vγ' S)
    (lower : ∀ x, Rd_entry_d x γ' S → Rd_entry_d x (ε.bound 3).val.val S)
    (treeName : Rd_entry_d S₀ (ρₛ.bound 19).val.val q) :
    let Pn := smdl_structure_l I (R := S) mp.2.1
    let ground := (root.map_l hZF hΩ mp right).native_l I hZF hΩ
    let hP := ZF.modelsKP (ZFC.models_zf_l ground)
    ∃ W ν : Pn.Domain,
    ∃ εr : Env (rt_model_l (M := Pn) ⟨C',target.member⟩ nd) 29,
      (∀ i : Fin 22, (εr.bound i.succ.succ.succ.succ.succ.succ.succ).val =
        [⟨w',target.omega_mem⟩,(ρₛ.bound 17).val,(ρₛ.bound 22).val,(ρₛ.bound 23).val,(ρₛ.bound 24).val,
          (ζ.bound 3).val,(ε.bound 6).val,W,(ζ.bound 5).val,(ζ.bound 6).val,(ζ.bound 7).val,
          (ζ.bound 8).val,(ζ.bound 9).val,(ζ.bound 10).val,(ζ.bound 11).val,(ρₛ.bound 29).val,
          (ρₛ.bound 18).val,(ρₛ.bound 19).val,(ρₛ.bound 20).val,(ρₛ.bound 42).val,ν,(ε.bound 0).val].get i) ∧
      Formula.satisfies εr tc_recovered0_m ∧ (ζ.bound 4).val = (εr.bound 10).val ∧
    ∃ πp : Env (rt_model_l (M := Pn) ⟨C',target.member⟩ nd) 12,
      (∀ i : Fin 11, πp.bound ([0,1,2,4,5,6,7,8,9,10,11].get i) =
        θₛ.bound ([0,1,7,8,10,11,12,13,14,15,16].get i)) ∧
    ∃ v₂ : (rt_model_l (M := Pn) ⟨C',target.member⟩ nd).Domain,
    ∃ a₂ : Fin 16 → (rt_model_l (M := Pn) ⟨C',target.member⟩ nd).Domain,
      let ρ₂ := tg_round_env_d (tg_restart_env_d ρₛ ε εr πp v₂) a₂
      Formula.satisfies (tg_restart_env_d ρₛ ε εr πp v₂) tg_seed0_m ∧
      Formula.satisfies ρ₂ tg_round0_m ∧ (ρ₂.bound 16).val.val = w' ∧
      Tg_request_d (fun y x => Rd_entry_d x y tₛ) (fun i => (ι.bound i).val.val) (fun i => (ρ₂.bound i).val.val) ∧
      Rd_entry_d (ι.bound 24).val.val (ρ₂.bound 21).val.val g ∧
      Rd_entry_d (ψ.bound 5).val.val (ρ₂.bound 40).val.val g ∧
      (∀ x, Rd_entry_d x γ' S → Rd_entry_d x (ρ₂.bound 21).val.val S) ∧
    ∃ Lr Wr : Pn.Domain, ∃ qr,
      Tg_saved_d I w' P S η' C' Lr.val Wr.val qr ∧
      Tg_saved_code_d P S w' Wr.val qr (fun i => (ρ₂.bound i).val.val) ∧ Rd_entry_d l Lr.val S ∧
      Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ P S w' C' Wr.val qr q ∧
      Tg_raw_cofinal_d I w' P S Lr.val ∧ Tg_saved_name_d I S₀ P S w' Wr.val qr q ∧
    ∃ X K R' F c' d' Y T j κ' A' D' u' : Pn.Domain,
      Tg_image_at_d hP ⟨w',target.omega_mem⟩
        (ρ₂.bound 21).val (ρ₂.bound 18).val (ρ₂.bound 23).val (ρ₂.bound 24).val
        (ρ₂.bound 31).val (ρ₂.bound 32).val (ρ₂.bound 34).val (ρ₂.bound 15).val
        (ρ₂.bound 12).val (ρ₂.bound 11).val (ρ₂.bound 36).val
        (fun i => (ρ₂.bound ([47,48,49,50,51,52,53].get i)).val) (ρ₂.bound 38).val
        ⟨(ρ₂.bound 2).val,(ρ₂.bound 1).val,(ρ₂.bound 0).val⟩ Lr Wr X K R' F c' d' Y T j κ' A' D' u' ∧
    ∃ α β : Pn.Domain, Pn.mem α ⟨l,common.right_rank.1⟩ ∧ Pn.mem β ⟨V,common.right_rank.2.1⟩ ∧
      Pn.mem (ρ₂.bound 21).val β ∧ Pn.IsLimitOrdinal α ∧ V_d (kp_pair_l hP) α β ∧
    ∃ B k, (∀ x, M.mem x B ↔ M.mem x P ∧ Rd_entry_d x V S) ∧
      M.IsSetInjectionFromTo I k B N ∧
      (∀ y, Rd_entry_d y U R ↔ ∃ x, M.mem x B ∧ Rd_entry_d x y k) ∧
      (∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y R ↔ ∃ a, Rd_entry_d a x S ∧ Rd_entry_d a v k) ∧
      (∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x g) ∧
      Er_rank_cut_d hZF Ω c₀ X₀ R₀ c N R p B k P S z' d mp.2.1 hP
        ⟨V,common.right_rank.2.1⟩ ⟨w',target.omega_mem⟩ (ρ₂.bound 21).val Lr F β X K j := by
  intro Pn groundP native
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let Cn : Pn.Domain := ⟨C',target.member⟩
  let Vn : Pn.Domain := ⟨V,common.right_rank.2.1⟩
  let ln : Pn.Domain := ⟨l,common.right_rank.1⟩
  let Un : Nn.Domain := ⟨U,common.left_rank.2.1⟩
  have ground := ZFC.models_zf_l ((root.map_l hZF hΩ mn left).native_l I hZF hΩ)
  have hN := ZF.modelsKP ground
  have targetZF := ZFC.models_zf_l groundP
  have fs := context.finite_l mn.2.1 hN.1
  have fs' := target.finite_l mp.2.1 native.1
  have rankU := (rr_rank_native_l I mn.2.1 hN ⟨L,common.left_rank.1⟩ Un).mp common.left_rank
  have rv := (rr_rank_native_l I mp.2.1 native ln Vn).mp common.right_rank
  have ol := v_ordinal_l (kp_pair_l native) rv
  have omega := targetNumbers.omega_l I (ZF.modelsKP hZF) hΩ native.1
  have fullImages i := ((restrict.2 _ _).mp (images i)).2
  have sameCurrent : ∀ i : Fin 3, θₛ.bound ([3,4,6].get i) = ε.bound ([3,1,0].get i) :=
    Fin.cases (Subtype.ext (Subtype.ext (ft.1.1.2 _ _ _ (pointsₛ 1) (fullImages 3))))
      (Fin.cases (Subtype.ext (Subtype.ext (ft.1.1.2 _ _ _ (pointsₛ 2) (fullImages 1))))
        (Fin.cases (Subtype.ext (Subtype.ext (ft.1.1.2 _ _ _ (pointsₛ 3) (fullImages 0)))) (fun i => Fin.elim0 i)))
  have sw : (θₛ.bound 0).val.val = w' := (ft.1.1.2 _ _ _ (pointsₛ 0) (fullImages 2)).trans ew
  obtain ⟨W,ν,pool,below,realized⟩ := target.realize_native_l hZF mp.2.1 targetZF omega nd ρₛ ε θₛ
    oldRound truth subtype program prior sameCurrent sw finiteTarget
  have h₄ : Rd_entry_d (ι.bound 27).val.val (ζ.bound 2).val.val tₛ :=
    congrArg (fun x => x.val.val) (queryCoords 2) ▸ ((restrict.2 _ _).mp (queryImages 2)).2
  have eqn : (ζ.bound 2).val = (ρₛ.bound 24).val := Subtype.ext
    ((ft.1.1.2 _ _ _ (pointsₛ 4) h₄).symm.trans (congrArg (fun x => x.val.val) (prior 1)))
  have eqm : ζ.bound 3 = ε.bound 1 := Subtype.ext (Subtype.ext
    (common.injection.1.1.2 _ _ _
      (congrArg (fun x => x.val.val) (queryCoords 3) ▸ queryImages 3) (images 1)))
  have candidateDomain := ((Formula.satisfies_conj_iff ..).mp truth).1
  simp only [Formula.satisfies_rename,ee_language0_m,ee_domain_pack_m,
    Formula.satisfies_bind,ee_domain_pack0_m,Formula.satisfies_conj_iff] at candidateDomain
  have hwU : Pn.mem ⟨w',target.omega_mem⟩ (ε.bound 6).val :=
    Eq.mp (congrArg (fun a => Pn.mem a (ε.bound 6).val)
      (show (ε.bound 2).val = ⟨w',target.omega_mem⟩ from Subtype.ext ew)) candidateDomain.1.1
  have oldSeed := ((Formula.satisfies_conj_iff ..).mp oldRound).1
  simp only [tg_seed0_m,Formula.satisfies_rename,tg_seed_m,Formula.satisfies_conj_iff] at oldSeed
  have emptyOld : ∀ x : Pn.Domain, ¬ Pn.mem x (ρₛ.bound 17).val := fun x hx =>
    (Formula.satisfies_isEmpty_iff ..).mp oldSeed.2.1 ⟨x,fs'.transitive _ (ρₛ.bound 17).property x hx⟩ hx
  have eqe : (ζ.bound 1).val = (ρₛ.bound 17).val := native.1.eq_of_same_members _ _
    (fun x => ⟨fun hx => (emptyQuery x hx).elim,fun hx => (emptyOld x hx).elim⟩)
  have witness : Tg_realized_in_d (M := Pn) ⟨w',target.omega_mem⟩
      (ρₛ.bound 18).val (ρₛ.bound 24).val (ρₛ.bound 29).val (ζ.bound 3).val
      (ε.bound 6).val W (ε.bound 0).val ν Cn := by
    rw [eqm]
    exact realized
  obtain ⟨εr,eqr,recovered⟩ := tg_recover_read_l native nd ρₛ ζ omega fs'
    (target.kernel_l mp.2.1 nd) oldRound queryTruth (Subtype.ext qw) eqe eqn hwU scopeTarget qnode qmax witness
  let ιl : Env (rt_model_l (M := Nn) ⟨C,context.member⟩ nc) 3 :=
    ⟨fun i => [ι.bound 26,ι.bound 0,ι.bound 23].get i,ι.free⟩
  have state := (tg_issued_sat_l (rt_pair_l fs.transitive nc hN.1 fs.pair)
    (rt_model_ext_l hN.1 fs.transitive nc) ι).mp issued
  have labels₀ : Fn0_d (M := Nn) (ι.bound 26).val (ι.bound 0).val (ι.bound 23).val :=
    (fn0_sat_l hN.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ιl).mp
        ((fn0_sat_l (rt_model_ext_l hN.1 fs.transitive nc) ιl (.bound 0) (.bound 1) (.bound 2)).mpr state.labels))
  have labels₁ := (rr_native_function_l I mn.2.1 mp.2.1 hN.1 native.1 Un
    (v_transitive_l (kp_pair_l hN) rankU) common.carrier common.injection common.pred
    (ι.bound 26).val (ι.bound 0).val (ι.bound 23).val (ζ.bound 4).val (ζ.bound 0).val (ζ.bound 6).val
    (congrArg (fun x => x.val.val) (queryCoords 4) ▸ queryImages 4)
    (congrArg (fun x => x.val.val) (queryCoords 0) ▸ queryImages 0)
    (congrArg (fun x => x.val.val) (queryCoords 5) ▸ queryImages 6) labels₀).1
  have labelsR : Fn0_d (M := Pn) (ζ.bound 4).val (εr.bound 7).val (εr.bound 16).val := by
    have ew : (εr.bound 7).val = (ζ.bound 0).val := (eqr 0).trans (Subtype.ext qw).symm
    have et : (εr.bound 16).val = (ζ.bound 6).val := eqr 9
    rw [ew,et]
    exact labels₁
  obtain ⟨label_domain,labels⟩ := tg_restart_labels_l native fs'.transitive nd εr recovered labelsR
  have oldω : (ρₛ.bound 16).val = (⟨w',target.omega_mem⟩ : Pn.Domain) :=
    Subtype.ext ((congrArg (fun x => x.val.val) (prior 0)).symm.trans sw)
  have sameL : ζ.bound 2 = ε.bound 4 := Subtype.ext (Subtype.ext
    (common.injection.1.1.2 _ _ _
      (congrArg (fun x => x.val.val) (queryCoords 2) ▸ queryImages 2) (images 4)))
  have sameRecovery : ∀ i : Fin 10, εr.bound ([7,8,10,11,12,13,23,24,25,28].get i) =
      [ρₛ.bound 16,ρₛ.bound 17,ρₛ.bound 23,ρₛ.bound 24,ε.bound 1,ε.bound 6,
        ρₛ.bound 18,ρₛ.bound 19,ρₛ.bound 20,ε.bound 0].get i := by
    intro i
    apply Subtype.ext
    exact Fin.cases ((eqr 0).trans oldω.symm) (Fin.cases (eqr 1) (Fin.cases (eqr 3)
      (Fin.cases (eqr 4) (Fin.cases ((eqr 5).trans (congrArg Subtype.val eqm)) (Fin.cases (eqr 6)
        (Fin.cases (eqr 16) (Fin.cases (eqr 17) (Fin.cases (eqr 18)
          (Fin.cases (eqr 21) (fun j => Fin.elim0 j)))))))))) i
  have hτ := (rt_limit_l fs'.transitive nd native (ε.bound 3)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp candidateDomain.2.1)
  have hτV : Pn.mem (ε.bound 3).val Vn := (common.image _).mpr
    ⟨_,common.injection.1.input_mem_of_pairMember (images 3),images 3⟩
  have belowNext : Pn.mem (ε.bound 3).val (ρₛ.bound 15).val :=
    bound _ (KP.v_ordinal_height_l native rv hτ.1 hτV)
  obtain ⟨πp,eqp,v₂,seed₂,a₂,round₂⟩ := tg_restart_read_l (target.kernel_l mp.2.1 nd) ρₛ ε εr
    (θₛ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i))
    oldRound truth recovered program labels sameRecovery
    (Subtype.ext ((Subtype.ext ew).trans oldω.symm))
    (Subtype.ext ((congrArg Subtype.val sameL).symm.trans eqn)) (prior 0) (prior 1) belowNext
  let ρ₂ := tg_round_env_d (tg_restart_env_d ρₛ ε εr πp v₂) a₂
  have qpts i := ((restrict.2 _ _).mp (queryImages i)).2
  have pw : Rd_entry_d (ι.bound 0).val.val (ρₛ.bound 16).val.val tₛ :=
    (congrArg Subtype.val (show (ε.bound 2).val = (ρₛ.bound 16).val from
      (Subtype.ext ew).trans oldω.symm)) ▸ fullImages 2
  have pe : Rd_entry_d (ι.bound 1).val.val (ρₛ.bound 17).val.val tₛ :=
    congrArg Subtype.val eqe ▸ (congrArg (fun x => x.val.val) (queryCoords 1) ▸ qpts 1)
  have pk : Rd_entry_d (ι.bound 26).val.val (ρₛ.bound 23).val.val tₛ :=
    congrArg Subtype.val (label_domain.trans (eqr 3)) ▸
      (congrArg (fun x => x.val.val) (queryCoords 4) ▸ qpts 4)
  have pl : Rd_entry_d (ι.bound 27).val.val (ρₛ.bound 24).val.val tₛ :=
    congrArg Subtype.val eqn ▸ (congrArg (fun x => x.val.val) (queryCoords 2) ▸ qpts 2)
  have pc (i : Fin 9) : Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (πp.bound ([2,4,5,6,7,8,9,10,11].get i)).val.val tₛ :=
    (congrArg (fun x => x.val.val) (eqp i.succ.succ)).symm ▸ program_points i
  have pt : Rd_entry_d (ι.bound 23).val.val (εr.bound 16).val.val tₛ :=
    (congrArg Subtype.val (eqr 9)).symm ▸ (congrArg (fun x => x.val.val) (queryCoords 5) ▸ qpts 6)
  have request : Tg_request_d (fun y x => Rd_entry_d x y tₛ) (fun i => (ι.bound i).val.val)
      (fun i => (ρ₂.bound i).val.val) := by
    intro i
    exact Fin.cases pw (Fin.cases pe (Fin.cases pk (Fin.cases pl (Fin.cases (fullImages 1)
      (Fin.cases (pc 0) (Fin.cases (pc 1) (Fin.cases (pc 2) (Fin.cases (pc 3) (Fin.cases (pc 4)
        (Fin.cases (pc 5) (Fin.cases (pc 6) (Fin.cases (pc 7) (Fin.cases (pc 8)
          (Fin.cases (fullImages 3) (Fin.cases (fullImages 6) (Fin.cases (fullImages 7)
            (Fin.cases (fullImages 0) (Fin.cases pt (fun j => Fin.elim0 j))))))))))))))))))) i
  have newω : (ρ₂.bound 16).val.val = w' := congrArg Subtype.val oldω
  have point : Rd_entry_d (ι.bound 24).val.val (ρ₂.bound 21).val.val g := images 3
  have short : Rd_entry_d (ψ.bound 5).val.val (ρ₂.bound 40).val.val g :=
    (congrArg Subtype.val (eqr 8)).symm ▸ queryImages 5
  obtain ⟨Lr,Wr,qr,saved,code,high₂,X,K,R',F,c',d',Y,T,j,κ',A',D',u',image⟩ :=
    target.save_round_native_l hZF mp.2.1 groundP omega nd ρ₂ round₂ newω
  have rW := (rr_rank_native_l I mp.2.1 native Lr Wr).mp ((rr_rank_truth_l I).mpr saved.rank)
  have above : Rd_entry_d l Lr.val S := ordinal_down_l native ol
    (v_ordinal_l (kp_pair_l native) rW) (fun x hx => bound x.val hx) high₂
  let ηn : Pn.Domain := ⟨η',target.height⟩
  have rankC := (rr_rank_native_l I mp.2.1 native ηn Cn).mp ((rr_rank_truth_l I).mpr target.rank)
  have limitC : Pn.IsLimitOrdinal ηn := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ηn)).mp target.limit)
  have height := (tg_round_control_l native rankC limitC fs' nd ρ₂ round₂).2.isLimitOrdinal
  have language := ((Formula.satisfies_conj_iff ..).mp round₂).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff] at language
  have higher : Pn.mem (ρ₂.bound 39).val (ρ₂.bound 15).val := language.1
  have language := language.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have limitτ := (rt_limit_l fs'.transitive nd native (ρ₂.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have lowerτ : ∀ x, Rd_entry_d x γ' S → Rd_entry_d x (ρ₂.bound 15).val.val S := by
    intro x hx
    have hxN := (mp.2.2.2 x γ' hx).1
    exact limitτ.1.transitive (ρ₂.bound 39).val higher ⟨x,hxN⟩
      ((limitτ.1.mem higher).transitive (ε.bound 3).val belowNext ⟨x,hxN⟩ (lower x hx))
  have base := Tg_raw_saved_base_d.of_code_l I hZF.1 slice omegaSlice code lowerτ
  have name := Tg_saved_name_d.of_code_l I hZF.1 code (show Rd_entry_d S₀ (ρ₂.bound 19).val.val q from treeName)
  have sourceOmega := numbers.omega_l I (ZF.modelsKP hZF) hΩ hN.1
  have sourceCofinal := cofinal.native_l I hZF.1 mn.2.1 (kp_pair_l hN) hN.1
    ⟨w,context.omega_mem⟩ ⟨L,common.left_rank.1⟩
  have imageData := image
  obtain ⟨rankX,source,_,_,_,_,_,loc,card,strong,mx,my,ultra,critical,bound,_⟩ := imageData
  have newCofinal := it_support_cofinal_l I hZF.1 mp.2.1 native card rankX height
  obtain ⟨α,β,hα,hβ,hκ,limitα,rankβ,B,k,carrier,function,back,pred,inverse,result⟩ :=
    common.return_cut_l hZFC hΩ root mn mp left groundP ⟨w,context.omega_mem⟩ (ι.bound 24).val
      sourceOmega sourceCofinal small high source rankX height loc card strong mx my ultra critical.image bound
      targetNumbers point above
  exact ⟨W,ν,εr,eqr,recovered,label_domain,πp,eqp,v₂,a₂,seed₂,round₂,newω,request,point,short,lower,
    Lr,Wr,qr,saved,code,above,base,newCofinal,name,X,K,R',F,c',d',Y,T,j,κ',A',D',u',image,
    α,β,hα,hβ,hκ,limitα,rankβ,B,k,carrier,function,back,pred,inverse,result⟩

end YesMetaZFC.SetTheory.LargeCardinal
