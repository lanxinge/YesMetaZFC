import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyNice
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Game.PreparedResult
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeRecord
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedView
import YesMetaZFC.SetTheory.LargeCardinal.Game.ContinueNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank

/-! # 实际旧活动行的共同层及当前反射层所属

从同一复制历史读取两行与共同层，原秩唯一性识别保存时的层值。
已实施边提供真实不可达支撑，历史最大界再把目标共同层放入当前反射层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_saved_d.common_l
    {ω T Q G E Λ m H ST QT GT i n X R A π z Z α N S B σ u Y β c d
      c₀ X₀ R₀ p q w η C L U r w' η' C' zx χ : M.Domain}
    (saved : Tg_saved_d I w X R η C L U r) (root : Zc_model_d I ω c₀ X₀ R₀)
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (tree : It_tree_d hZF ω c₀ m T Q G E)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (ai : Ic_at_d H i X A π z Z α) (an : Ic_at_d H n N B σ u Y β)
    (qi : Rd_entry_d i c Q) (qn : Rd_entry_d n d Q)
    (mx : Smdl_d I c X R) (mn : Smdl_d I d N S)
    (left : Smap_d I ω c₀ c X₀ X p) (right : Smap_d I ω c₀ d X₀ N q)
    (current : Tg_context_d I w' N S η' C') (nx : Rr_layer_d I ω X R w zx)
    (hi : M.mem i n) (active : Rd_entry_d i L Λ) (lf : M.IsSetFunction I Λ)
    (bound : Ic_bound_d I H Q N S σ n χ) (member : Rd_entry_d χ C' S) :
    ∃ a RA K b RB K' l φ V Γ t,
      Smem_d I a A RA ∧ Ep_source_d I ω ω K A RA ∧ Smap_d I ω c a X A π ∧
      Smem_d I b B RB ∧ Ep_source_d I ω ω K' B RB ∧ Smap_d I ω d b N B σ ∧
      ∃ _same : Ic_agree_d I X R A π N S B σ L l φ U V Γ t,
        Rr_truth_d I X R (sc_inaccessible_m (.bound 1) .newest) (Fin.cases L (fun _ : Fin 1 => w)) ∧
        Rr_truth_d I N S (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => l) ∧ Rd_entry_d V C' S := by
  have qf := tree.diagram.model_function
  obtain ⟨c',qc',_,row⟩ := hist.row_l hZF ai
  have eq := qf.2 i c' c qc' qi
  subst c'
  have sourceRow := row
  obtain ⟨R',RA,_,a,K,_,mx',ma,_,sa,_,_,_,_,copy⟩ := row
  have eq := (smdl_unique_l I mx' mx).2
  subst R'
  obtain ⟨d',qd',_,own⟩ := hist.row_l hZF an
  have eq := qf.2 n d' d qd' qn
  subst d'
  obtain ⟨S',RB,_,b,K',_,mn',mb,_,sb,_,_,_,_,next⟩ := own
  have eq := (smdl_unique_l I mn' mn).2
  subst S'
  obtain ⟨l,φ,U₁,V,Γ,t,c',d',R',S',qi',qn',mx',mn',same⟩ :=
    (hist.past i n X A π z Z α N B σ u Y β ai an hi).active_l (lf.2 i) active
  have eq := qf.2 i c' c qi' qi
  subst c'
  have eq := qf.2 n d' d qn' qn
  subst d'
  have eq := (smdl_unique_l I mx' mx).2
  subst R'
  have eq := (smdl_unique_l I mn' mn).2
  subst S'
  have hx := ZFC.models_zf_l ((root.map_l hZF tree.omega mx left).native_l I hZF tree.omega)
  have hn := ZFC.models_zf_l ((root.map_l hZF tree.omega mn right).native_l I hZF tree.omega)
  have hnM := (hist.domain n).mpr (an.imp fun _ h => h.1)
  have on := hist.diagram.order.ordinal.mem hnM
  obtain ⟨j,succ⟩ := KP.exists_successor (ZF.modelsKP hZF) i
  have hjM := ordinal_down_l (ZF.modelsKP hZF)
    (KP.successor_isOrdinal (ZF.modelsKP hZF) (on.mem hi) succ) hist.diagram.order.ordinal
    (fun x hx => ((succ x).mp hx).elim (on.transitive i hi x)
      (fun eq => (hZF.1.eq_of_same_members x i eq).symm ▸ hi)) hnM
  obtain ⟨pE,κE,FE,hpE,pay⟩ := (levels i L).mp active
  obtain ⟨κq,Lq,Fq,_,supportImage,_,quality⟩ :=
    hist.quality_l hZF ai hpE pay hjM succ (tree.steps i j hjM succ)
  obtain ⟨_,_,_,_,_,_,card⟩ := quality
  have support := sourceRow.inaccessible_l hZF mx nx saved.ext supportImage card
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Ln : Xn.Domain := ⟨L,same.common.left_rank.1⟩
  let Un : Xn.Domain := ⟨U,saved.rank.elim fun m _ => m 0⟩
  let U₁n : Xn.Domain := ⟨U₁,same.common.left_rank.2.1⟩
  have ru := (rr_rank_native_l I mx.2.1 (ZF.modelsKP hx) Ln Un).mp ((rr_rank_truth_l I).mpr saved.rank)
  have ru₁ := (rr_rank_native_l I mx.2.1 (ZF.modelsKP hx) Ln U₁n).mp same.common.left_rank
  have eq : U₁ = U := congrArg Subtype.val (ZF.v_unique_l (kp_pair_l (ZF.modelsKP hx)) hx ru₁ ru)
  subst U₁
  have ol := same.right_ord_l hZF tree.omega mn mb next
  have height : Ic_height_d I H Q N S σ n i l :=
    ⟨ol,X,A,π,z,Z,α,B,u,Y,β,c,d,R,L,φ,U,V,Γ,t,ai,an,qi,qn,mx,mn,same⟩
  let Nn := smdl_structure_l I (R := S) mn.2.1
  let ln : Nn.Domain := ⟨l,same.common.right_rank.1⟩
  have limit : Nn.IsLimitOrdinal ln := (KP.limit0_sat_l (ZF.modelsKP hn) _ .newest).mp
    ((rr_truth_native_l I mn.2.1 (KP.limit0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ln)).mp (same.right_limit_l hZF tree.omega mn mb next))
  have limit' : Rr_truth_d I N S (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => l) :=
    (rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ln)).mpr ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limit)
  let vn : Nn.Domain := ⟨V,same.common.right_rank.2.1⟩
  let cn : Nn.Domain := ⟨C',current.member⟩
  let ηn : Nn.Domain := ⟨η',current.height⟩
  let χn : Nn.Domain := ⟨χ,bound.ordinal.1 0⟩
  have rv := (rr_rank_native_l I mn.2.1 (ZF.modelsKP hn) ln vn).mp same.common.right_rank
  have rc := (rr_rank_native_l I mn.2.1 (ZF.modelsKP hn) ηn cn).mp ((rr_rank_truth_l I).mpr current.rank)
  have oc : Nn.IsOrdinal χn := (KP.ord0_sat_l (ZF.modelsKP hn) _ .newest).mp
    ((rr_truth_native_l I mn.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => χn)).mp bound.ordinal)
  have lt := ZF.v_ordinal_height_l hn rc oc member
  have hlt : Nn.mem ln ηn := by
    rcases bound.upper i l hi height with lower | eq
    · exact (v_ordinal_l (kp_pair_l (ZF.modelsKP hn)) rc).transitive χn lt ln lower
    · exact (show ln = χn from Subtype.ext eq).symm ▸ lt
  exact ⟨a,RA,K,b,RB,K',l,φ,V,Γ,t,ma,sa,copy,mb,sb,next,same,support,limit',
    ZF.v_mem_l (kp_pair_l (ZF.modelsKP hn)) hn rv rc hlt⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次原继续结果完成两步复制

原工厂、完整代表池、恢复记录和程序来自给定 raw 的同一组见证。
本段独立核验坐标复合及完整复制历史，准备阶段不再展开这段证明。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_continue_raw_d.saved_copy_l
    {ω T Q G E Λ m H ST QT GT i n X R A π z Z α N S B σ u Y β c d
      c₀ X₀ R₀ w₀ z₀ p q C₀ S₀ w η C L U r w' η' C' zn χ γ₀ Bγ o
      l φ V Γ t D k agN VgN sgN tgN : M.Domain}
    (mx : Smdl_d I c X R) (mn : Smdl_d I d N S)
    (hN : (smdl_structure_l I (R := S) mn.2.1).Models KP)
    (current : Tg_context_d I w' N S η' C')
    (nd : Nonempty {x : (smdl_structure_l I (R := S) mn.2.1).Domain //
      (smdl_structure_l I (R := S) mn.2.1).mem x ⟨C',current.member⟩})
    (ν : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ nd) 29)
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ nd) 46)
    (v : Fin 54 → M.Domain)
    (same : Ic_agree_d I X R A π N S B σ L l φ U V Γ t)
    (βc : (smdl_structure_l I (R := S) mn.2.1).Domain)
    (raw : Tg_continue_raw_d hZF ω c₀ X₀ R₀ c X R p D k N S zn d mn.2.1 hN
      ⟨V,same.common.right_rank.2.1⟩ ⟨w',current.omega_mem⟩ βc (fun j => (ν.bound j).val) w η C L U r v)
    (saved : Tg_saved_d I w X R η C L U r) (code : Tg_saved_code_d X R w U r v) (hw : v 16 = w)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (hnω : M.mem n ω) (hm : M.SuccessorOf m n)
    (qi : Rd_entry_d i c Q) (qn : Rd_entry_d n d Q) (origin : It_map_d G o i p)
    (ai : Ic_at_d H i X A π z Z α) (an : Ic_at_d H n N B σ u Y β)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (bound : Ic_bound_d I H Q N S σ n χ)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y k → Rd_entry_d y x' π)
    (image : ∀ y, Rd_entry_d y U R ↔ ∃ x, M.mem x D ∧ Rd_entry_d x y k)
    (small : Rr_small_d I X R U)
    (left : Smap_d I ω c₀ c X₀ X p) (right : Smap_d I ω c₀ d X₀ N q)
    (currentOrigin : It_map_d G o n q) (numbers : Rr_layer_d I ω X₀ R₀ w₀ z₀)
    (ic : Rd_entry_d C₀ C p) (id : Rd_entry_d C₀ C' q)
    (nn : Rr_layer_d I ω N S w' zn)
    (seed : Formula.satisfies ν tc_seed0_m) (issued : Formula.satisfies ι tg_issued0_m)
    (treeName : Rd_entry_d S₀ (ι.bound 7).val.val q)
    (hwν : (ν.bound 0).val = (⟨w',current.omega_mem⟩ : (smdl_structure_l I (R := S) mn.2.1).Domain))
    (newEq : ∀ j : Fin 14, ν.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get j) =
      ι.bound ([0,5,24,28,25,36,37,38,39,40,41,42,43,44].get j))
    (arity : ν.bound 3 = ι.bound 27) (boundEq : (ν.bound 28).val.val = χ)
    (oldLinks : ∀ j : Fin 5,
      Rd_entry_d ([⟨w',current.omega_mem⟩,(ν.bound 3).val,(ν.bound 1).val,(ν.bound 5).val,(ν.bound 7).val].get j).val
        (v ([16,24,15,13,11].get j)) k)
    (height : (smdl_structure_l I (R := S) mn.2.1).IsLimitOrdinal (ν.bound 2).val)
    (heightN : Rr_layer_d I γ₀ N S agN sgN) (layerN : Rr_layer_d I Bγ N S VgN tgN)
    (rankN : Rr_rank_d I N S agN VgN)
    (limitN : (smdl_structure_l I (R := S) mn.2.1).IsLimitOrdinal ⟨agN,heightN.member⟩)
    (lowerN : ∀ x, Rd_entry_d x agN S → Rd_entry_d x (ν.bound 1).val.val S)
    (omegaN : Rd_entry_d w' VgN S) (lettersN : Rd_entry_d (ι.bound 6).val.val VgN S)
    (baseCurrent : Tg_anchor_d I γ₀ Bγ N S q) (baseOld : Tg_anchor_d I γ₀ Bγ X R p)
    (ε : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ nd) 7)
    (reply : Formula.satisfies ε tg_reply_base0_m) (replyω : ε.bound 0 = ν.bound 0)
    (replyNum : ε.bound 3 = ν.bound 3)
    (replyLt : (smdl_structure_l I (R := S) mn.2.1).mem (ε.bound 2).val (ν.bound 3).val)
    (replyMem : (smdl_structure_l I (R := S) mn.2.1).mem (ε.bound 6).val (ν.bound 7).val)
    (empty : ∀ x, ¬ (smdl_structure_l I (R := S) mn.2.1).mem x (ε.bound 1).val)
    (s_old t_old k_old : (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ nd).Domain)
    (play : Tg_play_d I N S C' (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val s_old.val.val)
    (short : Tg_graph_d (kp_pair_l hN) k_old.val s_old.val)
    (size : (smdl_structure_l I (R := S) mn.2.1).MemberSubset k_old.val (ι.bound 26).val)
    (labels : (smdl_structure_l I (R := S) mn.2.1).MemberSubset t_old.val (ι.bound 23).val)
    (oldPoints : ∀ j : Fin 2, Rd_entry_d (([s_old,t_old].get j).val.val) (v ([40,41].get j)) k)
    (name : Tg_saved_name_d I S₀ X R w U r p) :
    ∃ Xc Kc jc ℓ e ec : (smdl_structure_l I (R := S) mn.2.1).Domain,
      ∃ Ls Js Os Zs Ds ps Vs Ws qs d₁ N₁ S₁ j₁ q₁ p₁ D₁ t₁ w₁ η₁ C₁,
      ∃ restored : Tg_context_d I w₁ N₁ S₁ η₁ C₁,
      ∃ nc₁ : Nonempty {x : (smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩).Domain //
        (smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩).mem x ⟨C₁,restored.member⟩},
      ∃ ρ₁ : Env (rt_model_l (M := smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩) ⟨C₁,restored.member⟩ nc₁) 54,
      ∃ θ₁ : Env (rt_model_l (M := smdl_structure_l I (R := S₁) ⟨w₁,restored.omega_mem⟩) ⟨C₁,restored.member⟩ nc₁) 17,
        (∀ j, Rd_entry_d (v j) (ρ₁.bound j).val.val j₁) ∧
        Ic_two_step_d hZF ω c₀ X₀ R₀ c X R d N S p D k zn n m T Q G E Λ H QT GT i o B σ
          w η C (v 15) (v 18) r Ls Js Os Zs Ds ps Vs Ws qs d₁ N₁ S₁ j₁ q₁ p₁ q C₀ S₀ η' C' γ₀ Bγ D₁ t₁
          w₁ η₁ C₁ mn hN ⟨V,same.common.right_rank.2.1⟩ ⟨w',current.omega_mem⟩ (ν.bound 1).val
          ℓ e βc Xc Kc jc ec tree.omega current nd ν ι restored nc₁ ρ₁ θ₁ := by
  let Nn := smdl_structure_l I (R := S) mn.2.1
  let cn : Nn.Domain := ⟨C',current.member⟩
  let vn : Nn.Domain := ⟨V,same.common.right_rank.2.1⟩
  let wn : Nn.Domain := ⟨w',current.omega_mem⟩
  obtain ⟨Xc,Kc,Rc,Lc,Fc,cN,dN,Nc,Tc,jc,κc,Uc,Dc,uc,
    rankc,sourcec,hLδ,hκL,hτL,hχL,locc,cardc,strongc,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,subtypec⟩ := raw
  let ψc : Env Nn 17 := ⟨fun j => [wn,(ν.bound 3).val,κc,(ν.bound 8).val,(ν.bound 9).val,Uc,
    (ν.bound 13).val,(ν.bound 14).val,(ν.bound 16).val,uc,(ν.bound 21).val,(ν.bound 22).val,
    (ν.bound 23).val,(ν.bound 24).val,(ν.bound 25).val,(ν.bound 26).val,(ν.bound 27).val].get j,fun _ => wn⟩
  -- 前十六项仅记载源端既有坐标；直接取后续证书，避免逐项消去整个依赖尾部。
  have stage := subtypec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- 依次读取原系统、代表池、目标环境和恢复记录，保持每段的依赖边界。
  refine stage.elim fun Ls h => h.elim fun Js h => h.elim fun Os h =>
    h.elim fun Zs h => h.elim fun Ds h => h.elim fun ps h =>
    h.elim fun Vs h => h.elim fun Ws h => h.elim fun qs h =>
    h.elim fun d₁ h => h.elim fun N₁ h => h.elim fun S₁ h =>
    h.elim fun j₁ h => h.elim fun q₁ h => h.elim fun p₁ stage => ?_
  have factory := stage.1
  refine stage.2.elim fun target h => h.elim fun A₁ h => h.elim fun Q₁ h =>
    h.elim fun B₁ h => h.elim fun e₁ h => h.elim fun D₁ h =>
    h.elim fun Γ₁ h => h.elim fun t₁ stage => ?_
  have pool₁ := stage.1
  have domain₁ := stage.2.1
  have ft₁ := stage.2.2.2.1
  have present₁ := stage.2.2.2.2.1
  refine stage.2.2.2.2.2.2.2.elim fun η₁ stage => ?_
  have points₁ := stage.1
  refine stage.2.2.elim fun ηP h => h.elim fun CP h => h.elim fun LP h =>
    h.elim fun VP h => h.elim fun rP stage => ?_
  have iwP := stage.1
  have iηP := stage.2.1
  have iCP := stage.2.2.1
  refine stage.2.2.2.2.2.2.elim fun savedP h => h.elim fun nc₁ h =>
    h.elim fun ρ₁ h => h.elim fun θ₁ stage => ?_
  have round₁ := stage.2.1
  have recordPoints := stage.2.2.1
  have reflectedPoints := stage.2.2.2.1
  have subtype₁ := stage.2.2.2.2.1
  have prior₁ := stage.2.2.2.2.2.1
  have compiled₁ := stage.2.2.2.2.2.2
  have images (j : Fin 17) : Rd_entry_d (ψc.bound j).val (θ₁.bound j).val.val t₁ :=
    Eq.mpr (congrArg (fun x => Rd_entry_d (ψc.bound j).val x.val t₁) (reflectedPoints j)) (points₁ j)
  have programEq : ∀ j : Fin 9,
      ν.bound ([14,16,21,22,23,24,25,26,27].get j) = ι.bound ([36,37,38,39,40,41,42,43,44].get j) :=
    Fin.cases (newEq 5) (Fin.cases (newEq 6) (Fin.cases (newEq 7) (Fin.cases (newEq 8)
      (Fin.cases (newEq 9) (Fin.cases (newEq 10) (Fin.cases (newEq 11)
        (Fin.cases (newEq 12) (Fin.cases (newEq 13) (fun j => Fin.elim0 j)))))))))
  have programs : ∀ j : Fin 9, Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get j)).val.val
      (θ₁.bound ([7,8,10,11,12,13,14,15,16].get j)).val.val t₁ := by
    intro j
    have eq : ψc.bound ([7,8,10,11,12,13,14,15,16].get j) =
        (ν.bound ([14,16,21,22,23,24,25,26,27].get j)).val := by
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))) j
    have h := images ([7,8,10,11,12,13,14,15,16].get j)
    rw [eq] at h
    exact Eq.mp (congrArg (fun x : (rt_model_l (M := Nn) cn nd).Domain =>
      Rd_entry_d x.val.val (θ₁.bound ([7,8,10,11,12,13,14,15,16].get j)).val.val t₁) (programEq j)) h
  have firstPoint : Rd_entry_d (ν.bound 0).val.val (θ₁.bound 0).val.val t₁ :=
    Eq.mpr (congrArg (fun x : Nn.Domain => Rd_entry_d x.val (θ₁.bound 0).val.val t₁) hwν) (images 0)
  have pointsν : ∀ j : Fin 5, Rd_entry_d (ν.bound ([0,8,9,13,3].get j)).val.val
      (θ₁.bound ([0,3,4,6,1].get j)).val.val t₁ :=
    Fin.cases firstPoint (Fin.cases (images 3) (Fin.cases (images 4)
      (Fin.cases (images 6) (Fin.cases (images 1) (fun j => Fin.elim0 j)))))
  have linksν : ∀ j : Fin 4, ν.bound ([0,8,9,13].get j) = ι.bound ([0,24,28,25].get j) :=
    Fin.cases (newEq 0) (Fin.cases (newEq 2) (Fin.cases (newEq 3)
      (Fin.cases (newEq 4) (fun j => Fin.elim0 j))))
  have omegaOld : Rd_entry_d wn.val w k := hw ▸ oldLinks 0
  have above : Rd_entry_d χ Lc.val S := boundEq ▸ hχL
  obtain ⟨W,hWA,_,rA,rB,_,iV⟩ := same.work
  -- 这里只读取根图方程；不消去包含后续全部工厂证书的长合取。
  have rootGraph₁ : ∀ x E, Rd_entry_d x E q₁ ↔
      M.mem x X₀ ∧ ∃ y, Rd_entry_d x y p ∧ Rd_entry_d y E j₁ :=
    factory.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have oldTree : Rd_entry_d S₀ (ρ₁.bound 19).val.val q₁ :=
    (rootGraph₁ S₀ (ρ₁.bound 19).val.val).mpr
      ⟨left.1.1.input_mem_of_pairMember (name v code),v 19,name v code,recordPoints 19⟩
  -- 先指定最终见证，再在确定的两步复制命题中核验应用，避免重推完整结论类型。
  refine ⟨Xc,Kc,jc,Lc,Fc,e₁,Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,d₁,N₁,S₁,j₁,q₁,p₁,D₁,t₁,
    (η₁.bound 0).val,ηP,CP,savedP.context,nc₁,ρ₁,θ₁,recordPoints,?_⟩
  exact factory.copy_history_l hZFC mx mn hN vn wn (ν.bound 1).val Lc Fc βc Xc Kc jc
    (ν.bound 2).val Rc A₁ Q₁ B₁ e₁ pool₁ domain₁ ft₁.1.1.1 present₁ nn sourcec rankc
    height locc strongc cardc root tree hist hnω hm qi qn origin ai an lf levels
    bound above iV hWA rA rB same.limit square image small (saved.control_l I hZF.1 code)
    (oldLinks 2) omegaOld right currentOrigin numbers ic id current nd ν ι seed issued treeName hwν rfl
    linksν arity hτL heightN layerN rankN limitN lowerN omegaN lettersN baseCurrent baseOld
    ε reply replyω replyNum replyLt replyMem empty savedP.context iwP iηP iCP nc₁ ρ₁ θ₁
    round₁ subtype₁ compiled₁ prior₁ programs (recordPoints 15) oldTree
    s_old t_old k_old play short size labels
    (Fin.cases ⟨v 40,oldPoints 0,recordPoints 40⟩
      (Fin.cases ⟨v 41,oldPoints 1,recordPoints 41⟩ (fun j => Fin.elim0 j))) pointsν

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从实际旧回答推进原树与复制历史

旧活动行确定同一个共同层，原生秩唯一性把它识别为存档的秩段。
当前历史界在反射层内，因而全部旧共同层也在该层内。完整语言沿实际
共同图搬运，逆图同时给出原生工厂需要的候选对应和全部前驱方程。
保存时的原码视图与历史选出的共同图核对后，直接调用当前继续核及原工厂。
同一次工厂的后继、完整代表池、恢复记录和程序再交给两步复制，
返回原树与工作历史的两次同步延伸，以及实际回答和全部档案视图保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_saved_d.prepare_l
    {ω T Q G E Λ m H ST QT GT i n X R A π z Z α N S B σ u Y β c d
      c₀ X₀ R₀ w₀ z₀ p q C₀ S₀ w η C L U r w' η' C' zx zn χ γ₀ Bγ
      g₀ l₀ φ₀ V₀ Γ₀ m₀ o : M.Domain}
    (saved : Tg_saved_d I w X R η C L U r)
    (root : Zc_model_d I ω c₀ X₀ R₀) (numbers : Rr_layer_d I ω X₀ R₀ w₀ z₀)
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (tree : It_tree_d hZF ω c₀ m T Q G E)
    (hnω : M.mem n ω) (hm : M.SuccessorOf m n)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (ai : Ic_at_d H i X A π z Z α) (an : Ic_at_d H n N B σ u Y β)
    (qi : Rd_entry_d i c Q) (qn : Rd_entry_d n d Q)
    (mx : Smdl_d I c X R) (mn : Smdl_d I d N S)
    (left : Smap_d I ω c₀ c X₀ X p) (right : Smap_d I ω c₀ d X₀ N q)
    (origin : It_map_d G o i p) (currentOrigin : It_map_d G o n q)
    (id : Rd_entry_d C₀ C' q)
    (current : Tg_context_d I w' N S η' C')
    (nx : Rr_layer_d I ω X R w zx) (nn : Rr_layer_d I ω N S w' zn)
    (hi : M.mem i n) (active : Rd_entry_d i L Λ) (lf : M.IsSetFunction I Λ)
    (bound : Ic_bound_d I H Q N S σ n χ) (member : Rd_entry_d χ C' S)
    (basis : Tg_basis_d I γ₀ Bγ C₀ w X R C p)
    (name : Tg_saved_name_d I S₀ X R w U r p)
    (baseCurrent : Tg_anchor_d I γ₀ Bγ N S q)
    (ncN : Nonempty {x : (smdl_structure_l I (R := S) mn.2.1).Domain //
      (smdl_structure_l I (R := S) mn.2.1).mem x ⟨C',current.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ ncN) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hwι : (ι.bound 0).val.val = w')
    (treeName : Rd_entry_d S₀ (ι.bound 7).val.val q)
    (alphabet : ∃ a, M.mem a Bγ ∧ Rd_entry_d a (ι.bound 6).val.val q)
    (ne : ι.bound 23 ≠ ι.bound 1)
    (prior : Ic_agree_d I X R A π N S B σ L l₀ φ₀ U V₀ Γ₀ g₀)
    (view : Tg_saved_view_d I X R w U r γ₀ g₀ N S w' C' (ι.bound 4).val.val
      (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val zn m₀ (ι.bound 20).val.val)
    (index : Rd_entry_d m₀ (ι.bound 22).val.val zn) (below : Rd_entry_d χ (ι.bound 5).val.val S) :
    let ground := (root.map_l hZF tree.omega mn right).native_l I hZF tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    Tg_prepared_d hZF ω T E m QT GT c₀ X₀ R₀ N S B σ d q C₀ S₀ w' η' C' zn χ γ₀ Bγ
      i c X R w η C L U r p A π o n Q G Λ H mn hN current ncN ι tree.omega := by
  intro ground hN
  -- 原档案已经保存根像及完整 γ 基底，此处直接读取其原生表达。
  have baseOld := basis.anchor_l I
  obtain ⟨ic,aγ,Vγ,sγ,tγ,baseHeight,baseLayer,baseRank,baseLimit₀,baseOmega,fixed⟩ := basis
  have baseLimit : (smdl_structure_l I (R := R) mx.2.1).IsLimitOrdinal ⟨aγ,baseHeight.member⟩ :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp
      ((rr_truth_native_l I mx.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
        (fun _ : Fin 1 => ⟨aγ,baseHeight.member⟩)).mp baseLimit₀)
  -- 同一活动历史已经生产并识别共同层，主证明直接消费其支撑和所属。
  obtain ⟨a,RA,K,b,RB,K',l,φ,V,Γ,t,ma,sa,copy,mb,sb,next,same,support,limit',inside⟩ :=
    saved.common_l hZF root hist tree levels ai an qi qn mx mn left right current nx hi active lf bound member
  have sourceGround := (root.map_l hZF tree.omega mx left).native_l I hZF tree.omega
  have hx := ZFC.models_zf_l sourceGround
  have hn := ZFC.models_zf_l ground
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Ln : Xn.Domain := ⟨L, same.common.left_rank.1⟩
  let wg : Xn.Domain := ⟨w, saved.context.omega_mem⟩
  let pv : Fin 2 → Xn.Domain := fun j =>
    ⟨Fin.cases L (fun _ : Fin 1 => w) j,
      Fin.cases same.common.left_rank.1 (fun _ => saved.context.omega_mem) j⟩
  have supportNative := (rr_truth_native_l I mx.2.1 (sc_inaccessible_m (.bound 1) .newest)
    (by simp -implicitDefEqProofs) pv).mp support
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff (kp_pair_l (ZF.modelsKP hx)) hx.1,
    Formula.satisfies_isStrongLimitCardinal_iff (kp_pair_l (ZF.modelsKP hx)) hx.1] at supportNative
  have hωL : Xn.mem wg Ln := supportNative.1
  have regularL : Xn.IsRegularCardinal (kp_pair_l (ZF.modelsKP hx)) Ln := supportNative.2.1
  let Un : Xn.Domain := ⟨U, saved.rank.elim fun m _ => m 0⟩
  have ru := (rr_rank_native_l I mx.2.1 (ZF.modelsKP hx) Ln Un).mp same.common.left_rank
  let Nn := smdl_structure_l I (R := S) mn.2.1
  let ln : Nn.Domain := ⟨l, same.common.right_rank.1⟩
  have limit : Nn.IsLimitOrdinal ln := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ln)).mp limit')
  let vn : Nn.Domain := ⟨V, same.common.right_rank.2.1⟩
  let cn : Nn.Domain := ⟨C', current.member⟩
  let ηn : Nn.Domain := ⟨η', current.height⟩
  let χn : Nn.Domain := ⟨χ, bound.ordinal.1 0⟩
  have rv := (rr_rank_native_l I mn.2.1 (ZF.modelsKP hn) ln vn).mp same.common.right_rank
  have rc := (rr_rank_native_l I mn.2.1 (ZF.modelsKP hn) ηn cn).mp ((rr_rank_truth_l I).mpr current.rank)
  obtain ⟨nc, ρ, code, round, hw, hk, _, _, hu⟩ := saved.read_l I hZF.1
  have fsx := saved.context.finite_l mx.2.1 hx.1
  have parts := tg_round_parts_l (ZF.modelsKP hx) fsx nc ρ round
  let v : Fin 54 → M.Domain := fun j => (ρ.bound j).val.val
  let f : Fin 10 → Term 54 := fun j => [.bound 16, .bound 15, .bound 24, .bound 14, .bound 13,
    .bound 12, .bound 6, .bound 5, .bound 4, .bound 3].get j
  let ε := Definitional.Env.substitute ρ f
  have language : Formula.satisfies ε ee_language0_m := parts.language
  have elastic := parts.elastic
  have heightMember := parts.height
  obtain ⟨_, _, nd, θ, points, hwθ, valid⟩ := same.common.language_native_l hZF tree.omega
    root.model mx mn (ZF.modelsKP hx) (ZF.modelsKP hn) left right root.ext numbers nx nn
    saved.context current ic id
    (fun x hx => (current.finite_l mn.2.1 hn.1).transitive vn inside
      ⟨x,(mn.2.2.2 x V hx).1⟩ hx) nc ε hw hk language
  obtain ⟨D,k,carrier,fk,image,pred,graph⟩ := same.common.reverse_native_l hZF mx (ZF.modelsKP hx)
  -- 逆图只使用原共同层；旧复制消费者另由实际交换方块恢复工作坐标。
  have square x x' y (xx : Rd_entry_d x x' σ) (pair : Rd_entry_d x y k) : Rd_entry_d y x' π := by
    have yx := (graph x y).mp pair
    obtain ⟨y',_,yy⟩ := copy.1.1.2.2 y
      ((same.common.carrier y).mp (same.common.injection.1.input_mem_of_pairMember yx)).1
    exact next.1.1.1.2 x y' x' (same.points y y' x yy yx) xx ▸ yy
  have coords (j : Fin 10) : (ε.bound j).val.val = v ([16,15,24,14,13,12,6,5,4,3].get j) := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))) j
  -- 旧完整类型与四个原查询一起进入当前层，弹性事实沿完整前驱方程保持。
  have huΓ := (same.common.carrier (v 11)).mpr ⟨(ρ.bound 11).val.property, hu⟩
  obtain ⟨a', ha', pair⟩ := same.common.injection.1.2.2 (v 11) huΓ
  have haV := (same.common.image a').mpr ⟨v 11, huΓ, pair⟩
  let a₀ : Nn.Domain := ⟨a', ha'⟩
  let a : (rt_model_l (M := Nn) cn nd).Domain :=
    ⟨a₀, (current.finite_l mn.2.1 hn.1).transitive vn inside a₀ haV⟩
  have move (j : Fin 10) (hj : Rd_entry_d (v ([16,15,24,14,13,12,6,5,4,3].get j)) (v 11) R) :
      Rd_entry_d (θ.bound j).val.val a' S :=
    (same.common.pred (v 11) a' pair _).mpr ⟨_, hj, coords j ▸ points j⟩
  have elastic' : Formula.satisfies (θ.push a)
      (ee_elastic_m (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest) := by
    simp only [ee_elastic_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at elastic ⊢
    exact ⟨⟨move 6 elastic.1.1, move 7 elastic.1.2⟩, move 8 elastic.2.1, move 9 elastic.2.2⟩
  -- 标签的自然数值域来自保存的真实请求；共同图搬运整图及两个后继。
  have empty := parts.empty
  have emptyω := parts.empty_omega
  have short_graph := parts.graph
  have first₀ := parts.first
  have last₀ := parts.last
  have num := parts.finite
  have labels₀ := parts.labels
  have omega : Xn.IsOmega (ρ.bound 16).val :=
    (show (ρ.bound 16).val = (⟨w, nx.member⟩ : Xn.Domain) from Subtype.ext hw).symm ▸
      nx.omega_l I (ZF.modelsKP hZF) sa.omega hx.1
  obtain ⟨k₀, l₀, t₀, ik, il, it, hkV, hlV, htV, labels₁, first₁, last₁⟩ :=
    same.common.labels_l hZF mx.2.1 mn.2.1 (ZF.modelsKP hx) hn.1
      (ρ.bound 16).val (ρ.bound 22).val (ρ.bound 23).val (ρ.bound 24).val (ρ.bound 41).val
      (θ.bound 0).val (θ.bound 2).val omega num first₀ last₀ labels₀ (points 0) (points 2)
  have scope (x : Nn.Domain) (hxV : Nn.mem x vn) : Nn.mem x cn :=
    (current.finite_l mn.2.1 hn.1).transitive vn inside x hxV
  let ζ : Env (rt_model_l (M := Nn) cn nd) 3 :=
    ⟨fun j => [⟨t₀, scope t₀ htV⟩, ⟨k₀, scope k₀ hkV⟩, ⟨l₀, scope l₀ hlV⟩].get j, fun _ => a⟩
  -- 从同一真实旧轮读取七项回答基底，全部查询仍使用原来的对象码。
  let ε₀ : Env (rt_model_l (M := Xn) ⟨C, saved.context.member⟩ nc) 7 :=
    ρ.reindex (fun j => [16,17,23,24,2,1,0].get j)
  have base₀ : Formula.satisfies ε₀ tg_reply_base0_m := parts.reply
  let ag : Xn.Domain := ⟨aγ, baseHeight.member⟩
  let Vg : Xn.Domain := ⟨Vγ, baseLayer.member⟩
  -- 两侧复制方块核对旧视图，再从同一存档读取下界。
  refine (view.read_l I hZF.1 code prior same copy.1.1 next.1
    nn.injection.1.1 index it (points 1) pair).elim fun trace rest => ?_
  refine rest.elim fun s_cur rest => ?_
  obtain ⟨is_cur,play_cur⟩ := rest
  let sn : Nn.Domain := ⟨s_cur,play_cur.elim fun m _ => m 4⟩
  let sc : (rt_model_l cn nd).Domain := ⟨sn,play_cur.member_l I⟩
  have current_graph : Tg_graph_d (kp_pair_l hN) k₀ sn := rr_native_graph_l I hZF.1 mx.2.1 mn.2.1
    hx.1 (KP.exists_pair (ZF.modelsKP hx)) hN.1 (KP.exists_pair hN)
    Un vn (v_transitive_l (kp_pair_l (ZF.modelsKP hx)) ru)
    (v_transitive_l (kp_pair_l hN) rv) same.common.carrier same.common.injection same.common.image same.common.pred
    (ρ.bound 22).val (ρ.bound 40).val k₀ sn ik is_cur short_graph
  -- 存档给出 γ≤旧回答域；同一原码及序数层的唯一性识别当前所用的高度。
  obtain ⟨v₀,code₀,lower₀,_⟩ := view
  have eqτ : v₀ 15 = v 15 := congrFun (code₀.inj_l I hZF.1 code) 17
  obtain ⟨a₀,s₀,layer₀,lower₀⟩ :=
    Eq.mp (congrArg (fun τ => It_lower_d I γ₀ X R τ) eqτ) lower₀
  have eqγ := (layer₀.unique_l (ZF.modelsKP hZF) baseHeight saved.ext).1
  subst a₀
  have oldLanguage := language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at oldLanguage
  have oldLimit := (rt_limit_l fsx.transitive nc (ZF.modelsKP hx) (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp oldLanguage.2.1)
  have oldBelow := ZF.v_ordinal_height_l hx ru oldLimit.1 hk
  have baseBelow : Xn.mem ag Ln := ordinal_down_l (ZF.modelsKP hx) baseLimit.1
    (v_ordinal_l (kp_pair_l (ZF.modelsKP hx)) ru) (fun x hx => lower₀ x.val hx) oldBelow
  have rg := (rr_rank_native_l I mx.2.1 (ZF.modelsKP hx) ag Vg).mp baseRank
  have hgU := ZF.v_mem_l (kp_pair_l (ZF.modelsKP hx)) hx rg ru baseBelow
  have eqw : (ρ.bound 16).val = wg := Subtype.ext hw
  have hwg : Xn.mem (ρ.bound 16).val Vg := Eq.mpr (congrArg (fun x => Xn.mem x Vg) eqw) baseOmega
  have hg := v_transitive_l (kp_pair_l (ZF.modelsKP hx)) rg
  have he : Xn.mem (ρ.bound 17).val (ρ.bound 16).val := emptyω
  have hng := hg (ρ.bound 16).val hwg (ρ.bound 24).val num
  have low : ∀ j : Fin 4, Xn.mem (ε₀.bound (j.castAdd 3)).val Vg :=
    Fin.cases hwg (Fin.cases (hg _ hwg _ he)
      (Fin.cases (hg _ hng _ last₀.predecessor_mem) (Fin.cases hng (fun j => Fin.elim0 j))))
  have small := tg_reply_base_scope_l (ZF.modelsKP hx) (nx.omega_l I (ZF.modelsKP hZF) sa.omega hx.1)
    fsx nc ε₀ rg baseLimit eqw (Eq.mp (congrArg (fun x => Xn.mem (ρ.bound 24).val x) eqw) num) low base₀
  obtain ⟨ε₁, replyPoints, reply⟩ := same.common.anchor_peer_l hZF sa.omega root.model mx mn left right
    (left.extensional_l hZF sa.omega root.model mx root.ext)
    (right.extensional_l hZF sa.omega root.model mn root.ext) baseOld baseCurrent baseLayer
    (v_transitive_l (kp_pair_l (ZF.modelsKP hx)) ru) hgU ⟨C, saved.context.member⟩ cn
    fsx.transitive (current.finite_l mn.2.1 hn.1).transitive nc nd ic id
    tg_reply_base0_m tg_reply_base0_closed_l ε₀ small base₀
  have rw₀ : ε₁.bound 0 = θ.bound 0 :=
    Subtype.ext (Subtype.ext (same.common.injection.1.1.2 _ _ _ (replyPoints 0) (points 0)))
  have rn₀ : ε₁.bound 3 = θ.bound 2 :=
    Subtype.ext (Subtype.ext (same.common.injection.1.1.2 _ _ _ (replyPoints 3) (points 2)))
  have rl₀ : Nn.mem (ε₁.bound 2).val (θ.bound 2).val :=
    (same.common.pred _ _ (points 2) _).mpr ⟨_, last₀.predecessor_mem, replyPoints 2⟩
  have rh₀ : Nn.mem (ε₁.bound 6).val a.val :=
    (same.common.pred _ _ pair _).mpr ⟨_, heightMember, replyPoints 6⟩
  have re₀ (x : Nn.Domain) (hx₀ : Nn.mem x (ε₁.bound 1).val) : False := by
    obtain ⟨y, hy, hyx⟩ := (same.common.pred _ _ (replyPoints 1) x.val).mp hx₀
    let y₀ : Xn.Domain := ⟨y, ((same.common.carrier y).mp (same.common.injection.1.input_mem_of_pairMember hyx)).1⟩
    exact empty y₀ hy
  -- 继续核读取同一个旧事件。
  let χ₀ : (rt_model_l (M := Nn) cn nd).Domain := ⟨χn,member⟩
  obtain ⟨ν,seedν,resultν,oldEq,typeEq,arity,newEq,labelsSub,boundEq⟩ :=
    current.continue_native_l hZF mn.2.1 hn nd ι issued hwι ne θ valid hwθ a (ζ.bound 0) χ₀
      (ζ.bound 1).val (ζ.bound 2).val elastic' labels₁ first₁ last₁ trace below
  have fsN := current.finite_l mn.2.1 hn.1
  have current_labels := (rt_fn_l fsN.transitive nd hn.1
    (ι.bound 26) (ι.bound 0) (ι.bound 23)).mp
    ((tg_issued_sat_l (rt_pair_l fsN.transitive nd hn.1 fsN.pair)
      (rt_model_ext_l hn.1 fsN.transitive nd) ι).mp issued).labels
  have short_domain : Nn.MemberSubset k₀ (ι.bound 26).val := by
    intro i hi
    obtain ⟨x,_,p,pair,hp⟩ := labels₁.2.1 i hi
    exact (current_labels.bound_l ⟨p,pair,labelsSub p hp⟩).1
  -- 完整前驱方程把同一个 γ 下界送到当前候选，供两步复制的临界点界使用。
  have anchorN := baseCurrent
  obtain ⟨agN,VgN,sgN,tgN,heightN,layerN,rankN,fixedN⟩ := anchorN
  have imageγ := (same.common.layer_image_l (ZF.modelsKP hZF) mx.2.1
    (right.extensional_l hZF sa.omega root.model mn root.ext) baseHeight heightN
    (v_transitive_l (kp_pair_l (ZF.modelsKP hx)) ru)
    (ZF.v_ordinal_mem_l (kp_pair_l (ZF.modelsKP hx)) hx ru baseBelow)).1
  have lowerN x (hx : Rd_entry_d x agN S) : Rd_entry_d x (ν.bound 1).val.val S := by
    obtain ⟨y,hy,iy⟩ := (same.common.pred aγ agN imageγ x).mp hx
    have h : Rd_entry_d x (θ.bound 1).val.val S :=
      (same.common.pred _ _ (points 1) x).mpr ⟨y,lower₀ y hy,iy⟩
    have eq : ν.bound 1 = θ.bound 1 := oldEq 1
    exact Eq.mpr (congrArg (fun a : (rt_model_l (M := Nn) cn nd).Domain =>
      M.PairMember I x a.val.val S) eq) h
  have candidateLower : It_lower_d I γ₀ N S (ν.bound 1).val.val := ⟨agN,sgN,heightN,lowerN⟩
  -- τ+ω 的最小极限切片同时落在旧共同层内，并低于当前超过关系给出的较大极限。
  obtain ⟨αc,βc,cutHeight,cutLayer,cutPoint,cutLimit,cutRank,least⟩ :=
    same.common.limit_cut_l (ZF.modelsKP hZF) mx.2.1 mn.2.1 hx (ZF.modelsKP hn)
      wg Ln (ρ.bound 15).val (θ.bound 1).val
      (nx.omega_l I (ZF.modelsKP hZF) tree.omega hx.1) regularL hωL oldBelow (points 1)
  have facts := seedν
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at facts
  obtain ⟨_,_,_,limitν,_,_,_,_,exceedsν,_⟩ := facts
  have limitν := (rt_limit_l (current.finite_l mn.2.1 hn.1).transitive nd
    (ZF.modelsKP hn) (ν.bound 8)).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp limitν)
  have lowerν : Nn.mem (θ.bound 1).val (ν.bound 8).val :=
    Eq.mp (congrArg (fun x => Nn.mem x (ν.bound 8).val) (congrArg Subtype.val (oldEq 1)))
      ((Formula.satisfies_conj_iff ..).mp exceedsν).1
  have memberν : Nn.mem (ν.bound 1).val βc :=
    Eq.mpr (congrArg (fun x => Nn.mem x βc) (congrArg Subtype.val (oldEq 1))) cutPoint
  -- 原源本身满足 ZFC；编号及最小原像在该源内构造，供原工厂的小集合收集使用。
  have small : Rr_small_d I X R U := by
    intro b hb _
    let b₀ : Xn.Domain := ⟨b,hb⟩
    let J := kp_pair_l (ZF.modelsKP hx)
    obtain ⟨μ,f,ord,fn,onto⟩ := ZFC.ordinal_enum_l sourceGround J b₀
    obtain ⟨g,inj,_⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hx J ord fn onto
    apply (rf_small_native_l I mx.2.1 b₀).mpr
    simp only [sc_small_m, Formula.satisfies_exists_iff]
    exact ⟨μ,g,(sc_index_sat_l (ZF.modelsKP hx) _ (.bound 1) (.bound 2) .newest).mpr
      (Sc_index_d.of_injection_l (ZF.modelsKP hx) ord inj)⟩
  let wn : Nn.Domain := ⟨w',current.omega_mem⟩
  have hwν : (ν.bound 0).val = wn := Subtype.ext
    ((congrArg (fun x => x.val.val) (oldEq 0)).trans hwθ)
  have oldLinks : ∀ j : Fin 5,
      Rd_entry_d ([wn,(ν.bound 3).val,(ν.bound 1).val,(ν.bound 5).val,(ν.bound 7).val].get j).val
        (v ([16,24,15,13,11].get j)) k := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))))
    · change Rd_entry_d w' (v 16) k
      exact Eq.mp (congrArg (fun x => Rd_entry_d x (v 16) k) hwθ) ((graph _ _).mpr (points 0))
    · change Rd_entry_d (ν.bound 3).val.val (v 24) k
      have eq : ν.bound 3 = θ.bound 2 := oldEq 2
      exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (v 24) k) eq) ((graph _ _).mpr (points 2))
    · change Rd_entry_d (ν.bound 1).val.val (v 15) k
      have eq : ν.bound 1 = θ.bound 1 := oldEq 1
      exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (v 15) k) eq) ((graph _ _).mpr (points 1))
    · change Rd_entry_d (ν.bound 5).val.val (v 13) k
      have eq : ν.bound 5 = θ.bound 4 := oldEq 4
      exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (v 13) k) eq) ((graph _ _).mpr (points 4))
    · change Rd_entry_d (ν.bound 7).val.val (v 11) k
      exact Eq.mpr (congrArg (fun x => Rd_entry_d x.val.val (v 11) k) typeEq) ((graph _ _).mpr pair)
  have limitC : Nn.IsLimitOrdinal ηn := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ηn)).mp current.limit)
  have regular := (tg_issued_control_l hN rc limitC fsN nd ι issued).2
  have regularν : Nn.IsRegularCardinal (kp_pair_l hN) (ν.bound 2).val :=
    Eq.mpr (congrArg (fun x => Nn.IsRegularCardinal (kp_pair_l hN) x)
      (congrArg Subtype.val (newEq 1))) regular
  have raw := Tg_context_d.raw_continue_l hZFC tree.omega mn.2.1 ground
    vn wn ηn cn αc βc ln nd ν v current mn root mx left right numbers ic id saved code oldLinks
    nn rv limit carrier fk image pred same.common.left_closed small cutLayer memberν cutLimit cutRank
    (least _ limitν lowerν) hwν regularν seedν resultν
  -- 当前锚点的极限性及 ω 所属沿同一完整共同图传输。
  let agn : Nn.Domain := ⟨agN,heightN.member⟩
  have hagU := ZF.v_ordinal_mem_l (kp_pair_l (ZF.modelsKP hx)) hx ru baseBelow
  let ng : Nonempty {x : Xn.Domain // Xn.mem x Un} := ⟨⟨ag,hagU⟩⟩
  let γsrc : Env (rt_model_l Un ng) 1 := ⟨fun _ => ⟨ag,hagU⟩,fun _ => ⟨ag,hagU⟩⟩
  let γdst : Env Nn 1 := ⟨fun _ => agn,fun _ => agn⟩
  have limitN := (KP.limit0_sat_l hN γdst .newest).mp
    ((rr_native_delta_l I mx.2.1 mn.2.1 Un (v_transitive_l (kp_pair_l (ZF.modelsKP hx)) ru) ng
      same.common.carrier same.common.injection same.common.pred (KP.limit0_m .newest)
      (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) γsrc γdst (fun _ => imageγ)).mp
        ((KP.limit0_sat_l (ZF.modelsKP hx) _ .newest).mpr baseLimit))
  have imageV := (same.common.layer_image_l (ZF.modelsKP hZF) mx.2.1
    (right.extensional_l hZF sa.omega root.model mn root.ext) baseLayer layerN
    (v_transitive_l (kp_pair_l (ZF.modelsKP hx)) ru) hgU).1
  have iw : Rd_entry_d w w' t := by
    have h : Rd_entry_d (ρ.bound 16).val.val (θ.bound 0).val.val t := points 0
    rw [hw,hwθ] at h
    exact h
  have omegaN : Rd_entry_d w' VgN S := (same.common.pred _ _ imageV _).mpr ⟨w,baseOmega,iw⟩
  have lettersN : Rd_entry_d (ι.bound 6).val.val VgN S := by
    obtain ⟨x,hx,ix⟩ := alphabet
    obtain ⟨y,_,iy⟩ := layerN.injection.1.2.2 x hx
    have eq := right.1.1.1.2 x y (ι.bound 6).val.val (fixedN x y iy) ix
    exact (layerN.image _).mpr ⟨x,hx,eq ▸ iy⟩
  -- 原结果的同一工厂与恢复池交给完整两步复制，主证明只组合其结论。
  have replyNum : ε₁.bound 3 = ν.bound 3 := rn₀.trans (oldEq 2).symm
  have replyω : ε₁.bound 0 = ν.bound 0 := rw₀.trans (oldEq 0).symm
  have replyLt : Nn.mem (ε₁.bound 2).val (ν.bound 3).val :=
    Eq.mpr (congrArg (fun x : (rt_model_l (M := Nn) cn nd).Domain =>
      Nn.mem (ε₁.bound 2).val x.val) (oldEq 2)) rl₀
  have replyMem : Nn.mem (ε₁.bound 6).val (ν.bound 7).val :=
    Eq.mpr (congrArg (fun x : (rt_model_l (M := Nn) cn nd).Domain =>
      Nn.mem (ε₁.bound 6).val x.val) typeEq) rh₀
  have finish := Tg_continue_raw_d.saved_copy_l hZFC mx mn hN current nd ν ι v same βc raw
    saved code hw root tree hist hnω hm qi qn origin ai an lf levels bound square image small
    left right currentOrigin numbers ic id nn seedν issued treeName hwν newEq arity
    (congrArg (fun x => x.val.val) boundEq) oldLinks regularν.isLimitOrdinal
    heightN layerN rankN limitN lowerN omegaN lettersN baseCurrent baseOld
    ε₁ reply replyω replyNum replyLt replyMem re₀ sc (ζ.bound 0) (ζ.bound 1)
    play_cur current_graph short_domain labelsSub
    (Fin.cases ((graph _ _).mpr is_cur)
      (Fin.cases ((graph _ _).mpr it) (fun j => Fin.elim0 j))) name
  exact ⟨v, code, saved.control_l I hZF.1 code, l, φ, V, Γ, t, same, limit', inside,
    D, k, carrier, fk, image, pred, graph, square, nd, θ,
    fun j => (graph _ _).mpr (coords j ▸ points j), hwθ,
    (same.common.image _).mpr ⟨_, same.common.injection.1.input_mem_of_pairMember (points 1), points 1⟩,
    valid, a, (graph _ _).mpr pair, elastic', ζ,
    Fin.cases ((graph _ _).mpr it) (Fin.cases ((graph _ _).mpr ik)
      (Fin.cases ((graph _ _).mpr il) (fun j => Fin.elim0 j))), labels₁, first₁, last₁,
    ε₁, reply, fun j => (graph _ _).mpr (replyPoints j), rw₀, rn₀, rl₀, rh₀, re₀,
    ν,seedν,resultν,oldEq,typeEq,arity,newEq,labelsSub,congrArg (fun x => x.val.val) boundEq,candidateLower,
    αc,βc,cutHeight,cutLayer,memberν,cutLimit,cutRank,least _ limitν lowerν,raw,
    finish⟩

end YesMetaZFC.SetTheory.LargeCardinal
