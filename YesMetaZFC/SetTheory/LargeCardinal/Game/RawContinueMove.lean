import YesMetaZFC.SetTheory.LargeCardinal.Game.RawFirst
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueRenewal
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRestartLink
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReturnReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueFinish
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawInput

/-! # 非空原请求的同次两步核验

选中原档案后，第一次后继中的候选、恢复和重启只生成一次；第二个
实际扩展器随这份回答施加回原当前模型。两次原树延伸、全部旧档案、
源端保存证书及最后回答位置共同保留原图身份，不经过工作复制历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_request_d.continue_checked_l
    {ω S₀ X₀ R₀ w₀ γ₀ B₀ D₀ C₀ A₀ A N R w η C χ z k H r q c₀ n m T Q G E Λ c o f : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k H r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qn : Rd_entry_d n c Q) (mn : Smdl_d I c N R) (qr : Rd_entry_d o c₀ Q)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i μ, Rd_entry_d i μ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ μ F)
    (ne : v 23 ≠ v 1)
    (prior : Tg_prefix_d I k A N R C (v 4) (v 3) (v 20) z q f) :
    ∃ m₀ r₀, ∃ row : Tg_raw_archive_row_d M.Domain,
      M.mem m₀ k ∧ Rd_entry_d m₀ (v 22) z ∧ Rd_entry_d m₀ r₀ H ∧
      Rt_tuple_d row.values_d r₀ ∧ row.link_d ⟨o,n,Q,G,Λ⟩ ∧
    ∃ vs₀ : Fin 54 → M.Domain, Tg_saved_code_d row.X row.R row.w row.U row.q vs₀ ∧
    ∃ L₁ θ T₁ Q₁ G₁ E₁ Λ₁ d P S j₁ q₁ p₁,
      Rd_entry_d χ L₁ R ∧ It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n row.i T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m d Q₁ ∧ It_map_d G₁ row.i m j₁ ∧ Rd_entry_d n p₁ E₁ ∧ It_map_d G₁ o m q₁ ∧
      M.IsSetFunction I Λ₁ ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ Rd_entry_d i μ Λ ∨ i = n ∧ μ = L₁) ∧
    ∃ _ : Smdl_d I d P S, Zc_model_d I ω d P S ∧ Smap_d I ω row.c d row.X P j₁ ∧
      Smap_d I ω c₀ d X₀ P q₁ ∧ It_comp_d row.p j₁ q₁ ∧
    ∃ wp ηp Cp L₂ W₂ r₂, Tg_saved_d I wp P S ηp Cp L₂ W₂ r₂ ∧
    ∃ vs us : Fin 54 → M.Domain, Tg_saved_code_d P S wp W₂ r₂ vs ∧
      (∀ i, Rd_entry_d (vs₀ i) (us i) j₁) ∧
      Tg_restart_link_d I P S (fun i => us ([19,22,40,41,42].get i)) vs ∧
      Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ P S wp Cp W₂ r₂ q₁ ∧
      Tg_raw_cofinal_d I wp P S L₂ ∧ Tg_saved_name_d I S₀ P S wp W₂ r₂ q₁ ∧
    ∃ θ₂ T₂ Q₂ G₂ E₂ Λ₂ d₂ Z R₂ j₂ q₂ p₂,
      It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧ It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ d₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      M.IsSetFunction I Λ₂ ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ Rd_entry_d i μ Λ₁ ∨ i = m ∧ μ = L₂) ∧
      (⟨m,d,P,S,wp,ηp,Cp,L₂,W₂,r₂,q₁⟩ : Tg_raw_archive_row_d M.Domain).link_d ⟨o,θ,Q₂,G₂,Λ₂⟩ ∧
      Tg_raw_archive_links_d I ⟨o,θ,Q₂,G₂,Λ₂⟩ H ∧
    ∃ mt : Smdl_d I d₂ Z R₂, Zc_model_d I ω d₂ Z R₂ ∧
      Smap_d I ω c d₂ N Z j₂ ∧ Smap_d I ω c₀ d₂ X₀ Z q₂ ∧ It_comp_d q j₂ q₂ ∧
      (Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂) ∧
    ∃ l Vc Γc gc, Ic_common_d I P S Z R₂ L₂ l W₂ Vc Γc gc ∧ Tg_root_square_d D₀ q₁ q₂ gc ∧
    ∃ w₂ η₂ C₂ z₂, Rd_entry_d w w₂ j₂ ∧ Rd_entry_d η η₂ j₂ ∧ Rd_entry_d C C₂ j₂ ∧
      Rr_layer_d I ω Z R₂ w₂ z₂ ∧
    ∃ current : Tg_context_d I w₂ Z R₂ η₂ C₂,
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := R₂) mt.2.1).Domain //
      (smdl_structure_l I (R := R₂) mt.2.1).mem x ⟨C₂,current.member⟩},
    ∃ ι₂ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) mt.2.1) ⟨C₂,current.member⟩ nd) 46,
      (∀ i, Rd_entry_d (v i) (ι₂.bound i).val.val j₂) ∧ Formula.satisfies ι₂ tg_issued0_m ∧
      (ι₂.bound 0).val.val = w₂ ∧
      Tg_round_index_d I ω z₂ mt.2.1 ⟨w₂,current.omega_mem⟩ (ι₂.bound 19).val k ∧
      Rd_entry_d S₀ (ι₂.bound 7).val.val q₂ ∧ Rd_entry_d A₀ (ι₂.bound 6).val.val q₂ ∧
      (∀ x, Rd_entry_d x l R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧ Rd_entry_d l C₂ R₂ ∧
      Tg_prefix_d I k A Z R₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 3).val.val (ι₂.bound 20).val.val z₂ q₂ f ∧
      Tg_raw_archive_views_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ q₂ H Z R₂ l w₂ C₂ (ι₂.bound 4).val.val
        (ι₂.bound 1).val.val (ι₂.bound 2).val.val (ι₂.bound 3).val.val z₂ (ι₂.bound 20).val.val ∧
    ∃ γ₂ Vγ₂ tγ₂, Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ Z R₂ C₂ q₂ γ₂ Vγ₂ tγ₂ ∧
      Rd_entry_d w₂ Vγ₂ R₂ ∧ (∀ x, Rd_entry_d x γ₂ R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧
    ∃ B fA, (∀ y, M.mem y B ↔ M.mem y Z ∧ Rd_entry_d y (ι₂.bound 6).val.val R₂) ∧
      M.IsSetBijectionFromTo I fA A B ∧ M.IsRestrictionOf I fA q₂ A ∧
    ∃ τ u Aq Uq Dq rq mq bq hq qq : (rt_model_l
      (M := smdl_structure_l I (R := R₂) mt.2.1) ⟨C₂,current.member⟩ nd).Domain,
      Rd_entry_d τ.val.val (ι₂.bound 5).val.val R₂ ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,τ,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) mt.2.1)
          ⟨C₂,current.member⟩ nd) 5) tg_query_request0_m ∧
      Tg_query_data_d (ι₂.bound 11) τ (ι₂.bound 26) (ι₂.bound 1) (ι₂.bound 1) Aq Uq Dq rq mq bq hq qq ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,ι₂.bound 27,ι₂.bound 28,ι₂.bound 24,τ,
        ι₂.bound 30,ι₂.bound 31,Dq,ι₂.bound 25,u,ι₂.bound 36,ι₂.bound 37,rq,bq,hq,
        ι₂.bound 38,ι₂.bound 39,ι₂.bound 40,ι₂.bound 41,ι₂.bound 42,ι₂.bound 43,ι₂.bound 44].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) mt.2.1)
          ⟨C₂,current.member⟩ nd) 22) tg_reply0_m ∧
      Rd_entry_d (vs 41) (ι₂.bound 23).val.val gc ∧ Rd_entry_d (vs 15) τ.val.val gc ∧
      Rd_entry_d (vs 11) u.val.val gc ∧
      (∃ a, Rd_entry_d (vs 40) a gc ∧ Tg_play_d I Z R₂ C₂ (ι₂.bound 4).val.val
        (ι₂.bound 3).val.val (ι₂.bound 20).val.val a) ∧
      Tg_raw_answer_result_d I mt.2.1 ⟨C₂,current.member⟩ nd w₂ η₂ ω z₂ k l
        X₀ R₀ γ₀ D₀ C₀ A₀ S₀ q₂ H gc ⟨m,d,P,S,wp,ηp,Cp,L₂,W₂,r₂,q₁⟩
        ⟨o,θ,Q₂,G₂,Λ₂⟩ ι₂ τ u := by
  let right := tree.diagram.elementary o n q c₀ X₀ R₀ c N R request.origin qr qn root.model mn
  have sourceZc := root.map_l hZF tree.omega mn right
  have ground := sourceZc.native_l I hZF tree.omega
  have hN := ZF.modelsKP (ZFC.models_zf_l ground)
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let Cn : Nn.Domain := ⟨C,request.context.member⟩
  obtain ⟨m₀,r₀,row,hm₀,index₀,stored,tuple,rowLink₀,mx,saved₀,name₀,vs₀,code₀,source⟩ :=
    request.first_l hZFC root cut tree hm qn mn qr lf levels ne
  -- 先固定原环境，再分别消去树、模型与反射环境，避免生成巨大的依赖消去式。
  refine source.elim fun nc h => h.elim fun ι h => h.elim fun ν h => ?_
  obtain ⟨eq,issued,seed,result,arity,boundEq,newEq,s,t,a,oldPlay,oldGraph,oldSize,oldLabels,b,is,it,
    γ,Vγ,tγ,slice,omegaSlice,lower,L,U,rankU,small,cofinal,highχ,highτ,rest⟩ := h
  obtain ⟨θ,T₁,Q₁,G₁,E₁,Λ₁,d,P,S,j₁,q₁,p₁,tree₁,extension₁,node₁,edge₁,move₁,root₁,
    lf₁,levels₁,entries₁,owner⟩ := rest
  refine owner.elim fun mp h => ?_
  obtain ⟨certificateP,embed₁,rootMapP,rootCompP,critical₁,l₁,V₁,Γ₁,g₁,first,roots₁,
    Bp,ts,ft₁,restrict₁,endpoint₁,layer₁,Pκ,rankκ,lowSquare₁,targetData⟩ := h
  obtain ⟨wp,ηp,Cp,Lp,Up,rp,zp,iwp,iηp,iCp,numbersP,pointω,restored⟩ := targetData
  refine restored.elim fun savedP h => h.elim fun nd h => h.elim fun ρ h => h.elim fun σ h => ?_
  obtain ⟨codeP,roundP,oldPoints,oldTree,subtype,prior₁,program,points₅,programPoints,bound₁,insideP,
    γp,Vγp,tγp,iγ,iVγ,sliceP,omegaP,candidates⟩ := h
  refine candidates.elim fun ψ h => h.elim fun ε h => h.elim fun ζ h => ?_
  obtain ⟨queries,coords,queryPlay,
    lowShort,lowLabels,candidate,targetQueries,candidatePoints,queryPoints,candidateω,queryω,
    finiteTarget,nodeQuery,maxQuery,scopeQuery,emptyQuery,targetLower⟩ := h
  refine ⟨m₀,r₀,row,hm₀,index₀,stored,tuple,rowLink₀,vs₀,code₀,
    L.val,θ,T₁,Q₁,G₁,E₁,Λ₁,d,P,S,j₁,q₁,p₁,highχ,tree₁,extension₁,node₁,edge₁,move₁,root₁,
    lf₁,levels₁,entries₁,mp,certificateP,embed₁,rootMapP,rootCompP,?_⟩
  let Pn := smdl_structure_l I (R := S) mp.2.1
  have groundP := certificateP.native_l I hZF tree.omega
  have ownerZF := ZFC.models_zf_l groundP
  have hP := ZF.modelsKP ownerZF
  have fp := savedP.context.finite_l mp.2.1 hP.1
  have hwι : (ι.bound 0).val.val = w := (eq 0).trans request.omega
  obtain ⟨W,νr,εr,eqr,recovered,labelDomain,πp,eqp,v₂,a₂,renewal⟩ :=
    first.continue_renewal_l hZFC tree.omega root mn mp right rootMapP request.numbers numbersP
      request.context savedP.context cofinal small ft₁ restrict₁ nc nd ι ψ ρ σ ε ζ issued roundP
      subtype program prior₁ candidate targetQueries coords candidatePoints queryPoints candidateω queryω
      finiteTarget nodeQuery maxQuery scopeQuery emptyQuery points₅ programPoints highτ bound₁
      sliceP omegaP targetLower oldTree
  let ρ₂ := tg_round_env_d (tg_restart_env_d ρ ε εr πp v₂) a₂
  obtain ⟨seed₂,round₂,hw₂,request₂,point,shortPoint,lower₂,L₂,W₂,r₂,saved₂,code₂,above₂,base₂,
    cofinal₂,name₂,X,K,R',F,c',d',Y,RY,j,κ',A',D',u',image,α,β,hα,hβ,hκ,limitα,rankβ,
    B,kback,carrierBack,injectionBack,imageBack,predBack,inverse,returned⟩ := renewal
  -- 恢复几何也取同一次 εr；旧图与新保存轮没有另选一个代表。
  have rankγ := (rr_rank_native_l I mn.2.1 hN ⟨γ,slice.rank.1⟩ ⟨Vγ,slice.rank.2.1⟩).mp slice.rank
  have oldPlay' : Tg_play_d I N R C (ι.bound 4).val.val (ι.bound 3).val.val
      (ι.bound 20).val.val s.val.val := by
    rw [eq 4,eq 3,eq 20]
    exact oldPlay
  have oldImages : ∀ i : Fin 2, ∃ x, Rd_entry_d ([s,t].get i).val.val x b ∧
      Rd_entry_d x (ρ.bound ([40,41].get i)).val.val j₁ :=
    Fin.cases ⟨vs₀ 40,is,oldPoints 40⟩ (Fin.cases ⟨vs₀ 41,it,oldPoints 41⟩ (fun i => Fin.elim0 i))
  obtain ⟨_,_,restart⟩ := first.raw_restart_link_l hZF mn mp hN hP request.context savedP.context
    nc nd ι ψ ρ ε ζ πp εr v₂ a₂ s t a issued roundP recovered oldPlay' queryPlay oldGraph oldSize oldLabels
    coords queryPoints labelDomain (eqr 8) (eqr 9) (eqr 2) (eqr 19)
    ⟨γ,slice.rank.1⟩ ⟨Vγ,slice.rank.2.1⟩ (ν.bound 1).val Pκ rankγ rankκ
    (fun x hx => lower x.val hx) lowShort lowLabels oldImages lowSquare₁
  refine ⟨wp,ηp,Cp,L₂.val,W₂.val,r₂,saved₂,(fun i => (ρ₂.bound i).val.val),(fun i => (ρ.bound i).val.val),
    code₂,oldPoints,restart,base₂,cofinal₂,name₂,?_⟩
  -- 同一第二 cert 只解包一次，完整回答与目标请求也各生产一次。
  obtain ⟨Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,d₂,Z,R₂,j₂,q₂,p₂,cert₂⟩ := returned
  obtain ⟨mt,certificateZ,embed₂,rootMapZ,rootGraph,payload₂,active₂,extend₂,
    l,Vc,Γc,gc,second,readW,smallW,Kκ,rankKκ,lowSquare₂,B₃,D₃,t₃,transB₃,carrier₃,ft₃,
    restrict₃,endpoint₃,layer₃,pred₃,ε₃,transport⟩ := image.return_reply_l hZF tree.omega root mp ownerZF
      savedP.context nd ρ₂ round₂ hw₂ (fun i => (ι.bound i).val.val) request₂ first ft₁ restrict₁ inverse
      α β L₂ W₂ X K R' F c' d' Y RY j κ' A' D' u' hα hβ hκ limitα rankβ above₂ cert₂
  have used := image
  obtain ⟨_,_,_,κL,τL,rankW,hQW,_,_,_,_,_,_,_,_,_,_,_,_,_,replyData⟩ := used
  have huW : Pn.mem (ρ₂.bound 11).val W₂ := v_subset_mem_l (kp_pair_l hP) rankW hQW replyData.1
  exact transport.continue_finish_l hZF request root cut tree hm qn mn qr prior
    tree₁ extension₁ node₁ root₁ lf₁ levels₁ (fun i μ hi => (entries₁ i μ).mpr (Or.inl hi)) critical₁
    mp hN ownerZF L₂ W₂ κ' A' D' u' B₃ saved₂ numbersP rootMapP nc nd ι ρ₂ eq issued round₂ hw₂
    code₂ base₂ cofinal₂ name₂ first roots₁ inverse point highτ slice sliceP iVγ omegaP lower₂
    (ψ.bound 5).val queryPlay lowShort shortPoint mt certificateZ embed₂ rootMapZ rootGraph payload₂ extend₂
    second Kκ rankKκ lowSquare₂ κL τL hQW huW transB₃ carrier₃ ft₃ restrict₃ endpoint₃ layer₃ pred₃ ε₃

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 一般原游戏的完整继续后继

非空请求实际选取旧档案，经过两条原树边和同一次重启后接受外部落子。
旧保存码、原边像及三图延伸方程一并返回；十一项档案精确追加，
原前缀延长一个字母，目标原历史严格增长。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_request_d.continue_l
    {ω S₀ X₀ R₀ w₀ γ₀ B₀ D₀ C₀ A₀ A N R w η C χ z k H r q c₀ n m T Q G E Λ c o f x : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k H r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qn : Rd_entry_d n c Q) (mn : Smdl_d I c N R) (qr : Rd_entry_d o c₀ Q)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i μ, Rd_entry_d i μ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ μ F)
    (ne : v 23 ≠ v 1)
    (prior : Tg_prefix_d I k A N R C (v 4) (v 3) (v 20) z q f) (input : M.mem x A) :
    ∃ m₀ r₀, ∃ row : Tg_raw_archive_row_d M.Domain,
      M.mem m₀ k ∧ Rd_entry_d m₀ (v 22) z ∧ Rd_entry_d m₀ r₀ H ∧
      Rt_tuple_d row.values_d r₀ ∧ row.link_d ⟨o,n,Q,G,Λ⟩ ∧
    ∃ vs₀ : Fin 54 → M.Domain, Tg_saved_code_d row.X row.R row.w row.U row.q vs₀ ∧
    ∃ L₁ θ T₁ Q₁ G₁ E₁ Λ₁ d P S j₁ q₁ p₁,
      Rd_entry_d χ L₁ R ∧ It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n row.i T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m d Q₁ ∧ It_map_d G₁ row.i m j₁ ∧ Rd_entry_d n p₁ E₁ ∧ It_map_d G₁ o m q₁ ∧
      M.IsSetFunction I Λ₁ ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ Rd_entry_d i μ Λ ∨ i = n ∧ μ = L₁) ∧
      Zc_model_d I ω d P S ∧ Smap_d I ω row.c d row.X P j₁ ∧
      Smap_d I ω c₀ d X₀ P q₁ ∧ It_comp_d row.p j₁ q₁ ∧
    ∃ wp ηp Cp L₂ W₂ r₂, Tg_saved_d I wp P S ηp Cp L₂ W₂ r₂ ∧
    ∃ vs us : Fin 54 → M.Domain, Tg_saved_code_d P S wp W₂ r₂ vs ∧
      (∀ i, Rd_entry_d (vs₀ i) (us i) j₁) ∧
      Tg_restart_link_d I P S (fun i => us ([19,22,40,41,42].get i)) vs ∧
      Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ P S wp Cp W₂ r₂ q₁ ∧
      Tg_raw_cofinal_d I wp P S L₂ ∧ Tg_saved_name_d I S₀ P S wp W₂ r₂ q₁ ∧
    ∃ θ₂ T₂ Q₂ G₂ E₂ Λ₂ d₂ Z R₂ j₂ q₂ p₂,
      It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧ It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ d₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      M.IsSetFunction I Λ₂ ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ Rd_entry_d i μ Λ₁ ∨ i = m ∧ μ = L₂) ∧
      (⟨m,d,P,S,wp,ηp,Cp,L₂,W₂,r₂,q₁⟩ : Tg_raw_archive_row_d M.Domain).link_d ⟨o,θ,Q₂,G₂,Λ₂⟩ ∧
      Zc_model_d I ω d₂ Z R₂ ∧ Smap_d I ω c d₂ N Z j₂ ∧
      Smap_d I ω c₀ d₂ X₀ Z q₂ ∧ It_comp_d q j₂ q₂ ∧
      (Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂) ∧
    ∃ w₂ η₂ C₂ z₂ l k' H' r' rr y f', ∃ b : Fin 46 → M.Domain,
      M.SuccessorOf k' k ∧ M.mem y A ∧ (Gm_even_d I ω k → y = x) ∧
      Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ Z R₂ w₂ η₂ C₂ l z₂ k' H' r' q₂
        ⟨o,θ,Q₂,G₂,Λ₂⟩ b ∧
      (∀ i : Fin 19, Rd_entry_d (v (i.castAdd 27)) (b (i.castAdd 27)) j₂) ∧
      (∃ h, Rd_entry_d (v 20) h j₂ ∧ h ≠ b 20 ∧
        ∀ a, Rd_entry_d a h R₂ → Rd_entry_d a (b 20) R₂) ∧
      Rt_tuple_d (⟨m,d,P,S,wp,ηp,Cp,L₂,W₂,r₂,q₁⟩ : Tg_raw_archive_row_d M.Domain).values_d rr ∧
      (∀ i a, M.PairMember I i a H' ↔ M.PairMember I i a H ∨ i = k ∧ a = rr) ∧
      Tg_prefix_d I k' A Z R₂ C₂ (b 4) (b 3) (b 20) z₂ q₂ f' ∧ Fseq_end_d I ω f' f y := by
  obtain ⟨m₀,r₀,row,hm₀,index₀,stored,tuple₀,link₀,vs₀,code₀,rest⟩ :=
    request.continue_checked_l hZFC root cut tree hm qn mn qr lf levels ne prior
  obtain ⟨L₁,θ,T₁,Q₁,G₁,E₁,Λ₁,d,P,S,j₁,q₁,p₁,high₁,mid,first,node₁,edge₁,move₁,root₁,
    function₁,levels₁,entries₁,_,certificate₁,embed₁,rootMap₁,composition₁,rest⟩ := rest
  obtain ⟨wp,ηp,Cp,L₂,W₂,r₂,saved,vs,us,code,oldPoints,restart,base,cofinal,name,rest⟩ := rest
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,Λ₂,d₂,Z,R₂,j₂,q₂,p₂,next,second,node₂,edge₂,move₂,root₂,
    function₂,levels₂,entries₂,rowLink,_,target,certificate₂,embed₂,rootMap₂,composition₂,critical,
    l,Vc,Γc,gc,_,_,rest⟩ := rest
  obtain ⟨w₂,η₂,C₂,z₂,_,_,_,_,current,nd,ι₂,points,_,hw,index,_,_,_,_,play,_,rest⟩ := rest
  obtain ⟨γ₂,Vγ₂,tγ₂,_,_,_,B,fA,carrier,letters,restriction,τ,u,Aq,Uq,Dq,rq,mq,bq,hq,qq,
    _,_,_,_,_,_,_,_,answered⟩ := rest
  have native := ZFC.models_zf_l (certificate₂.native_l I hZF tree.omega)
  obtain ⟨k',H',r',rr,y,f',ε,successor,hy,even,head,request',tuple,append,play',endt,keep,proper⟩ :=
    answered.input_l hZF current target.2.1 native nd ι₂ τ u
      ⟨m,d,P,S,wp,ηp,Cp,L₂,W₂,r₂,q₁⟩ ⟨o,θ,Q₂,G₂,Λ₂⟩ index hw rootMap₂.1.2
      carrier letters restriction play input
  refine ⟨m₀,r₀,row,hm₀,index₀,stored,tuple₀,link₀,vs₀,code₀,
    L₁,θ,T₁,Q₁,G₁,E₁,Λ₁,d,P,S,j₁,q₁,p₁,high₁,mid,first,node₁,edge₁,move₁,root₁,
    function₁,levels₁,entries₁,certificate₁,embed₁,rootMap₁,composition₁,?_⟩
  refine ⟨wp,ηp,Cp,L₂,W₂,r₂,saved,vs,us,code,oldPoints,restart,base,cofinal,name,?_⟩
  refine ⟨θ₂,T₂,Q₂,G₂,E₂,Λ₂,d₂,Z,R₂,j₂,q₂,p₂,next,second,node₂,edge₂,move₂,root₂,
    function₂,levels₂,entries₂,rowLink,certificate₂,embed₂,rootMap₂,composition₂,critical,?_⟩
  refine ⟨w₂,η₂,C₂,z₂,l,k',H',r',rr,y,f',(fun i => (ε.bound i).val.val),successor,hy,even,
    request',?_,?_,tuple,append,play',endt⟩
  · intro i
    exact Eq.mpr (congrArg (fun a => Rd_entry_d (v (i.castAdd 27)) a j₂)
      (congrArg (fun a => a.val.val) (head i))) (points (i.castAdd 27))
  · exact ⟨(ι₂.bound 20).val.val,points 20,fun eq => proper (Subtype.ext eq),
      fun a ha => keep ⟨a,(target.2.2.2 a (ι₂.bound 20).val.val ha).1⟩ ha⟩

end YesMetaZFC.SetTheory.LargeCardinal
