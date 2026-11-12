import YesMetaZFC.SetTheory.LargeCardinal.Game.RawResetChecked
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawInput
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawPrepare
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueCandidate
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 一般原游戏的完整重置后继

一次重置的两条原树边、原回答、外部落子和下一请求在这里合并。
同一次核验所选的字母图与回答位置直接接受原输入；旧原前缀精确追加，
十一项新档案保留该次原奇数行及重置的零长度几何。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_request_d.reset_l
    {ω S₀ X₀ R₀ w₀ γ₀ B₀ D₀ C₀ A₀ A N R w η C χ z k D r q c₀ n m T Q G E Λ d o f x : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k D r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qn : Rd_entry_d n d Q) (mn : Smdl_d I d N R) (qr : Rd_entry_d o c₀ Q)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i μ, Rd_entry_d i μ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ μ F)
    (empty : v 23 = v 1)
    (prior : Tg_prefix_d I k A N R C (v 4) (v 3) (v 20) z q f) (input : M.mem x A) :
    ∃ L W r₁, Tg_saved_d I w N R η C L W r₁ ∧
    ∃ vs : Fin 54 → M.Domain, Tg_saved_code_d N R w W r₁ vs ∧
      vs 17 = v 1 ∧ vs 19 = v 7 ∧
      vs 22 = v 1 ∧ vs 40 = v 1 ∧ vs 41 = v 1 ∧ vs 42 = v 1 ∧ Rd_entry_d χ L R ∧
    ∃ θ T₁ Q₁ G₁ E₁ jp q₁, M.SuccessorOf θ m ∧ It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁ ∧ Rd_entry_d m d Q₁ ∧
      It_map_d G₁ n m jp ∧ (∀ a b, Rd_entry_d a b jp → a = b) ∧ It_map_d G₁ o m q₁ ∧
      (∀ a b, Rd_entry_d a b q₁ ↔ Rd_entry_d a b q) ∧ Tg_saved_name_d I S₀ N R w W r₁ q₁ ∧
    ∃ θ₂ T₂ Q₂ G₂ E₂ d₂ P R₂ j₂ q₂ p₂ Λ₂,
      It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧ It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ d₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      M.IsSetFunction I Λ₂ ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ Rd_entry_d i μ Λ ∨ i = m ∧ μ = L) ∧
      (⟨m,d,N,R,w,η,C,L,W,r₁,q₁⟩ : Tg_raw_archive_row_d M.Domain).link_d ⟨o,θ,Q₂,G₂,Λ₂⟩ ∧
      Zc_model_d I ω d₂ P R₂ ∧ Smap_d I ω d d₂ N P j₂ ∧
      Smap_d I ω c₀ d₂ X₀ P q₂ ∧ It_comp_d q j₂ q₂ ∧
      (Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂) ∧
    ∃ w₂ η₂ C₂ z₂ l k' D' r' rr y f', ∃ b : Fin 46 → M.Domain,
      M.SuccessorOf k' k ∧ M.mem y A ∧ (Gm_even_d I ω k → y = x) ∧
      Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ P R₂ w₂ η₂ C₂ l z₂ k' D' r' q₂
        ⟨o,θ,Q₂,G₂,Λ₂⟩ b ∧
      (∀ i : Fin 19, Rd_entry_d (v (i.castAdd 27)) (b (i.castAdd 27)) j₂) ∧
      (∃ h, Rd_entry_d (v 20) h j₂ ∧ h ≠ b 20 ∧
        ∀ a, Rd_entry_d a h R₂ → Rd_entry_d a (b 20) R₂) ∧
      Rt_tuple_d (⟨m,d,N,R,w,η,C,L,W,r₁,q₁⟩ : Tg_raw_archive_row_d M.Domain).values_d rr ∧
      (∀ i a, M.PairMember I i a D' ↔ M.PairMember I i a D ∨ i = k ∧ a = rr) ∧
      Tg_prefix_d I k' A P R₂ C₂ (b 4) (b 3) (b 20) z₂ q₂ f' ∧ Fseq_end_d I ω f' f y := by
  obtain ⟨L,W,r₁,saved,vs,code,emptyCoord,treeCoord,lengthZero,shortZero,labelZero,graphZero,above,
    θ,T₁,Q₁,G₁,E₁,jp,q₁,succ,mid,first,node,pad,identity,root₁,same,name,rest⟩ :=
    request.reset_checked_l hZFC root cut tree hm qn mn qr lf levels empty prior
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,d₂,P,R₂,j₂,q₂,p₂,Λ₂,next,second,node₂,edge₂,move₂,root₂,
    function,levels₂,entries,rowLink,_,target,certificate,embed,rootMap,composition,critical,
    l,Vc,Dc,t,_,_,rest⟩ := rest
  obtain ⟨w₂,η₂,C₂,z₂,_,_,_,_,current,nd,ι₂,points,_,hw,index,_,_,_,_,play,_,
    γ₂,Vγ₂,tγ₂,_,_,_,B,fA,carrier,letters,restriction,τ,u,Aq,Uq,Dq,rq,mq,bq,hq,qq,
    _,_,_,_,_,_,_,_,answered⟩ := rest
  have native := ZFC.models_zf_l (certificate.native_l I hZF tree.omega)
  obtain ⟨k',D',r',rr,y,f',ε,successor,hy,even,head,request',tuple,append,play',endt,keep,proper⟩ :=
    answered.input_l hZF current target.2.1 native nd ι₂ τ u
      ⟨m,d,N,R,w,η,C,L,W,r₁,q₁⟩ ⟨o,θ,Q₂,G₂,Λ₂⟩ index hw rootMap.1.2
      carrier letters restriction play input
  refine ⟨L,W,r₁,saved,vs,code,emptyCoord,treeCoord,lengthZero,shortZero,labelZero,graphZero,above,
    θ,T₁,Q₁,G₁,E₁,jp,q₁,succ,mid,first,node,pad,identity,root₁,same,name,
    θ₂,T₂,Q₂,G₂,E₂,d₂,P,R₂,j₂,q₂,p₂,Λ₂,next,second,node₂,edge₂,move₂,root₂,
    function,levels₂,entries,rowLink,certificate,embed,rootMap,composition,critical,
    w₂,η₂,C₂,z₂,l,k',D',r',rr,y,f',(fun i => (ε.bound i).val.val),successor,hy,even,
    request',?_,?_,tuple,append,play',endt⟩
  · intro i
    exact Eq.mpr (congrArg (fun a => Rd_entry_d (v (i.castAdd 27)) a j₂)
      (congrArg (fun a => a.val.val) (head i))) (points (i.castAdd 27))
  · exact ⟨(ι₂.bound 20).val.val,points 20,fun eq => proper (Subtype.ext eq),
      fun a ha => keep ⟨a,(target.2.2.2 a (ι₂.bound 20).val.val ha).1⟩ ha⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 非空请求的第一个实际原后继

准备结果的 raw 与 subtype 只解包一次。根切片沿固定工厂推进，subtype
已选代表池在这同一目标上保留；原生控制界给出共同层属于恢复反射层，
随即搬运真实候选与原查询。完整旧轮、程序和短图留给下一次更新核。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_raw_request_d.first_l
    {ω S₀ Xᵣ Rᵣ wr γ₀ B₀ D₀ C₀ A₀ A N R w η C χ z k H r q c₀ n m T Q G E Λ c o : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I ω S₀ Xᵣ Rᵣ γ₀ D₀ C₀ A₀ N R w η C χ z k H r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d I ω c₀ Xᵣ Rᵣ)
    (cut : Tg_root_cut_d I c₀ Xᵣ Rᵣ wr γ₀ B₀ A₀ D₀ A)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qn : Rd_entry_d n c Q) (mn : Smdl_d I c N R) (qr : Rd_entry_d o c₀ Q)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i L, Rd_entry_d i L Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ L F)
    (ne : v 23 ≠ v 1) :
    let right := tree.diagram.elementary o n q c₀ Xᵣ Rᵣ c N R request.origin qr qn root.model mn
    let ground := (root.map_l hZF tree.omega mn right).native_l I hZF tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    let Nn := smdl_structure_l I (R := R) mn.2.1
    let Cn : Nn.Domain := ⟨C,request.context.member⟩
    ∃ m₀ r₀, ∃ row : Tg_raw_archive_row_d M.Domain,
      M.mem m₀ k ∧ Rd_entry_d m₀ (v 22) z ∧ Rd_entry_d m₀ r₀ H ∧
      Rt_tuple_d row.values_d r₀ ∧ row.link_d ⟨o,n,Q,G,Λ⟩ ∧
    ∃ _ : Smdl_d I row.c row.X row.R,
      Tg_saved_d I row.w row.X row.R row.η row.C row.L row.U row.q ∧
      Tg_saved_name_d I S₀ row.X row.R row.w row.U row.q row.p ∧
    ∃ vs : Fin 54 → M.Domain, Tg_saved_code_d row.X row.R row.w row.U row.q vs ∧
    ∃ nc : Nonempty {x : Nn.Domain // Nn.mem x Cn},
    ∃ ι : Env (rt_model_l Cn nc) 46, ∃ ν : Env (rt_model_l Cn nc) 29,
      (∀ i, (ι.bound i).val.val = v i) ∧ Formula.satisfies ι tg_issued0_m ∧
      Formula.satisfies ν tc_seed0_m ∧ Formula.satisfies ν tc_result0_m ∧
      ν.bound 3 = ι.bound 27 ∧ (ν.bound 28).val.val = χ ∧
      (∀ i : Fin 14, ν.bound ([0,2,8,9,13,14,16,21,22,23,24,25,26,27].get i) =
        ι.bound ([0,5,24,28,25,36,37,38,39,40,41,42,43,44].get i)) ∧
    ∃ s t a : (rt_model_l Cn nc).Domain,
      Tg_play_d I N R C (v 4) (v 3) (v 20) s.val.val ∧ Tg_graph_d (kp_pair_l hN) a.val s.val ∧
      Nn.MemberSubset a.val (ι.bound 26).val ∧ Nn.MemberSubset t.val (ι.bound 23).val ∧
    ∃ b, Rd_entry_d s.val.val (vs 40) b ∧ Rd_entry_d t.val.val (vs 41) b ∧
    ∃ γ Vγ tγ, Tg_root_slice_d I Xᵣ Rᵣ γ₀ D₀ C₀ N R C q γ Vγ tγ ∧ Rd_entry_d w Vγ R ∧
      (∀ x, Rd_entry_d x γ R → Rd_entry_d x (ν.bound 1).val.val R) ∧
    ∃ L U : Nn.Domain, V_d (kp_pair_l hN) L U ∧ Rr_small_d I N R U.val ∧
      Tg_raw_cofinal_d I w N R L.val ∧ Rd_entry_d χ L.val R ∧ Rd_entry_d (ι.bound 24).val.val L.val R ∧
    ∃ θ T₁ Q₁ G₁ E₁ Λ₁ d P S j q' p,
      It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧ It_extension_d m n row.i T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m d Q₁ ∧ It_map_d G₁ row.i m j ∧ Rd_entry_d n p E₁ ∧ It_map_d G₁ o m q' ∧
      M.IsSetFunction I Λ₁ ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ Rd_entry_d i μ Λ ∨ i = n ∧ μ = L.val) ∧
    ∃ mp : Smdl_d I d P S, Zc_model_d I ω d P S ∧ Smap_d I ω row.c d row.X P j ∧
      Smap_d I ω c₀ d Xᵣ P q' ∧ It_comp_d row.p j q' ∧
      (Tg_raw_critical_d I Xᵣ Rᵣ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I Xᵣ Rᵣ γ₀ D₀ C₀ o Q₁ G₁ E₁) ∧
    ∃ l V Γ g, Ic_common_d I N R P S L.val l U.val V Γ g ∧ Tg_root_square_d D₀ q q' g ∧
    ∃ Bp ts, M.IsSetInjectionFromTo I ts Bp P ∧ M.IsRestrictionOf I g ts Γ ∧
      Rd_entry_d L.val l ts ∧ Rd_entry_d U.val V ts ∧
    ∃ Pκ : Nn.Domain, V_d (kp_pair_l hN) (ν.bound 1).val Pκ ∧
      (∀ x : Nn.Domain, ∀ y Z, Nn.mem x Pκ → Rd_entry_d x.val y b →
        (Rd_entry_d x.val Z g ↔ Rd_entry_d y Z j)) ∧
    ∃ w' η' C' L' U' r' z', Rd_entry_d row.w w' j ∧ Rd_entry_d row.η η' j ∧ Rd_entry_d row.C C' j ∧
      Rr_layer_d I ω P S w' z' ∧ Rd_entry_d w w' g ∧
    ∃ saved' : Tg_saved_d I w' P S η' C' L' U' r',
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := S) mp.2.1).Domain //
      (smdl_structure_l I (R := S) mp.2.1).mem x ⟨C',saved'.context.member⟩},
    ∃ ρ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C',saved'.context.member⟩ nd) 54,
    ∃ σ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C',saved'.context.member⟩ nd) 17,
      Tg_saved_code_d P S w' U' r' (fun i => (ρ.bound i).val.val) ∧ Formula.satisfies ρ tg_round0_m ∧
      (∀ i, Rd_entry_d (vs i) (ρ.bound i).val.val j) ∧ Rd_entry_d S₀ (ρ.bound 19).val.val q' ∧
      Formula.satisfies σ tg_subtype0_m ∧
      (∀ i : Fin 5, σ.bound ([0,1,2,5,9].get i) = ρ.bound ([16,24,15,13,11].get i)) ∧
      Formula.satisfies (σ.reindex (fun i : Fin 11 => [0,1,7,8,10,11,12,13,14,15,16].get i)) ts_numeric0_m ∧
      (∀ i : Fin 5, Rd_entry_d (ι.bound ([0,24,28,25,27].get i)).val.val
        (σ.bound ([0,3,4,6,1].get i)).val.val ts) ∧
      (∀ i : Fin 9, Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
        (σ.bound ([7,8,10,11,12,13,14,15,16].get i)).val.val ts) ∧
      (∀ x, Rd_entry_d x l S → Rd_entry_d x (ρ.bound 15).val.val S) ∧
      Rd_entry_d V C' S ∧
    ∃ γ' Vγ' tγ', Rd_entry_d γ γ' g ∧ Rd_entry_d Vγ Vγ' g ∧
      Tg_root_slice_d I Xᵣ Rᵣ γ₀ D₀ C₀ P S C' q' γ' Vγ' tγ' ∧
      Rd_entry_d w' Vγ' S ∧
    ∃ ψ : Env (rt_model_l Cn nc) 12,
    ∃ ε ζ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C',saved'.context.member⟩ nd) 12,
      Formula.satisfies ψ tg_query_row0_m ∧
      (∀ i : Fin 6, ψ.bound ([0,1,2,3,4,6].get i) = ι.bound ([0,1,27,28,26,23].get i)) ∧
      Tg_play_d I N R C (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val (ψ.bound 5).val.val ∧
      Rd_entry_d (ψ.bound 5).val.val Vγ R ∧ Rd_entry_d (ψ.bound 6).val.val Vγ R ∧
      Formula.satisfies ε tg_candidate0_m ∧ Formula.satisfies ζ tg_query_row0_m ∧
      (∀ i : Fin 12, Rd_entry_d (ι.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i)).val.val
        (ε.bound i).val.val g) ∧ (∀ i, Rd_entry_d (ψ.bound i).val.val (ζ.bound i).val.val g) ∧
      (ε.bound 2).val.val = w' ∧ (ζ.bound 0).val.val = w' ∧ Rd_entry_d (ε.bound 1).val.val w' S ∧
      Rd_entry_d (ζ.bound 11).val.val (ε.bound 0).val.val S ∧ Rd_entry_d (ζ.bound 8).val.val (ε.bound 0).val.val S ∧
      (Rd_entry_d (ζ.bound 4).val.val (ε.bound 6).val.val S ∧
        Rd_entry_d (ζ.bound 5).val.val (ε.bound 6).val.val S ∧
        Rd_entry_d (ζ.bound 6).val.val (ε.bound 6).val.val S) ∧
      (∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain,
        ¬ (smdl_structure_l I (R := S) mp.2.1).mem x (ζ.bound 1).val) ∧
      ∀ x, Rd_entry_d x γ' S → Rd_entry_d x (ε.bound 3).val.val S := by
  intro right ground hN Nn Cn
  have native := ZFC.models_zf_l ground
  let wn : Nn.Domain := ⟨w,request.context.omega_mem⟩
  obtain ⟨m₀,r₀,row,hm₀,index,stored,tuple,link,prepared⟩ := request.prepare_l hZFC root tree qn mn qr ne
  obtain ⟨mx,saved,name,baseOld,_,left,zx,_,vs,code,hwold,prepared⟩ := prepared
  obtain ⟨l₀,V₀,Γ₀,gold,oldCommon,oldSquare,_,Δ,b,_,back,_,_,inverse,prepared⟩ := prepared
  refine prepared.elim fun nc prepared => prepared.elim fun ι prepared => ?_
  obtain ⟨eq,issued,prepared⟩ := prepared
  refine prepared.elim fun ν prepared => ?_
  obtain ⟨seed,result,arity,boundEq,newEq,oldLinks,prepared⟩ := prepared
  refine prepared.elim fun ε₀ prepared => ?_
  obtain ⟨reply,replyω,replyN,replyLt,replyMem,replyEmpty,prepared⟩ := prepared
  refine prepared.elim fun s h => h.elim fun t h => h.elim fun a prepared => ?_
  obtain ⟨play,short,size,labels,is,it,γ,Vγ,tγ,slice,omegaSlice,lower,_,β,_,_,_,_,_,_,raw⟩ := prepared
  have hwι : (ι.bound 0).val.val = w := (eq 0).trans request.omega
  have hwν : (ν.bound 0).val = wn := Subtype.ext ((congrArg (fun x => x.val.val) (newEq 0)).trans hwι)
  have links : ∀ i : Fin 4, ν.bound ([0,8,9,13].get i) = ι.bound ([0,24,28,25].get i) :=
    Fin.cases (newEq 0) (Fin.cases (newEq 2) (Fin.cases (newEq 3) (Fin.cases (newEq 4) (fun i => Fin.elim0 i))))
  obtain ⟨γp,Vγp,tp,parentSlice,_,_⟩ := baseOld
  obtain ⟨Xc,Kc,Rc,L,F,cN,dN,Nc,Tc,jN,κc,Uc,Dc,uc,
    rankX,source,hLδ,hκL,hτL,hχL,loc,card,strong,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,subtypec⟩ := raw
  let src : Env Nn 17 := ⟨fun i => [wn,(ν.bound 3).val,κc,(ν.bound 8).val,(ν.bound 9).val,Uc,
    (ν.bound 13).val,(ν.bound 14).val,(ν.bound 16).val,uc,(ν.bound 21).val,(ν.bound 22).val,
    (ν.bound 23).val,(ν.bound 24).val,(ν.bound 25).val,(ν.bound 26).val,(ν.bound 27).val].get i,fun _ => wn⟩
  have stage := subtypec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine stage.elim fun Ls h => h.elim fun Js h => h.elim fun Os h => h.elim fun Zs h =>
    h.elim fun Ds h => h.elim fun ps h => h.elim fun Vs h => h.elim fun Ws h => h.elim fun qs h =>
    h.elim fun d h => h.elim fun P h => h.elim fun S h => h.elim fun j h => h.elim fun q' h =>
    h.elim fun p stage => ?_
  have factory := stage.1
  refine stage.2.elim fun mp₀ h => h.elim fun Ac h => h.elim fun Qc h => h.elim fun Bc h =>
    h.elim fun ec h => h.elim fun Dp h => h.elim fun Γp h => h.elim fun ts stage => ?_
  have collapse := stage.1
  have domain := stage.2.1
  have pool := stage.2.2.2.1
  have present := stage.2.2.2.2.1
  refine stage.2.2.2.2.2.2.2.elim fun native17 stage => ?_
  have nativePoints := stage.1
  refine stage.2.2.elim fun η' h => h.elim fun C' h => h.elim fun L' h => h.elim fun U' h =>
    h.elim fun r' stage => ?_
  have iw := stage.1
  have iη := stage.2.1
  have iC := stage.2.2.1
  refine stage.2.2.2.2.2.2.elim fun saved' h => h.elim fun nd h => h.elim fun ρ h => h.elim fun σ stage => ?_
  have code' := stage.1
  have round := stage.2.1
  have recordPoints := stage.2.2.1
  have reflected := stage.2.2.2.1
  have subtype := stage.2.2.2.2.1
  have prior := stage.2.2.2.2.2.1
  have program := stage.2.2.2.2.2.2
  have omegaOld : Rd_entry_d w row.w b := hwold ▸ oldLinks 0
  have advanced :=
    factory.continue_step_l hZF mx mn hN ⟨V₀,oldCommon.right_rank.2.1⟩ wn (ν.bound 1).val L F β Xc Kc jN
      Ac Qc Bc ec collapse domain pool.1.1.1 present root tree hm link.2.1 qn qr link.2.2.1 request.origin
      lf levels slice omegaSlice lower hκL oldSquare inverse (fun x hx => ((cut.carrier x).mp hx).1)
      omegaOld iw parentSlice.context iC
  refine advanced.elim fun mp advanced => ?_
  obtain ⟨target,embed,rootMap,_,rootComp,_,θ,T₁,Q₁,G₁,E₁,Λ₁,next,extension,node,edge,move,rootEdge,
    lf₁,levels₁,entries,critical,advanced⟩ := advanced
  obtain ⟨U,rankU,readU,small,l,V,Γ,g,common,restrict,endpoint,layer,Bp,fullPool,z',numbers,
    pointω,Pκ,rankK,lowSquare,bκ,κ',pointκ,edgeκ,boundκ,ordκ,γ',Vγ',tγ',iγ,iVγ,_,slice',_,omegaSlice',_,roots⟩ := advanced
  let Pn := smdl_structure_l I (R := S) mp.2.1
  let Cp : Pn.Domain := ⟨C',saved'.context.member⟩
  have targetZF := ZFC.models_zf_l (target.native_l I hZF tree.omega)
  have hP := ZF.modelsKP targetZF
  have fp := saved'.context.finite_l mp.2.1 hP.1
  have rankC := (rr_rank_native_l I mp.2.1 hP ⟨η',saved'.context.height⟩ Cp).mp
    ((rr_rank_truth_l I).mpr saved'.context.rank)
  have limitC : Pn.IsLimitOrdinal ⟨η',saved'.context.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => (⟨η',saved'.context.height⟩ : Pn.Domain))).mp saved'.context.limit)
  obtain ⟨oldBound,regularP⟩ := tg_round_control_l hP rankC limitC fp nd ρ round
  have eqκ : κ' = (ρ.bound 15).val.val := by
    have e := back.1.1.2 (ν.bound 1).val.val bκ (vs 15) pointκ (oldLinks 2)
    exact embed.1.1.1.2 (vs 15) κ' _ (e ▸ edgeκ) (recordPoints 15)
  have bound x (hx : Rd_entry_d x l S) : Rd_entry_d x (ρ.bound 15).val.val S := eqκ ▸ boundκ x hx
  let ln : Pn.Domain := ⟨l,common.right_rank.1⟩
  let Vn : Pn.Domain := ⟨V,common.right_rank.2.1⟩
  have rv := (rr_rank_native_l I mp.2.1 hP ln Vn).mp common.right_rank
  have lδ : Pn.mem ln (ρ.bound 18).val := ordinal_down_l hP (v_ordinal_l (kp_pair_l hP) rv)
    regularP.isCardinal.1 (fun x hx => bound x.val hx) oldBound
  have lC := fp.transitive (ρ.bound 18).val (ρ.bound 18).property ln lδ
  have lη := KP.v_ordinal_height_l hP rankC (v_ordinal_l (kp_pair_l hP) rv) lC
  have inside : Pn.mem Vn Cp := (KP.v_compare_l hP rv rankC
    ((v_ordinal_l (kp_pair_l hP) rankC).transitive ln lη)).2 lη
  have fs := request.context.finite_l mn.2.1 hN.1
  have rankSource := (rr_rank_native_l I mn.2.1 hN ⟨η,request.context.height⟩ Cn).mp
    ((rr_rank_truth_l I).mpr request.context.rank)
  have limitSource : Nn.IsLimitOrdinal ⟨η,request.context.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => (⟨η,request.context.height⟩ : Nn.Domain))).mp request.context.limit)
  have regular := (tg_issued_control_l hN rankSource limitSource fs nc ι issued).2
  have height : Nn.IsLimitOrdinal (ν.bound 2).val :=
    (congrArg Subtype.val (newEq 1)).symm ▸ regular.isLimitOrdinal
  have cofinal : Tg_raw_cofinal_d I w N R L.val :=
    it_support_cofinal_l I hZF.1 mn.2.1 hN card rankX height
  have highχ : Rd_entry_d χ L.val R := boundEq ▸ hχL
  have highτ : Rd_entry_d (ι.bound 24).val.val L.val R :=
    Eq.mp (congrArg (fun x => Rd_entry_d x.val.val L.val R) (newEq 2)) hτL
  obtain ⟨Xr,Rr,wroot,Kroot,zroot,mroot,_,rootNumbers⟩ := (tree.sources o c₀ qr).objects
  obtain ⟨eX,eR⟩ := smdl_unique_l I mroot root.model
  subst Xr Rr
  have alphabet : Rd_entry_d A₀ (ι.bound 6).val.val q := (eq 6).symm ▸ request.alphabet
  obtain ⟨ψ,ε,ζ,queries,coords,queryPlay,lowShort,lowLabels,candidate,targetQueries,candidatePoints,queryPoints,
    candidateω,queryω,finite,nodeQuery,maxQuery,scopeQuery,emptyQuery⟩ :=
    common.continue_candidate_l hZF tree.omega root mn mp right rootMap rootNumbers request.numbers numbers
      request.context saved'.context cut slice slice' roots
      (fun x hx => fp.transitive Vn inside ⟨x,(mp.2.2.2 x V hx).1⟩ hx) nc nd ν ι ε₀ seed issued
      ((congrArg (fun x => x.val.val) (newEq 0)).trans hwι) links hτL omegaSlice alphabet lower
      reply replyω replyN replyLt replyMem replyEmpty
  have fullImages i : Rd_entry_d (src.bound i).val (σ.bound i).val.val ts :=
    Eq.mpr (congrArg (fun x => Rd_entry_d (src.bound i).val x.val ts) (reflected i)) (nativePoints i)
  have points5 : ∀ i : Fin 5, Rd_entry_d (ι.bound ([0,24,28,25,27].get i)).val.val
      (σ.bound ([0,3,4,6,1].get i)).val.val ts := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))))
    · exact Eq.mpr (congrArg (fun x => Rd_entry_d x (σ.bound 0).val.val ts) hwι) (fullImages 0)
    · exact Eq.mp (congrArg (fun x => Rd_entry_d x.val.val (σ.bound 3).val.val ts) (newEq 2)) (fullImages 3)
    · exact Eq.mp (congrArg (fun x => Rd_entry_d x.val.val (σ.bound 4).val.val ts) (newEq 3)) (fullImages 4)
    · exact Eq.mp (congrArg (fun x => Rd_entry_d x.val.val (σ.bound 6).val.val ts) (newEq 4)) (fullImages 6)
    · exact Eq.mp (congrArg (fun x => Rd_entry_d x.val.val (σ.bound 1).val.val ts) arity) (fullImages 1)
  have programEq : ∀ i : Fin 9, ν.bound ([14,16,21,22,23,24,25,26,27].get i) =
      ι.bound ([36,37,38,39,40,41,42,43,44].get i) :=
    Fin.cases (newEq 5) (Fin.cases (newEq 6) (Fin.cases (newEq 7) (Fin.cases (newEq 8)
      (Fin.cases (newEq 9) (Fin.cases (newEq 10) (Fin.cases (newEq 11)
        (Fin.cases (newEq 12) (Fin.cases (newEq 13) (fun i => Fin.elim0 i)))))))))
  have programs : ∀ i : Fin 9, Rd_entry_d (ι.bound ([36,37,38,39,40,41,42,43,44].get i)).val.val
      (σ.bound ([7,8,10,11,12,13,14,15,16].get i)).val.val ts := by
    intro i
    have e : src.bound ([7,8,10,11,12,13,14,15,16].get i) =
        (ν.bound ([14,16,21,22,23,24,25,26,27].get i)).val := by
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))) i
    have h := fullImages ([7,8,10,11,12,13,14,15,16].get i)
    rw [e] at h
    exact Eq.mp (congrArg (fun x => Rd_entry_d x.val.val
      (σ.bound ([7,8,10,11,12,13,14,15,16].get i)).val.val ts) (programEq i)) h
  have oldTree : Rd_entry_d S₀ (ρ.bound 19).val.val q' :=
    (rootComp.2 S₀ _).mpr ⟨vs 19,name vs code,recordPoints 19⟩
  have facts := seed
  simp only [tc_seed0_m,Formula.satisfies_conj_iff] at facts
  obtain ⟨_,_,_,limitν,_,_,_,_,exceedsν,_⟩ := facts
  have limitν := (rt_limit_l fs.transitive nc hN (ν.bound 8)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limitν)
  have before : Nn.mem (ν.bound 1).val (ν.bound 8).val := ((Formula.satisfies_conj_iff ..).mp exceedsν).1
  have targetLower x (hx : Rd_entry_d x γ' S) : Rd_entry_d x (ε.bound 3).val.val S := by
    obtain ⟨y,hy,yx⟩ := (common.pred γ γ' iγ x).mp hx
    have h := limitν.1.transitive (ν.bound 1).val before ⟨y,(mn.2.2.2 y γ hy).1⟩ (lower y hy)
    have h' : Rd_entry_d y (ι.bound 24).val.val R :=
      Eq.mp (congrArg (fun x => Rd_entry_d y x.val.val R) (newEq 2)) h
    exact (common.pred _ _ (candidatePoints 3) x).mpr ⟨y,h',yx⟩
  refine ⟨m₀,r₀,row,hm₀,index,stored,tuple,link,mx,saved,name,vs,code,?_⟩
  refine ⟨nc,ι,ν,eq,issued,seed,result,arity,boundEq,newEq,?_⟩
  refine ⟨s,t,a,play,short,size,labels,b,is,it,γ,Vγ,tγ,slice,omegaSlice,lower,?_⟩
  refine ⟨L,U,rankU,small,cofinal,highχ,highτ,?_⟩
  refine ⟨θ,T₁,Q₁,G₁,E₁,Λ₁,d,P,S,j,q',p,next,extension,node,edge,move,rootEdge,lf₁,levels₁,entries,?_⟩
  refine ⟨mp,target,embed,rootMap,rootComp,critical,?_⟩
  refine ⟨l,V,Γ,g,common,roots,Bp,ts,fullPool,restrict,endpoint,layer,Pκ,rankK,lowSquare,?_⟩
  refine ⟨(native17.bound 0).val,η',C',L',U',r',z',iw,iη,iC,numbers,pointω,saved',?_⟩
  refine ⟨nd,ρ,σ,code',round,recordPoints,oldTree,subtype,prior,program,points5,programs,bound,inside,?_⟩
  exact ⟨γ',Vγ',tγ',iγ,iVγ,slice',omegaSlice',ψ,ε,ζ,queries,coords,queryPlay,lowShort,lowLabels,candidate,targetQueries,
    candidatePoints,queryPoints,candidateω,queryω,finite,nodeQuery,maxQuery,scopeQuery,emptyQuery,targetLower⟩

end YesMetaZFC.SetTheory.LargeCardinal
