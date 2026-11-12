import YesMetaZFC.SetTheory.LargeCardinal.Game.RawResetReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootContinueStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawPrepareRoot
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawAnswer
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # 一般原请求的同次重置核验

原请求只调用一次工厂和一次回答搬运。三个表项经实际根方块回到原回答
核验，再沿同一完整代表池返回；完成的回答、根切片、原前缀和档案列
均属于同一个新原模型。两次树延伸及支撑列保留实际源行，不引入工作复制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 空标签分支完成原回答、三个查询、根几何及全部旧档案的同步核验。 -/
theorem Tg_raw_request_d.reset_checked_l
    {ω S₀ X₀ R₀ w₀ γ₀ B₀ D₀ C₀ A₀ A N R w η C χ z k D r q c₀ n m T Q G E Λ d o f : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k D r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d I ω c₀ X₀ R₀)
    (cut : Tg_root_cut_d I c₀ X₀ R₀ w₀ γ₀ B₀ A₀ D₀ A)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qn : Rd_entry_d n d Q) (mn : Smdl_d I d N R) (qr : Rd_entry_d o c₀ Q)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i μ, Rd_entry_d i μ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ μ F)
    (empty : v 23 = v 1)
    (prior : Tg_prefix_d I k A N R C (v 4) (v 3) (v 20) z q f) :
    ∃ L W r₁, Tg_saved_d I w N R η C L W r₁ ∧
    ∃ vs : Fin 54 → M.Domain, Tg_saved_code_d N R w W r₁ vs ∧
      vs 17 = v 1 ∧ vs 19 = v 7 ∧
      vs 22 = v 1 ∧ vs 40 = v 1 ∧ vs 41 = v 1 ∧ vs 42 = v 1 ∧ Rd_entry_d χ L R ∧
    ∃ θ T₁ Q₁ G₁ E₁ jp q₁, M.SuccessorOf θ m ∧ It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁ ∧ Rd_entry_d m d Q₁ ∧
      It_map_d G₁ n m jp ∧ (∀ x y, Rd_entry_d x y jp → x = y) ∧ It_map_d G₁ o m q₁ ∧
      (∀ x y, Rd_entry_d x y q₁ ↔ Rd_entry_d x y q) ∧
      Tg_saved_name_d I S₀ N R w W r₁ q₁ ∧
    ∃ θ₂ T₂ Q₂ G₂ E₂ d₂ P R₂ j₂ q₂ p₂ Λ₂,
      It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧ It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ d₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      M.IsSetFunction I Λ₂ ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ ∃ p κ F, Rd_entry_d i p E₂ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₂ ↔ Rd_entry_d i μ Λ ∨ i = m ∧ μ = L) ∧
      (⟨m,d,N,R,w,η,C,L,W,r₁,q₁⟩ : Tg_raw_archive_row_d M.Domain).link_d ⟨o,θ,Q₂,G₂,Λ₂⟩ ∧
      Tg_raw_archive_links_d I ⟨o,θ,Q₂,G₂,Λ₂⟩ D ∧
    ∃ target : Smdl_d I d₂ P R₂, Zc_model_d I ω d₂ P R₂ ∧
      Smap_d I ω d d₂ N P j₂ ∧ Smap_d I ω c₀ d₂ X₀ P q₂ ∧ It_comp_d q j₂ q₂ ∧
      (Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂) ∧
    ∃ l Vc Dc t, Ic_common_d I N R P R₂ L l W Vc Dc t ∧ Tg_root_square_d D₀ q₁ q₂ t ∧
    ∃ w₂ η₂ C₂ z₂, Rd_entry_d w w₂ j₂ ∧ Rd_entry_d η η₂ j₂ ∧ Rd_entry_d C C₂ j₂ ∧
      Rr_layer_d I ω P R₂ w₂ z₂ ∧
    ∃ current : Tg_context_d I w₂ P R₂ η₂ C₂,
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := R₂) target.2.1).Domain //
      (smdl_structure_l I (R := R₂) target.2.1).mem x ⟨C₂,current.member⟩},
    ∃ ι₂ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd) 46,
      (∀ i, Rd_entry_d (v i) (ι₂.bound i).val.val j₂) ∧ Formula.satisfies ι₂ tg_issued0_m ∧
      (ι₂.bound 0).val.val = w₂ ∧
      Tg_round_index_d I ω z₂ target.2.1 ⟨w₂,current.omega_mem⟩ (ι₂.bound 19).val k ∧
      Rd_entry_d S₀ (ι₂.bound 7).val.val q₂ ∧ Rd_entry_d A₀ (ι₂.bound 6).val.val q₂ ∧
      (∀ x, Rd_entry_d x l R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧ Rd_entry_d l C₂ R₂ ∧
      Tg_prefix_d I k A P R₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 3).val.val (ι₂.bound 20).val.val z₂ q₂ f ∧
      Tg_raw_archive_views_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ q₂ D P R₂ l w₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 1).val.val
        (ι₂.bound 2).val.val (ι₂.bound 3).val.val z₂ (ι₂.bound 20).val.val ∧
    ∃ γ₂ Vγ₂ tγ₂, Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P R₂ C₂ q₂ γ₂ Vγ₂ tγ₂ ∧
      Rd_entry_d w₂ Vγ₂ R₂ ∧ (∀ x, Rd_entry_d x γ₂ R₂ → Rd_entry_d x (ι₂.bound 24).val.val R₂) ∧
    ∃ B fA, (∀ y, M.mem y B ↔ M.mem y P ∧ Rd_entry_d y (ι₂.bound 6).val.val R₂) ∧
      M.IsSetBijectionFromTo I fA A B ∧ M.IsRestrictionOf I fA q₂ A ∧
    ∃ τ u Aq Uq Dq rq mq bq hq qq : (rt_model_l
      (M := smdl_structure_l I (R := R₂) target.2.1) ⟨C₂,current.member⟩ nd).Domain,
      Rd_entry_d τ.val.val (ι₂.bound 5).val.val R₂ ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,τ,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1)
          ⟨C₂,current.member⟩ nd) 5) tg_query_request0_m ∧
      Tg_query_data_d (ι₂.bound 11) τ (ι₂.bound 26) (ι₂.bound 1) (ι₂.bound 1) Aq Uq Dq rq mq bq hq qq ∧
      Formula.satisfies (⟨fun i => [ι₂.bound 0,ι₂.bound 27,ι₂.bound 28,ι₂.bound 24,τ,
        ι₂.bound 30,ι₂.bound 31,Dq,ι₂.bound 25,u,ι₂.bound 36,ι₂.bound 37,rq,bq,hq,
        ι₂.bound 38,ι₂.bound 39,ι₂.bound 40,ι₂.bound 41,ι₂.bound 42,ι₂.bound 43,ι₂.bound 44].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l (M := smdl_structure_l I (R := R₂) target.2.1)
          ⟨C₂,current.member⟩ nd) 22) tg_reply0_m ∧
      Rd_entry_d (vs 41) (ι₂.bound 23).val.val t ∧ Rd_entry_d (vs 15) τ.val.val t ∧
      Rd_entry_d (vs 11) u.val.val t ∧
      (∃ a, Rd_entry_d (vs 40) a t ∧ Tg_play_d I P R₂ C₂ (ι₂.bound 4).val.val
        (ι₂.bound 3).val.val (ι₂.bound 20).val.val a) ∧
      Tg_raw_answer_result_d I target.2.1 ⟨C₂,current.member⟩ nd w₂ η₂ ω z₂ k l
        X₀ R₀ γ₀ D₀ C₀ A₀ S₀ q₂ D t ⟨m,d,N,R,w,η,C,L,W,r₁,q₁⟩
        ⟨o,θ,Q₂,G₂,Λ₂⟩ ι₂ τ u := by
  let right := tree.diagram.elementary o n q c₀ X₀ R₀ d N R request.origin qr qn root.model mn
  have sourceZc := root.map_l hZF tree.omega mn right
  have ground := sourceZc.native_l I hZF tree.omega
  have native := ZFC.models_zf_l ground
  have hN := ZF.modelsKP native
  obtain ⟨nc,ι,eq,issued,factory⟩ := request.reset_factory_l hZFC root tree hm qn mn qr empty
  obtain ⟨_,_,ρ,_,_,round,links,eκ,_,lengthZero,shortZero,labelZero,graphZero,treeEq,_,growth,rest⟩ := factory
  obtain ⟨L,W,r₁,saved,code,cofinal,above,rest⟩ := rest
  obtain ⟨X,K,R₁,F,c₁,d₁,Y,S,j₁,κ₁,U₁,D₁,u₁,data,rest⟩ := rest
  obtain ⟨V,Γ,k₁,Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,d₂,P,R₂,j₂,q₂,p₂,rankV,carrier,idGraph,_,cert,rest⟩ := rest
  obtain ⟨_,_,_,_,payload,_,rest⟩ := rest
  obtain ⟨θ,T₁,Q₁,G₁,E₁,jp,q₁,succ,next,extension,node,pad,identity,noMove,root₁,same,rest⟩ := rest
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,tree₂,extension₂,node₂,edge₂,move₂,root₂,_⟩ := rest
  have hw : (ι.bound 0).val.val = w := (eq 0).trans request.omega
  have empty' : ι.bound 23 = ι.bound 1 := Subtype.ext (Subtype.ext
    ((eq 23).trans (empty.trans (eq 1).symm)))
  -- 一次解包同时固定共同图、完整池、目标上下文和两份实际原记录。
  obtain ⟨l,Vc,Dc,t,common,Pκ,rankP,high,square,_,Bp,t₀,_,_,pool,restrict,_,_,predPool,
    mp,target,embed,rootMap,rootGraph,w₂,η₂,C₂,z₂,iw,iη,iC,numbers,pointω,current,nd,ι₂,ε₂,
    points,issued₂,eqω,ordinal,boundκ,_,member,_,_,reply,sameReply,label,domain,type,
    finiteL,finiteNp,pointBase,belowτ,key,Aq,Uq,Dq,rq,mq,bq,hq,qq,domainEq,table,language,queries⟩ :=
    data.raw_reset_reply_l hZF tree.omega root mn native request.context nc ι ρ issued round hw links
      empty' growth L W X K R₁ F c₁ d₁ Y S j₁ κ₁ U₁ D₁ u₁ V rankV carrier idGraph cert
  let Pn := smdl_structure_l I (R := R₂) mp.2.1
  let Cp : Pn.Domain := ⟨C₂,current.member⟩
  have targetZF := ZFC.models_zf_l (target.native_l I hZF tree.omega)
  have hP := ZF.modelsKP targetZF
  have fs := request.context.finite_l mn.2.1 hN.1
  have fp := current.finite_l mp.2.1 hP.1
  have h₀ := ZF.modelsKP (ZFC.models_zf_l (root.native_l I hZF tree.omega))
  obtain ⟨γ,Vγ,tγ,slice,omegaSlice,lower⟩ := request.slice
  have below x (hx : Rd_entry_d x γ R) : Rd_entry_d x (ρ.bound 21).val.val R :=
    Eq.mpr (congrArg (fun y => Rd_entry_d x y R) (eκ.trans (eq 24))) (lower x hx)
  obtain ⟨γ₂,Vγ₂,tγ₂,_,iVγ,_,slice₂,_,lower₂,roots,a₂,B,fA,iA,_,range,bij,restriction⟩ :=
    Tg_root_slice_d.reset_l hZF cut h₀ slice common mn mp hN hP (ρ.bound 21).val Pκ rankP high
      (fun x hx y => square x y hx) below right.1.1 rootMap.1.1.1 rootGraph iC boundκ ordinal request.alphabet
  have rootComp : It_comp_d q j₂ q₂ := ⟨rootMap.1.1.1.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨v,xv,vy⟩ => ⟨right.1.1.input_mem_of_pairMember xv,v,xv,vy⟩⟩⟩
  have oldPoints i : Rd_entry_d (v i) (ι₂.bound i).val.val j₂ := (eq i) ▸ points i
  have eqA : a₂ = (ι₂.bound 6).val.val := embed.1.1.1.2 (v 6) a₂ _ iA (oldPoints 6)
  have range : ∀ y, M.mem y B ↔ M.mem y P ∧ Rd_entry_d y (ι₂.bound 6).val.val R₂ := by
    simpa only [eqA] using range
  have targetName := (rootComp.2 S₀ _).mpr ⟨v 7,request.name,oldPoints 7⟩
  have targetAlphabet := (rootComp.2 A₀ _).mpr ⟨v 6,request.alphabet,oldPoints 6⟩
  have omegaSlice₂ : Rd_entry_d w₂ Vγ₂ R₂ := (common.pred Vγ Vγ₂ iVγ w₂).mpr ⟨w,omegaSlice,pointω⟩
  -- 三个目标查询先回到原回答核验；目标 ω 的低层所属来自同一前驱方程。
  let queryEnv : Env (rt_model_l Cp nd) 12 :=
    ⟨fun i => [ι₂.bound 0,ι₂.bound 1,ι₂.bound 27,ι₂.bound 28,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1,
      rq,mq,bq,hq,qq].get i,ι₂.free⟩
  let fields : Fin 7 → Term 12 := fun i => [.bound 0,.bound 1,.bound 2,.bound 3,.bound 7,.bound 9,.bound 10].get i
  let base := Definitional.Env.substitute queryEnv fields
  have baseTruth : Formula.satisfies base tg_reply_base0_m :=
    (Formula.satisfies_bind queryEnv fields tg_reply_base0_m).mp
      ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp queries).1).2
  have facts := language
  simp only [tg_reply_language0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at facts
  let wn : Pn.Domain := ⟨w₂,current.omega_mem⟩
  let Vgn : Pn.Domain := ⟨Vγ₂,slice₂.rank.2.1⟩
  have omega := numbers.omega_l I (ZF.modelsKP hZF) tree.omega hP.1
  have hwN : (ι₂.bound 0).val = wn := Subtype.ext eqω
  have finiteN : Pn.mem (ι₂.bound 28).val wn := finiteNp
  have rankG₂ := (rr_rank_native_l I mp.2.1 hP ⟨γ₂,slice₂.rank.1⟩ Vgn).mp slice₂.rank
  have small (x : Pn.Domain) (hx : Pn.mem x wn) : Pn.mem x Vgn :=
    v_transitive_l (kp_pair_l hP) rankG₂ wn omegaSlice₂ x hx
  have low : ∀ i : Fin 4, Pn.mem (base.bound (i.castAdd 3)).val Vgn :=
    Fin.cases (hwN.symm ▸ omegaSlice₂)
      (Fin.cases (small _ (omega.transitive hP _ finiteN _ facts.2.1))
        (Fin.cases (small _ (omega.transitive hP _ finiteN _ facts.2.2.1))
          (Fin.cases (small _ finiteN) (fun i => Fin.elim0 i))))
  have basePoints : ∀ i : Fin 4, Rd_entry_d (ρ.bound ([16,17,23,24].get i)).val.val
      (base.bound (i.castAdd 3)).val.val t₀ :=
    Fin.cases (pointBase 0) (Fin.cases (pointBase 1)
      (Fin.cases (pointBase 2) (Fin.cases (pointBase 3) (fun i => Fin.elim0 i))))
  have members := slice.reply_members_l hZF slice₂ roots tree.omega root.model mn mp right rootMap
    fs.transitive nc nd hP wn (ε₂.bound 9).val omega fp (request.context.kernel_l mn.2.1 nc)
    ρ round base hwN finiteN low baseTruth pool restrict predPool basePoints
      ((restrict.2 _ _).mp type).2
  have rankC := (rr_rank_native_l I mp.2.1 hP ⟨η₂,current.height⟩ Cp).mp ((rr_rank_truth_l I).mpr current.rank)
  have limitC : Pn.IsLimitOrdinal ⟨η₂,current.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => (⟨η₂,current.height⟩ : Pn.Domain))).mp current.limit)
  have tableReply := tg_reply_table_l targetZF omega rankC limitC fp nd ε₂ finiteL reply
    rq bq hq members.1 members.2.1 members.2.2
  let answer : Env (rt_model_l Cp nd) 22 :=
    ⟨fun i => [ι₂.bound 0,ι₂.bound 27,ι₂.bound 28,ι₂.bound 24,ε₂.bound 4,
      ι₂.bound 30,ι₂.bound 31,Dq,ι₂.bound 25,ε₂.bound 9,ι₂.bound 36,ι₂.bound 37,rq,bq,hq,
      ι₂.bound 38,ι₂.bound 39,ι₂.bound 40,ι₂.bound 41,ι₂.bound 42,ι₂.bound 43,ι₂.bound 44].get i,
      fun _ => ι₂.bound 0⟩
  have aligned : (tg_reply_table_env_d ε₂ rq bq hq).bound = answer.bound := by
    funext i
    exact Fin.cases (sameReply 0).symm (Fin.cases (sameReply 1).symm (Fin.cases (sameReply 2).symm
      (Fin.cases (sameReply 3).symm (Fin.cases rfl (Fin.cases (sameReply 4).symm
        (Fin.cases (sameReply 5).symm (Fin.cases domainEq.symm (Fin.cases (sameReply 6).symm
          (Fin.cases rfl (Fin.cases (sameReply 7).symm (Fin.cases (sameReply 8).symm
            (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases (sameReply 9).symm
              (Fin.cases (sameReply 10).symm (Fin.cases (sameReply 11).symm (Fin.cases (sameReply 12).symm
                (Fin.cases (sameReply 13).symm (Fin.cases (sameReply 14).symm
                  (Fin.cases (sameReply 15).symm (fun i => Fin.elim0 i)))))))))))))))))))))) i
  have answerTruth := (Formula.closed_env_l tg_reply0_m tg_reply0_closed_l aligned).mp tableReply
  have requestTruth : Formula.satisfies
      (⟨fun i => [ι₂.bound 0,ε₂.bound 4,ι₂.bound 26,ι₂.bound 1,ι₂.bound 1].get i,
        fun _ => ι₂.bound 0⟩ : Env (rt_model_l Cp nd) 5) tg_query_request0_m :=
    (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l rfl).mp key
  -- 原轮号由两份实际数字图保持，故档案索引没有重新选择。
  have digits := (request.numbers.omega_map_l I hZF tree.omega mn mp embed sourceZc.ext target.ext numbers).2
  have indexPoint : Rd_entry_d k (ι₂.bound 19).val.val z₂ := by
    obtain ⟨n',_,nn'⟩ := numbers.injection.1.2.2 k request.finite
    have ni := digits k (v 19) n' request.index nn'
    exact embed.1.1.1.2 (v 19) n' _ ni (oldPoints 19) ▸ nn'
  obtain ⟨k',index⟩ := tg_round_index_l I (ZF.modelsKP hZF) tree.omega mp.2.1 hP.1 wn
    (ι₂.bound 19).val numbers ((numbers.image _).mpr ⟨k,request.finite,indexPoint⟩)
  have indexEq := numbers.injection.2 k' k (ι₂.bound 19).val.val index.point indexPoint
  have index : Tg_round_index_d I ω z₂ mp.2.1 wn (ι₂.bound 19).val k := indexEq ▸ index
  have letters x (hx : M.mem x A) : ∃ y, M.mem y N ∧ Rd_entry_d x y q := by
    have ha := (cut.carrier A₀).mpr ⟨(cut.model.2.2.2 A₀ B₀ cut.alphabet).1,cut.alphabet⟩
    have hd := cut.down_l hZF h₀ A₀ x ha ((cut.letters x).mp hx).2
    obtain ⟨y,hy,xy⟩ := slice.injection.1.2.2 x hd
    exact ⟨y,hy,slice.root x y xy⟩
  have play := prior.map_l hZF tree.omega mn mp embed sourceZc.ext target.ext request.numbers numbers
    letters (tree.omega.transitive (ZF.modelsKP hZF) k request.finite) rootMap.1.1.1
    (fun x y z xy yz => (rootComp.2 x z).mpr ⟨y,xy,yz⟩) iC (oldPoints 4) (oldPoints 3) (oldPoints 20)
  have trace := current.trace_image_l hZF tree.omega mn mp embed hP sourceZc.ext request.numbers numbers nd
    (ι₂.bound 4) (ι₂.bound 1) (ι₂.bound 2) (ι₂.bound 3) (ι₂.bound 20) iw iC
    (oldPoints 4) (oldPoints 1) (oldPoints 2) (oldPoints 3) (oldPoints 20)
  have oldViews := request.views.step_l hZF common mn mp hN hP.1 (ρ.bound 21).val Pκ rankP high
    (Eq.mpr (congrArg (fun y => Rd_entry_d χ y R) (eκ.trans (eq 24))) request.below)
    (fun x hx y => square x y hx) rootComp trace (ι₂.bound 20).property (fun _ _ hx => hx)
  -- 恒等填充不改变支撑；真实活动只追加本轮保存的 L。
  have levels₁ := extension.levels_pad_l noMove levels
  obtain ⟨Λ₂,lf₂,levels₂,entries⟩ := next.levels_extend_l hZF succ lf levels₁ tree₂ extension₂ move₂ payload
  let frame : Tg_raw_archive_frame_d M.Domain := ⟨o,θ,Q₂,G₂,Λ₂⟩
  let row : Tg_raw_archive_row_d M.Domain := ⟨m,d,N,R,w,η,C,L.val,W.val,r₁,q₁⟩
  have rowLink : row.link_d frame := ⟨succ.predecessor_mem,extension₂.2.2.1 m d node,
    (extension₂.2.2.2.1 o m q₁ succ.predecessor_mem).mpr root₁,
    (entries m L.val).mpr (Or.inr ⟨rfl,rfl⟩)⟩
  have oldLinks : Tg_raw_archive_links_d I frame D := request.links.extend_l I
    (fun i hi => (succ i).mpr (Or.inl ((hm i).mpr (Or.inl hi))))
    (fun i c hi => extension₂.2.2.1 i c (extension.2.2.1 i c hi))
    (fun i p hi hp => (extension₂.2.2.2.1 o i p ((succ i).mpr (Or.inl ((hm i).mpr (Or.inl hi))))).mpr
      ((extension.2.2.2.1 o i p ((hm i).mpr (Or.inl hi))).mpr hp))
    (fun i μ hi => (entries i μ).mpr (Or.inl hi))
  have sourceName : Tg_saved_name_d I S₀ N R w W.val r₁ q₁ :=
    Tg_saved_name_d.of_code_l I hZF.1 code
      ((same S₀ (ρ.bound 19).val.val).mpr (treeEq.symm ▸ (eq 7).symm ▸ request.name))
  -- 填充根图逐点不变；保存时的源切片及候选界写入同一新档案行。
  have sourceSlice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C q₁ γ Vγ tγ :=
    { slice with context := (same C₀ C).mpr slice.context
                 root := fun x y xy => (same x y).mpr (slice.root x y xy) }
  have critical (old : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E) :
      Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂ := by
    have mid := extension.raw_critical_pad_l I
      (fun i c hi => (tree.diagram.model_domain i).mpr ⟨c,hi⟩) old noMove
    exact extension₂.raw_critical_apply_l I (ZF.modelsKP hZF)
      (fun i c hi => (next.diagram.model_domain i).mpr ⟨c,hi⟩) mid tree₂.move_function
      move₂ payload (extension₂.2.2.1 m d node) mn
      ((extension₂.2.2.2.1 o m q₁ succ.predecessor_mem).mpr root₁) sourceSlice below
  have body := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff] at body
  have language := body.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have limitτ := (rt_limit_l fs.transitive nc hN (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have sourceBase := Tg_raw_saved_base_d.of_code_l I hZF.1 sourceSlice omegaSlice code
    (fun x hx => limitτ.1.transitive (ι.bound 24).val growth
      ⟨x,(mn.2.2.2 x γ hx).1⟩
      (Eq.mpr (congrArg (fun y => Rd_entry_d x y R) (eq 24)) (lower x hx)))
  have savedRoots : Tg_root_square_d D₀ q₁ q₂ t :=
    fun a ha x ax y => roots a ha x ((same a x).mp ax) y
  -- 重置短图是同一原空集，完整旧视图由原控制规则直接读取。
  have emptyImage : (ι₂.bound 23).val.val = (ι₂.bound 1).val.val := embed.1.1.1.2 (ι.bound 1).val.val _ _
    (Eq.mp (congrArg (fun x => Rd_entry_d x (ι₂.bound 23).val.val j₂)
      (congrArg (fun x => x.val.val) empty')) (points 23)) (points 1)
  have shortEq : (ρ.bound 40).val.val = (ρ.bound 41).val.val := shortZero.trans labelZero.symm
  have shortPoint : Rd_entry_d (ρ.bound 40).val.val (ι₂.bound 1).val.val t :=
    Eq.mpr (congrArg (fun x => Rd_entry_d x (ι₂.bound 1).val.val t) shortEq)
      (Eq.mp (congrArg (fun y => Rd_entry_d (ρ.bound 41).val.val y t) emptyImage) label)
  have state₂ := (tg_issued_sat_l (rt_pair_l fp.transitive nd hP.1 fp.pair)
    (rt_model_ext_l hP.1 fp.transitive nd) ι₂).mp issued₂
  have rules := state₂.control
  simp only [tg_control0_m,Formula.satisfies_conj_iff] at rules
  have rules := rules.2.2.1
  simp only [tg_rules_m,Formula.satisfies_conj_iff,Formula.satisfies_isEmpty_iff] at rules
  have shortPlay : Tg_play_d I P R₂ C₂ (ι₂.bound 4).val.val (ι₂.bound 3).val.val
      (ι₂.bound 20).val.val (ι₂.bound 1).val.val :=
    (tg_play_native_l I mp.2.1 hP.1 Cp fp.transitive nd (rt_pair_l fp.transitive nd hP.1 fp.pair)
      (ι₂.bound 4) (ι₂.bound 3) (ι₂.bound 20) (ι₂.bound 1)).mpr
      (fun _ _ ⟨p,_,hp⟩ => (rules.2.1 p hp).elim)
  have answered := current.answer_raw_l (ZF.modelsKP hZF) mp.2.1 hP nd ι₂ issued₂ eqω ω z₂ k index
    ⟨l,common.right_rank.1⟩ (fun x hx => boundκ x.val hx)
    (ε₂.bound 4) (ε₂.bound 9) Aq Uq Dq rq mq bq hq qq belowτ requestTruth table answerTruth
    X₀ R₀ γ₀ D₀ C₀ A₀ S₀ q₂ t Vc Dc row frame root₂ targetName targetAlphabet rowLink sourceName
    mn saved ⟨z,request.numbers⟩ sourceBase cofinal common savedRoots
    (fun i => (ρ.bound i).val.val) code label domain type
    ⟨_,shortPoint,shortPlay⟩ γ₂ Vγ₂ tγ₂ slice₂ omegaSlice₂ lower₂ D request.sequence oldViews oldLinks
  exact ⟨L.val,W.val,r₁,saved,(fun i => (ρ.bound i).val.val),code,
    (links 1).trans (eq 1),treeEq.trans (eq 7),
    lengthZero.trans (eq 1),shortZero.trans (eq 1),labelZero.trans (eq 1),graphZero.trans (eq 1),above,
    θ,T₁,Q₁,G₁,E₁,jp,q₁,succ,next,extension,node,pad,identity,root₁,same,sourceName,
    θ₂,T₂,Q₂,G₂,E₂,d₂,P,R₂,j₂,q₂,p₂,Λ₂,tree₂,extension₂,node₂,edge₂,move₂,root₂,
    lf₂,levels₂,entries,rowLink,oldLinks,mp,target,embed,rootMap,rootComp,critical,l,Vc,Dc,t,common,savedRoots,
    w₂,η₂,C₂,z₂,iw,iη,iC,numbers,current,nd,ι₂,oldPoints,issued₂,eqω,index,targetName,targetAlphabet,
    boundκ,member,play,oldViews,γ₂,Vγ₂,tγ₂,slice₂,omegaSlice₂,lower₂,B,fA,range,bij,restriction,
    ε₂.bound 4,ε₂.bound 9,Aq,Uq,Dq,rq,mq,bq,hq,qq,belowτ,requestTruth,table,answerTruth,
    label,domain,type,⟨(ι₂.bound 1).val.val,shortPoint,shortPlay⟩,answered⟩

end YesMetaZFC.SetTheory.LargeCardinal
