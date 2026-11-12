import YesMetaZFC.SetTheory.LargeCardinal.Demand.ContinueFirst
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.OwnerQuality

/-! # 非重置请求的完整原回合

从实际档案选中奇父节点，连续执行两次扩展器施加，并在下一实数落子前
登记新奇行。调用者只给当前请求与已保持的不变量；两个施加、深度后继、
字母枚举和新档案均由本回合产生，不另行指定中间模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_raw_continue_l
    {Ω c₀ X₀ R₀ wr zr o n m T Q G E cN N R qN z Da a D₀ γ₀ C₀ CN γN VN tN : M.Domain}
    (root : Zc_model_d I Ω c₀ X₀ R₀) (rootNumbers : Rr_layer_d I Ω X₀ R₀ wr zr)
    (tree : It_tree_d hZF Ω c₀ m T Q G E) (owned : It_owned_d I Ω Q E) (hm : M.SuccessorOf m n)
    (qr : Rd_entry_d o c₀ Q) (current : Rd_entry_d n cN Q) (origin : It_map_d G o n qN)
    (mn : Smdl_d I cN N R)
    (ι : Env (smdl_structure_l I (R := R) mn.2.1) 47)
    (issued : Formula.satisfies ι td_issued0_m) (ne : ι.bound 23 ≠ ι.bound 1)
    (numbers : Rr_layer_d I Ω N R (ι.bound 0).val z)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R CN qN γN VN tN)
    (omegaLow : Rd_entry_d (ι.bound 0).val VN R)
    (lettersLow : Rd_entry_d (ι.bound 6).val VN R)
    (lettersRoot : Rd_entry_d Ar (ι.bound 6).val qN) (treeRoot : Rd_entry_d Sr (ι.bound 7).val qN)
    (ha : M.mem a Ω) (sequence : M.IsSequenceOfLength I Da a)
    (index : Rd_entry_d a (ι.bound 19).val z)
    (χ : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (hχ : (smdl_structure_l I (R := R) mn.2.1).mem χ (ι.bound 5))
    (archive : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ.val
      (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val z (ι.bound 20).val D₀ qN)
    (archiveBound : Rd_entry_d χ.val (ι.bound 24).val R)
    (treeLinks : Td_archive_links_d o Q G E Da)
    (powerCount : Pc_count_d I Ω N R (ι.bound 5).val)
    (alphabetCode : Td_code_d I N R (ι.bound 7).val (ι.bound 5).val) :
    ∃ s : Td_archive_row_d M.Domain,
      (∃ r k, M.mem k a ∧ Rd_entry_d k r Da ∧ Rt_tuple_d s.values_d r) ∧
      Rd_entry_d s.i s.c Q ∧ It_map_d G o s.i s.p ∧
    ∃ ξ κP θ T₁ Q₁ G₁ E₁ cP P S jP qP pP θ₂ T₂ Q₂ G₂ E₂ cH H RH J qH pH,
      It_tree_d hZF Ω c₀ θ T₁ Q₁ G₁ E₁ ∧ It_extension_d m n s.i T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m cP Q₁ ∧ It_map_d G₁ s.i m jP ∧ Rd_entry_d n pP E₁ ∧ It_map_d G₁ o m qP ∧
      It_tree_d hZF Ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧
      It_owned_d I Ω Q₂ E₂ ∧
      It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ cH Q₂ ∧ It_map_d G₂ n θ J ∧ Rd_entry_d m pH E₂ ∧ It_map_d G₂ o θ qH ∧
      (∀ γ, It_lower_d I γ N R ξ → It_lower_d I γ P S κP →
        It_critical_bound_d I γ Q E → It_critical_bound_d I γ Q₂ E₂) ∧
      (Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂) ∧
    ∃ mh : Smdl_d I cH H RH, ∃ target : Zc_model_d I Ω cH H RH,
      Smap_d I Ω cN cH N H J ∧ Smap_d I Ω c₀ cH X₀ H qH ∧ It_comp_d qN J qH ∧
    ∃ CH γH VH tH lH zh a' Da' r, ∃ row : Td_archive_row_d M.Domain,
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ H RH CH qH γH VH tH ∧ Rd_entry_d γH lH RH ∧
      M.mem a' Ω ∧ M.SuccessorOf a' a ∧ M.IsSequenceOfLength I Da' a' ∧
      (∀ i t, Rd_entry_d i t Da' ↔ Rd_entry_d i t Da ∨ i = a ∧ t = r) ∧
      Rt_tuple_d row.values_d r ∧ row.i = m ∧ row.c = cP ∧ row.X = P ∧ row.R = S ∧ row.p = qP ∧
      M.SuccessorOf row.depth s.depth ∧
      (∀ p y, Rd_entry_d p y row.ancestors ↔
        Td_depth_next_d Ω s.depth s.ancestors s.enumeration jP p y) ∧
      Td_aux_growth_d I P S jP s.v row.v ∧ Td_archive_links_d o Q₂ G₂ E₂ Da' ∧
      Ic_round_d hZF Ω (fun i => [n,m,T,Q,G,E,N,R,χ.val].get i)
        (fun i => [θ,θ₂,T₂,Q₂,G₂,E₂,H,RH,lH].get i) ∧
    ∃ ι' : Env (smdl_structure_l I (R := RH) mh.2.1) 47,
      (∀ i, Rd_entry_d (ι.bound i).val (ι'.bound i).val J) ∧ Formula.satisfies ι' td_issued0_m ∧
      Rr_layer_d I Ω H RH (ι'.bound 0).val zh ∧
      Rd_entry_d (ι'.bound 0).val VH RH ∧ Rd_entry_d (ι'.bound 6).val VH RH ∧
    ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x (ι.bound 6) →
    let Hn := smdl_structure_l I (R := RH) mh.2.1
    let hH := ZF.modelsKP (ZFC.models_zf_l (target.native_l I hZF tree.omega))
    ∃ b y h t : Hn.Domain, ∃ ψ : Env Hn 47,
      Rd_entry_d x.val b.val J ∧ Hn.mem y (ι'.bound 6) ∧
      (∃ b₀ : Hn.Domain, Fseq_end_d (kp_pair_l hH) (ι'.bound 0) h (ι'.bound 20) b₀) ∧
      (Gm_even_d (kp_pair_l hH) (ι'.bound 0) (ι'.bound 19) → y = b) ∧
      (¬ Gm_even_d (kp_pair_l hH) (ι'.bound 0) (ι'.bound 19) → Rd_entry_d h y (ι'.bound 17)) ∧
      Fseq_end_d (kp_pair_l hH) (ι'.bound 0) t h y ∧
      Fseq_end_d (kp_pair_l hH) (ι'.bound 0) (ψ.bound 20) t (ψ.bound 21) ∧
      Rd_entry_d t (ψ.bound 21) (ι'.bound 17) ∧
      (∀ i : Fin 19, ψ.bound (i.castAdd 28) = ι'.bound (i.castAdd 28)) ∧
      Formula.satisfies ψ td_issued0_m ∧ Rd_entry_d a' (ψ.bound 19).val zh ∧
      Rd_entry_d Ar (ψ.bound 6).val qH ∧ Rd_entry_d Sr (ψ.bound 7).val qH ∧
      Hn.mem (ι'.bound 24) (ψ.bound 24) ∧ Rd_entry_d lH (ψ.bound 24).val RH ∧
      Hn.MemberSubset h (ψ.bound 20) ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da' H RH lH
        (ψ.bound 4).val (ψ.bound 1).val (ψ.bound 2).val zh (ψ.bound 20).val D₀ qH ∧
      Td_rank_step_d (N := smdl_structure_l I (R := R) mn.2.1) (P := Hn)
        (fun x y => Rd_entry_d x.val y.val J) ι.bound ψ.bound ∧
      Pc_count_d I Ω H RH (ψ.bound 5).val ∧ Td_code_d I H RH (ψ.bound 7).val (ψ.bound 5).val := by
  have fromN := tree.diagram.elementary o n qN c₀ X₀ R₀ cN N R origin qr current root.model mn
  have ground := (root.map_l hZF tree.omega mn fromN).native_l I hZF tree.omega
  have hN := ZF.modelsKP (ZFC.models_zf_l ground)
  -- 先选真实旧行，再依次读取共同层、继续输入和第一次施加。
  obtain ⟨s,saved,selected,parent,parentRoot,first⟩ := archive.demand_first_l hZFC tree.omega
    root rootNumbers mn fromN ι issued ne numbers slice omegaLow lettersLow lettersRoot
      sequence index χ hχ treeLinks powerCount
  obtain ⟨l,V,Δ,g,common,_,_,first⟩ := first
  obtain ⟨τ,w,θ,_,_,_,_,_,first⟩ := first
  obtain ⟨ρ,_,_,_,_,coords,_,first⟩ := first
  obtain ⟨s₀,pn,pm,_,_,_,_,first⟩ := first
  obtain ⟨X,K,R',L,F,c,d,Y,T',j,κ',U',D',u',rankX,source,height,first⟩ := first
  obtain ⟨_,_,below,_,loc,card,strong,_,_,_,_,_,_,_,_,_,_,_,first⟩ := first
  obtain ⟨α,β,B,v,_,_,_,_,_,_,inverse,first⟩ := first
  obtain ⟨Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,cP,P,S,jP,qP,pP,cert,first⟩ := first
  obtain ⟨mp,Ul,lp,Vp,Δp,gp,commonP,first⟩ := first
  obtain ⟨CP,γP,VP,tP,sliceP,_,_,_,rootsP,first⟩ := first
  obtain ⟨Ac,Qc,Yc,ec,Dc,Γc,t,_,_,_,_,_,_,_,_,_,_,first⟩ := first
  obtain ⟨η,_,_,ζ,_,_,_,_,first⟩ := first
  obtain ⟨nativeP,Bc,Vc,Dq,_,_,_,_,first⟩ := first
  obtain ⟨pn',pm',_,_,_,_,first⟩ := first
  obtain ⟨e',l',s',k',pc',qc',_,_,_,_,_,first⟩ := first
  obtain ⟨ν₁,X₁,c₁,R₁,r₁,a₁,b₁,z₁,π₁,_,dep,tab,depthStep,_,tableGraph,first⟩ := first
  obtain ⟨ξ,_,_,_,_,_,_,_,_,_,_,_,_,first⟩ := first
  obtain ⟨ε,same,round,endpoint,points,depth,chosen,lower,rootLow,
    roundLetters,roundTree,omegaP,lettersP,basePoints,oddCount,supportBelow,oddCode,growth,realTrace,realPoint,lowerN⟩ := first
  have numbersρ : Rr_layer_d I Ω N R (ρ.bound 0).val z :=
    (congrArg Subtype.val (coords 0)).symm ▸ numbers
  have lower' x (hx : Rd_entry_d x γP S) : Rd_entry_d x (ε.bound 24).val S :=
    (congrArg Subtype.val (same 5)).symm ▸ lower x hx
  have historyBound x (hx : Rd_entry_d x lp S) : Rd_entry_d x (ε.bound 43).val S := endpoint.symm ▸ hx
  -- 第二施加只读取上述同一次输出；新奇行连同枚举在这里实际登记。
  have second := cert.demand_double_l hZFC root rootNumbers tree hm mn qr parent current
    parentRoot origin hN ⟨V,common.right_rank.2.1⟩ (ρ.bound 0) (ρ.bound 1) L F β X K j
      (ρ.bound 2) (ι.bound 24) (ι.bound 25) source.omega rankX height card
      (coords 2 ▸ below) mp commonP ε round (points 2) (points 5) ι issued points basePoints realTrace realPoint
      sliceP omegaP lettersP rootsP lower' historyBound numbersρ archive archiveBound powerCount oddCount
      supportBelow alphabetCode oddCode depth chosen rootLow roundLetters roundTree ha sequence index treeLinks
  obtain ⟨L₂,W₂,X₂,K₂,R₂,F₂,c₂,d₂,Y₂,S₂,j₂,κ₂,U₂,E₂,u₂,image₂,_,_,second⟩ := second
  obtain ⟨α₂,β₂,B₂,v₂,zp,_,_,_,_,_,_,_,numsP,second⟩ := second
  obtain ⟨Ls₂,Js₂,Os₂,Zs₂,Ds₂,ps₂,Vs₂,Ws₂,qs₂,cH,H,RH,J,qH,pH,_,target,embed,rootH,rootGraph,payload₂,_,second⟩ := second
  obtain ⟨mh,lH,VH,ΔH,gH,D,tH,_,_,_,_,_,_,_,second⟩ := second
  obtain ⟨ζ₂,_,_,_,_,_,_,_,_,_,_,ι',images,issued',_,second⟩ := second
  obtain ⟨CH,γH,VH₀,tH₀,sliceH,_,_,_,boundH,_,_,_,wLow,aLow,second⟩ := second
  obtain ⟨b,pair,answer,keys,zh,h,jh,nums,second⟩ := second
  obtain ⟨nativeH,ending,_,_,_,_,_,a',Da',r,En,ha',succ,seq,tuple,append,registered,second⟩ := second
  obtain ⟨θ₁,T₁,Q₁,G₁,E₁,θ₂,T₂,Q₂,G₂,Eout,tree₁,ext₁,node₁,edge₁,move₁,root₁,
    tree₂,ext₂,node₂,edge₂,move₂,root₂,critical,links,copy₂,next⟩ := second
  have roots : It_comp_d qN J qH := ⟨rootH.1.1.1.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨a,xa,ay⟩ => ⟨fromN.1.1.input_mem_of_pairMember xa,a,xa,ay⟩⟩⟩
  have firstData := cert
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,payload₁,_⟩ := firstData
  have quality₁ := it_owner_l I mn hN (ρ.bound 0) (ρ.bound 1) L F
    (ρ.bound 2) X K R' numbersρ rankX height source loc card strong
  have chosenSource := selected
  obtain ⟨r₀,k₀,_,entry₀,pack₀⟩ := chosenSource
  obtain ⟨_,_,p₀,κ₀,F₀,oldMove,oldPayload⟩ := treeLinks k₀ r₀ s entry₀ pack₀
  have copy₁ := ic_copy_past_l hZFC tree hm saved.model mn parent current hN
    ⟨V,common.right_rank.2.1⟩ (ρ.bound 0) (ρ.bound 1) L F β X K j (ρ.bound 2) R' cert
      numbersρ source rankX height loc quality₁ common oldMove oldPayload inverse saved.small commonP
      ((loc.ordinals_l hN source.transitive source.code).2.transitive (ι.bound 24) (coords 2 ▸ below) χ archiveBound)
      tree₁ ext₁ node₁ edge₁ move₁ payload₁
  have copy := copy₁.trans_l hZF copy₂
  have owned₁ := ext₁.owned_apply_l I owned tree₁.move_function.2 move₁ payload₁
    (ext₁.2.2.1 n cN current) quality₁
  obtain ⟨rank₂,source₂,_,_,_,_,_,loc₂,card₂,strong₂,_⟩ := image₂
  obtain ⟨_,height₂,_⟩ := td_round_native_l (ZF.modelsKP nativeP) ε round
  have quality₂ := it_owner_l I mp (ZF.modelsKP nativeP) (ε.bound 19) (ε.bound 24) L₂ F₂
    (ε.bound 21) X₂ K₂ R₂ numsP rank₂ height₂ source₂ loc₂ card₂ strong₂
  have owned₂ := ext₂.owned_apply_l I owned₁ tree₂.move_function.2 move₂ payload₂
    (ext₂.2.2.1 m cP node₁) quality₂
  have rawCritical (old : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E) :
      Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ Eout := by
    have kept := ext₁.raw_critical_apply_l I (ZF.modelsKP hZF)
      (fun i c hi => (tree.diagram.model_domain i).mpr ⟨c,hi⟩) old tree₁.move_function move₁ payload₁
      (ext₁.2.2.1 n cN current) mn ((ext₁.2.2.2.1 o n qN hm.predecessor_mem).mpr origin) slice lowerN
    exact ext₂.raw_critical_apply_l I (ZF.modelsKP hZF)
      (fun i c hi => (tree₁.diagram.model_domain i).mpr ⟨c,hi⟩) kept tree₂.move_function move₂ payload₂
      (ext₂.2.2.1 m cP node₁) mp ((ext₂.2.2.2.1 o m qP ext₁.1.predecessor_mem).mpr root₁) sliceP lower'
  refine ⟨s,selected,parent,parentRoot,(ρ.bound 1).val,(ε.bound 24).val,
    θ₁,T₁,Q₁,G₁,E₁,cP,P,S,jP,qP,pP,θ₂,T₂,Q₂,G₂,Eout,cH,H,RH,J,qH,pH,
    tree₁,ext₁,node₁,edge₁,move₁,root₁,tree₂,owned₂,ext₂,node₂,edge₂,move₂,root₂,critical,rawCritical,
    mh,target,embed,rootH,roots,CH,γH,VH₀,tH₀,lH,zh,a',Da',r,
    ⟨fun i => (ε.bound i).val,m,cP,P,S,qP,L₂.val,W₂.val,zp,dep,tab,En⟩,
    sliceH,boundH,ha',succ,seq,append,tuple,rfl,rfl,rfl,rfl,rfl,depthStep,tableGraph,growth,links,copy,
    ι',images,issued',nums,wLow,aLow,?_⟩
  -- 所有树边及新行先于输入固定；原策略随后产生实数步和下一请求。
  intro x hx
  dsimp only
  obtain ⟨b',y,t',ψ,xb,hy,even,odd,digit,aux,value,head,_,valid,increase,bound,history,
    archive',rank,count,code,index'⟩ := next x hx
  exact ⟨b',y,h,t',ψ,xb,hy,⟨b,ending⟩,even,odd,digit,aux,value,head,valid,index',
    (congrArg Subtype.val (head 6)).symm ▸ (roots.2 _ _).mpr ⟨_,lettersRoot,images 6⟩,
    (congrArg Subtype.val (head 7)).symm ▸ (roots.2 _ _).mpr ⟨_,treeRoot,images 7⟩,
    increase,bound,history,archive',rank,count,code⟩

end YesMetaZFC.SetTheory.LargeCardinal
