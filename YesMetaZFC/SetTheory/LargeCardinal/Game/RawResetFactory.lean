import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRequest
import YesMetaZFC.SetTheory.LargeCardinal.Game.IssuedReset
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # 一般原请求的同次重置工厂

原请求自身的反射核生产回答与支撑；原树先插入恒等边，再施加这一次
回答中的扩展器。完整证书、根图和原后继全部保留，不读取工作复制历史。
支撑界只用原请求的 χ < κ；根切片的推进由同一证书的共同图另行完成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一原重置轮、固定超幂和实际两步树延伸的完整生产结果。 -/
def Tg_raw_reset_factory_d
    (ω c₀ X₀ R₀ n m T Q G E N R d o q w η C z χ : M.Domain)
    (mn : Smdl_d I d N R) (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (context : Tg_context_d I w N R η C)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46) : Prop :=
    ∃ ε : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 38,
    ∃ a : Fin 16 → (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc).Domain,
    ∃ ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 54,
      Formula.satisfies ε tg_seed0_m ∧ ρ = tg_round_env_d ε a ∧ Formula.satisfies ρ tg_round0_m ∧
      Tg_request_d Eq (fun i => (ι.bound i).val.val) (fun i => (ρ.bound i).val.val) ∧
      (ρ.bound 21).val.val = (ι.bound 24).val.val ∧
      (ρ.bound 39).val.val = (ι.bound 24).val.val ∧
      (ρ.bound 22).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 40).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 41).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 42).val.val = (ι.bound 1).val.val ∧
      (ρ.bound 19).val.val = (ι.bound 7).val.val ∧
      (ρ.bound 20).val.val = (ι.bound 8).val.val ∧
      Rd_entry_d (ι.bound 24).val.val (ρ.bound 15).val.val R ∧
    ∃ L W : (smdl_structure_l I (R := R) mn.2.1).Domain, ∃ r,
      Tg_saved_d I w N R η C L.val W.val r ∧
      Tg_saved_code_d N R w W.val r (fun i => (ρ.bound i).val.val) ∧
      Tg_raw_cofinal_d I w N R L.val ∧ Rd_entry_d χ L.val R ∧
    ∃ X K R₁ F c₁ d₁ Y S j₁ κ₁ U₁ D₁ u₁ : (smdl_structure_l I (R := R) mn.2.1).Domain,
      Tg_image_at_d hN ⟨w,context.omega_mem⟩
        (ρ.bound 21).val (ρ.bound 18).val (ρ.bound 23).val (ρ.bound 24).val
        (ρ.bound 31).val (ρ.bound 32).val (ρ.bound 34).val (ρ.bound 15).val
        (ρ.bound 12).val (ρ.bound 11).val (ρ.bound 36).val
        (fun i => (ρ.bound ([47,48,49,50,51,52,53].get i)).val) (ρ.bound 38).val
        ⟨(ρ.bound 2).val,(ρ.bound 1).val,(ρ.bound 0).val⟩ L W X K R₁ F c₁ d₁ Y S j₁ κ₁ U₁ D₁ u₁ ∧
    ∃ V : (smdl_structure_l I (R := R) mn.2.1).Domain,
    ∃ Γ k Ls Js Os Zs Ds ps Vs Ws qs d₂ P R₂ j₂ q₂ p₂,
      V_d (kp_pair_l hN) (ρ.bound 15).val V ∧
      (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x X.val R) ∧
      (∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y) ∧ Rr_small_d I N R X.val ∧
      Er_rank_cut_at_d hZF ω c₀ X₀ R₀ d N R q Γ k N R z d mn.2.1 hN
        X ⟨w,context.omega_mem⟩ (ρ.bound 21).val L F V X K j₁
        Ls Js Os Zs Ds ps Vs Ws qs d₂ P R₂ j₂ q₂ p₂ ∧
    ∃ target : Smdl_d I d₂ P R₂,
      Zc_model_d I ω d₂ P R₂ ∧ (smdl_structure_l I (R := R₂) target.2.1).Models ZFC ∧
      Smap_d I ω c₀ d₂ X₀ P q₂ ∧ It_payload_d p₂ (ρ.bound 21).val.val L.val F.val ∧
      It_active_d hZF ω d d d₂ j₂ p₂ ∧
    ∃ θ T₁ Q₁ G₁ E₁ j q₁,
      M.SuccessorOf θ m ∧ It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m d Q₁ ∧ It_map_d G₁ n m j ∧ (∀ x y, Rd_entry_d x y j → x = y) ∧
      (∀ p, Rd_entry_d n p E₁ → ∀ x, ¬ M.mem x p) ∧
      It_map_d G₁ o m q₁ ∧ (∀ x y, Rd_entry_d x y q₁ ↔ Rd_entry_d x y q) ∧
    ∃ θ₂ T₂ Q₂ G₂ E₂,
      It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧
      It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ d₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      ∀ x E, Rd_entry_d x E q₂ ↔ M.mem x X₀ ∧ ∃ y, Rd_entry_d x y q₁ ∧ Rd_entry_d y E j₂

variable (hZFC : M.Models ZFC)

/-- 实际请求直接调用原反射核、保存工厂和原树延伸；原生理论由根图自动供应。 -/
theorem Tg_raw_request_d.reset_factory_l
    {ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k D r q c₀ n m T Q G E Λ d o : M.Domain}
    {v : Fin 46 → M.Domain}
    (request : Tg_raw_request_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
      ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ N R w η C χ z k D r q ⟨o,n,Q,G,Λ⟩ v)
    (root : Zc_model_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c₀ X₀ R₀)
    (tree : It_tree_d (ZFC.models_zf_l hZFC) ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qn : Rd_entry_d n d Q) (mn : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N R)
    (qr : Rd_entry_d o c₀ Q) (empty : v 23 = v 1) :
    let right := tree.diagram.elementary o n q c₀ X₀ R₀ d N R request.origin qr qn root.model mn
    let ground := (root.map_l (ZFC.models_zf_l hZFC) tree.omega mn right).native_l
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (ZFC.models_zf_l hZFC) tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    ∃ nc : Nonempty {x : (smdl_structure_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
        (R := R) mn.2.1).Domain //
      (smdl_structure_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (R := R) mn.2.1).mem x
        ⟨C,request.context.member⟩},
    ∃ ι : Env (rt_model_l (M := smdl_structure_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
      (R := R) mn.2.1) ⟨C,request.context.member⟩ nc) 46,
      (∀ i, (ι.bound i).val.val = v i) ∧ Formula.satisfies ι tg_issued0_m ∧
      Tg_raw_reset_factory_d (ZFC.models_zf_l hZFC) ω c₀ X₀ R₀ n m T Q G E N R d o q w η C z χ
        mn hN request.context nc ι := by
  intro right ground hN
  let hZF := ZFC.models_zf_l hZFC
  let J₀ := kp_pair_l (ZF.modelsKP hZF)
  let Nn := smdl_structure_l J₀ (R := R) mn.2.1
  let context := request.context
  obtain ⟨nc,ι,eq,issued,_⟩ := request.read_l J₀ (ZF.modelsKP hZF) hN.1
  have hw : (ι.bound 0).val.val = w := (eq 0).trans request.omega
  have empty : ι.bound 23 = ι.bound 1 := Subtype.ext (Subtype.ext
    ((eq 23).trans (empty.trans (eq 1).symm)))
  have below : Rd_entry_d χ (ι.bound 24).val.val R := (eq 24).symm ▸ request.below
  have fs := context.finite_l mn.2.1 hN.1
  let J := rt_pair_l fs.transitive nc hN.1 fs.pair
  have ext := rt_model_ext_l hN.1 fs.transitive nc
  obtain ⟨ε,seed,head,length_zero,hb,zero,tag,graph,_,_,_,_,matched⟩ :=
    tg_issued_reset_l J ext ι issued empty
  obtain ⟨a,round⟩ := tg_successor_read_l ε seed ((context.kernel_l mn.2.1 nc).renew_l ε seed)
  let ρ := tg_round_env_d ε a
  have links : Tg_request_d Eq (fun i => (ι.bound i).val.val) (fun i => (ρ.bound i).val.val) :=
    fun i => congrArg (fun x => x.val.val) (matched a i)
  have eκ : (ρ.bound 21).val = (ι.bound 24).val := congrArg Subtype.val (matched a 14)
  have eχ : (ρ.bound 39).val = (ι.bound 24).val := (congrArg Subtype.val hb).trans eκ
  have ew : (ρ.bound 16).val.val = w := (congrArg (fun x => x.val.val) (matched a 0)).trans hw
  obtain ⟨L,W,r₁,saved,code,high,X,K,R₁,F,c₁,d₁,Y,S,j₁,κ₁,U₁,D₁,u₁,data⟩ :=
    context.save_round_native_l hZF mn.2.1 ground
      (request.numbers.omega_l J₀ (ZF.modelsKP hZF) tree.omega hN.1) nc ρ round ew
  have limitL : Nn.IsLimitOrdinal L := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l J₀ mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => L)).mp saved.limit)
  have above : Rd_entry_d χ L.val R := limitL.1.transitive (ι.bound 24).val (eχ ▸ high)
    ⟨χ,request.ordinal.1 0⟩ below
  have body := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [tg_witness0_m,tg_round_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at body
  have growth : Nn.mem (ι.bound 24).val (ρ.bound 15).val := eχ ▸ body.1
  have language := body.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff] at language
  have limitτ := (rt_limit_l fs.transitive nc hN (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have rankC := (rr_rank_native_l J₀ mn.2.1 hN ⟨η,context.height⟩ ⟨C,context.member⟩).mp
    ((rr_rank_truth_l J₀).mpr context.rank)
  have limitC : Nn.IsLimitOrdinal ⟨η,context.height⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l J₀ mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ⟨η,context.height⟩)).mp context.limit)
  have height := (tg_round_control_l hN rankC limitC fs nc ρ round).2.isLimitOrdinal
  have imageData := data
  obtain ⟨rankX,source,hLδ,_,hτL,_,_,loc,card,strong,mx,my,ultra,crit,lb,_⟩ := imageData
  have cofinal := it_support_cofinal_l J₀ hZF.1 mn.2.1 hN card rankX height
  obtain ⟨V,Γ,k₁,rankV,carrier,idGraph,small,cut⟩ := loc.raw_self_l hZFC tree.omega mn.2.1 ground
    ⟨w,context.omega_mem⟩ (ρ.bound 21).val L F (ρ.bound 15).val X K R₁ (ρ.bound 18).val
    c₁ d₁ Y S j₁ κ₁ mn root right request.numbers rankX height limitτ (eκ.symm ▸ growth) hτL hLδ
    source mx my ultra card strong crit.image lb
  obtain ⟨Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,d₂,P,R₂,j₂,q₂,p₂,cert⟩ := cut
  -- 同一证书同时给出目标理论、原根复合图和实际活动步，不再选择后继。
  have used := cert
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,mp,_,_,_,_,rootMap,_,_,payload,active,certificate,rootGraph,
    Uc,rankUc,readUc,_,_,l,Vc,Dc,t,common,_,_,tail⟩ := used
  obtain ⟨Pκ,rankP,lowSquare,κ₀,bκ,κ',hκ₀,hbκ,hκ',belowL,boundκ,neκ,memκ,ordκ,ord₀,ord₁,
    fixκ,lowerImages,anchors,rest⟩ := tail
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,build⟩ := rest
  have target := certificate root
  have targetGround : (smdl_structure_l J₀ (R := R₂) mp.2.1).Models ZFC :=
    target.native_l J₀ hZF tree.omega
  obtain ⟨_,_,_,extend⟩ := build.2 root
  -- 恒等填充只延长原树；其根图与旧根图逐点相同。
  obtain ⟨θ,T₁,Q₁,G₁,E₁,d',j,succ,next,extension,old,node,edge,identity,_,noMove⟩ :=
    it_pad_l hZF tree hm
  have equal := tree.diagram.model_function.2 n d' d old qn
  subst d'
  have parentNode := extension.2.2.1 n d qn
  have oldRoot := (extension.2.2.2.1 o n q hm.predecessor_mem).mpr request.origin
  have pad := next.diagram.elementary n m j d N R d N R edge parentNode node mn mn
  obtain ⟨q₁,root₁⟩ := next.diagram.map_l hZF
    ((extension.2.1 o m).mpr (Or.inr ⟨rfl,Or.inr (tree.diagram.map_bound_l hZF request.origin)⟩))
  have keep x y (point : Rd_entry_d x y q) : Rd_entry_d x y q₁ := by
    obtain ⟨v,_,hv⟩ := pad.1.1.2.2 y (right.1.1.output_mem_of_pairMember point)
    have fixed : Rd_entry_d y y j := (identity y v hv).symm ▸ hv
    exact next.diagram.comp o n m q j q₁ oldRoot edge root₁ x y y point fixed
  have padRoot := next.diagram.elementary o m q₁ c₀ X₀ R₀ d N R root₁
    (extension.2.2.1 o c₀ qr) node root.model mn
  have same x y : Rd_entry_d x y q₁ ↔ Rd_entry_d x y q := by
    refine ⟨fun h => ?_,keep x y⟩
    obtain ⟨v,_,hv⟩ := right.1.1.2.2 x (padRoot.1.1.input_mem_of_pairMember h)
    exact (padRoot.1.1.1.2 x v y (keep x v hv) h) ▸ hv
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,tree₂,extension₂,node₂,edge₂,move₂,root₂,_⟩ :=
    extend θ m T₁ Q₁ G₁ E₁ n o next succ node parentNode oldRoot
  have composite x E : Rd_entry_d x E q₂ ↔
      M.mem x X₀ ∧ ∃ y, Rd_entry_d x y q₁ ∧ Rd_entry_d y E j₂ := by
    refine (rootGraph x E).trans (and_congr_right fun _ => ?_)
    exact exists_congr fun y => and_congr (same x y).symm Iff.rfl
  refine ⟨nc,ι,eq,issued,ε,a,ρ,seed,rfl,round,links,congrArg Subtype.val eκ,
    congrArg Subtype.val eχ,congrArg (fun x => x.val.val) length_zero,
    congrArg (fun x => x.val.val) zero,congrArg (fun x => x.val.val) tag,
    congrArg (fun x => x.val.val) graph,congrArg (fun x => x.val.val) (head 3),
    congrArg (fun x => x.val.val) (head 4),growth,L,W,r₁,saved,code,cofinal,above,
    X,K,R₁,F,c₁,d₁,Y,S,j₁,κ₁,U₁,D₁,u₁,data,V,Γ,k₁,Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,d₂,P,R₂,j₂,q₂,p₂,
    rankV,carrier,idGraph,small,cert,mp,target,targetGround,rootMap,payload,active,
    θ,T₁,Q₁,G₁,E₁,j,q₁,succ,next,extension,node,edge,identity,noMove,root₁,same,
    θ₂,T₂,Q₂,G₂,E₂,tree₂,extension₂,node₂,edge₂,move₂,root₂,composite⟩

end YesMetaZFC.SetTheory.LargeCardinal
