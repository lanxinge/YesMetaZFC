import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RawPool
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate
import YesMetaZFC.SetTheory.LargeCardinal.Demand.PowerRead
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ResetRequest
import YesMetaZFC.SetTheory.LargeCardinal.Demand.AnswerArchive
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootContinueStep
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundReal
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.OwnerQuality
import YesMetaZFC.SetTheory.LargeCardinal.Demand.CopyReset

/-! # demanding 重置回答的实际双后继

原模型自己的完整回合给出同次更新的一步证书。先插入恒等边，再把该
扩展器施加到同一原模型，保留实际施加证书、两条根图和完整树扩张。
完整回答沿同一次施加的代表池进入新模型，三个元数及临界像界一并保留。
旧档案的共同图、根方块及事件沿同一次实际后继自动更新。
原模型的幂集计数同时控制支撑和代表，产生指定原边上每个 δ 像的计数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_reset_tree_l
    {Ω c₀ X₀ R₀ n m T Q G E c N R o q z Da χ D₀ : M.Domain}
    (root : Zc_model_d I Ω c₀ X₀ R₀)
    (tree : It_tree_d hZF Ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (qr : Rd_entry_d o c₀ Q) (qn : Rd_entry_d n c Q)
    (mn : Smdl_d I c N R) (origin : It_map_d G o n q)
    (ρ : Env (smdl_structure_l I (R := R) mn.2.1) 62)
    (valid : Formula.satisfies ρ td_round0_m)
    (numbers : Rr_layer_d I Ω N R (ρ.bound 19).val z)
    (ctl : Env (smdl_structure_l I (R := R) mn.2.1) 4)
    (archive : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χ
      (ctl.bound 0).val (ctl.bound 1).val (ctl.bound 2).val z (ctl.bound 3).val D₀ q)
    (archiveBound : Rd_entry_d χ (ρ.bound 24).val R)
    (powerCount : Pc_count_d I Ω N R (ρ.bound 21).val) :
    let N₀ := smdl_structure_l I (R := R) mn.2.1
    let map := tree.diagram.elementary o n q c₀ X₀ R₀ c N R origin qr qn root.model mn
    let ground := (root.map_l hZF tree.omega mn map).native_l I hZF tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    ∃ dep tab, (∀ x, ¬ M.mem x dep) ∧
      Td_depth_d I Ω N R (ρ.bound 47).val dep tab ∧ Td_pick_d I Ω dep tab (ρ.bound 49).val ∧
    ∃ L W X K R₁ F c₁ d₁ Y S j₁ κ' U' E' u' : N₀.Domain,
      Td_image_at_d hN (ρ.bound 19)
        (ρ.bound 24) (ρ.bound 21) (ρ.bound 27) (ρ.bound 28) (ρ.bound 9)
        (ρ.bound 35) (ρ.bound 36) (ρ.bound 38) (ρ.bound 0) (ρ.bound 3)
        (ρ.bound 4) (ρ.bound 40) (ρ.bound 42) (ρ.bound 16) (ρ.bound 17)
        (ρ.bound 18) (fun i => ρ.bound ⟨55+i.val,by omega⟩)
        L W X K R₁ F c₁ d₁ Y S j₁ κ' U' E' u' ∧
      Tg_raw_cofinal_d I (ρ.bound 19).val N R L.val ∧
    ∃ V : N₀.Domain, ∃ Γ k,
      V_d (kp_pair_l hN) (ρ.bound 0) V ∧
      (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x X.val R) ∧
      (∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ x = y) ∧ Rr_small_d I N R X.val ∧
    ∃ Ls Js Os Zs Ds ps Vs Ws qs c₂ P R₂ j₂ q₂ p₂,
      Er_rank_cut_at_d hZF Ω c₀ X₀ R₀ c N R q Γ k N R z c mn.2.1 hN
        X (ρ.bound 19) (ρ.bound 24) L F V X K j₁
        Ls Js Os Zs Ds ps Vs Ws qs c₂ P R₂ j₂ q₂ p₂ ∧
      Zc_model_d I Ω c₂ P R₂ ∧ Smap_d I Ω c c₂ N P j₂ ∧
      Smap_d I Ω c₀ c₂ X₀ P q₂ ∧
      (∀ x y, Rd_entry_d x y q₂ ↔ M.mem x X₀ ∧ ∃ a, Rd_entry_d x a q ∧ Rd_entry_d a y j₂) ∧
      It_payload_d p₂ (ρ.bound 24).val L.val F.val ∧
      It_active_d hZF Ω c c c₂ j₂ p₂ ∧
    ∃ mt : Smdl_d I c₂ P R₂, ∃ l W₂ Δ g Dp t,
      Ic_common_d I N R P R₂ L.val l W.val W₂ Δ g ∧
      Rr_small_d I N R W.val ∧
      M.IsSetInjectionFromTo I t Dp P ∧ M.IsRestrictionOf I g t Δ ∧
      Rd_entry_d L.val l t ∧ Rd_entry_d W.val W₂ t ∧
      (∀ x E, Rd_entry_d x E t → ∀ y, Rd_entry_d y E R₂ ↔
        ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a y t) ∧
      (∀ x y : N₀.Domain, ∀ a E,
        N₀.mem x V → Rd_entry_d x y j₁ → Rd_entry_d x.val a k →
          (Rd_entry_d y.val E t ↔ Rd_entry_d a E j₂)) ∧
    ∃ ε : Env (smdl_structure_l I (R := R₂) mt.2.1) 23,
      (∀ i, Rd_entry_d
        (td_reply_values_d (ρ.bound 19) (ρ.bound 27) (ρ.bound 28) (ρ.bound 9)
          κ' (ρ.bound 0) U' E' (ρ.bound 3) u' (ρ.bound 4) (ρ.bound 40)
          (ρ.bound 42) (ρ.bound 16) (ρ.bound 17) (ρ.bound 18)
          (fun j => ρ.bound ⟨55+j.val,by omega⟩) i).val (ε.bound i).val t) ∧
      Formula.satisfies ε td_reply0_m ∧
      (∃ zt, Rr_layer_d I Ω P R₂ (ε.bound 0).val zt) ∧
      Rd_entry_d (ρ.bound 19).val (ε.bound 0).val g ∧
      Rd_entry_d (ε.bound 1).val (ε.bound 0).val R₂ ∧
      Rd_entry_d (ε.bound 2).val (ε.bound 0).val R₂ ∧
      Rd_entry_d (ε.bound 3).val (ε.bound 0).val R₂ ∧
      (∀ x, Rd_entry_d x l R₂ → Rd_entry_d x (ε.bound 4).val R₂) ∧
    ∃ Kκ : N₀.Domain, V_d (kp_pair_l hN) (ρ.bound 24) Kκ ∧
      (∀ x : N₀.Domain, N₀.mem x Kκ → ∀ E, Rd_entry_d x.val E g ↔ Rd_entry_d x.val E j₂) ∧
    ∃ ctl' : Env (smdl_structure_l I (R := R₂) mt.2.1) 4, ∃ zt,
      (∀ i, Rd_entry_d (ctl.bound i).val (ctl'.bound i).val j₂) ∧
      Rr_layer_d I Ω P R₂ (ε.bound 0).val zt ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da P R₂ l
        (ctl'.bound 0).val (ctl'.bound 1).val (ctl'.bound 2).val zt (ctl'.bound 3).val D₀ q₂ ∧
    ∃ θ T₁ Q₁ G₁ E₁ j,
      M.SuccessorOf θ m ∧ It_tree_d hZF Ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m c Q₁ ∧ It_map_d G₁ n m j ∧
      (∀ x y, Rd_entry_d x y j → x = y) ∧
      (∀ p, Rd_entry_d n p E₁ → ∀ x, ¬ M.mem x p) ∧
    ∃ θ₂ T₂ Q₂ G₂ E₂,
      It_tree_d hZF Ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧
      It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ c₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      (∀ γ, It_lower_d I γ N R (ρ.bound 24).val → It_critical_bound_d I γ Q E →
        It_critical_bound_d I γ Q₂ E₂) ∧
      ∀ δ', Rd_entry_d (ρ.bound 21).val δ' j₂ → Pc_count_d I Ω P R₂ δ' := by
  intro N₀ map ground hN
  obtain ⟨dep,tab,zero,depth,chosen⟩ := td_depth_zero_l I
    (X := N) (R := R) (U := (ρ.bound 47).val) (z := (ρ.bound 49).val) tree.omega
  have native := ZFC.models_zf_l ground
  obtain ⟨_,height,limitτ,growth,_,L,W,X,K,R₁,F,c₁,d₁,Y,S,j₁,κ',U',E',u',image⟩ :=
    td_round_native_l hN ρ valid
  have data := image
  obtain ⟨rankX,source,hLδ,_,hτL,rankW,hDW,loc,card,strong,mx,my,ultra,crit,bound,
    limitκ,iU,iE,iu,_,reply⟩ := data
  have cofinal := it_support_cofinal_l I hZF.1 mn.2.1 hN card rankX height
  obtain ⟨V,Γ,k,rankV,carrier,idGraph,small,cut⟩ := loc.raw_self_l hZFC tree.omega mn.2.1 ground
    (ρ.bound 19) (ρ.bound 24) L F (ρ.bound 0) X K R₁ (ρ.bound 21)
    c₁ d₁ Y S j₁ κ' mn root map numbers rankX height limitτ growth hτL hLδ
    source mx my ultra card strong crit.image bound
  obtain ⟨Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,c₂,P,R₂,j₂,q₂,p₂,cert⟩ := cut
  obtain ⟨ω₀,_,hω₀,above₀,regular₀,strong₀,_⟩ := td_round_woodin_l hN ρ valid
  have image₀ y : Rd_entry_d y X.val R ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k := by
    constructor
    · intro hy
      have hyΓ := (carrier y).mpr ⟨(mn.2.2.2 y X.val hy).1,hy⟩
      exact ⟨y,hyΓ,(idGraph y y).mpr ⟨hyΓ,rfl⟩⟩
    · rintro ⟨x,hx,hxy⟩
      exact ((idGraph x y).mp hxy).2 ▸ ((carrier x).mp hx).2
  have ownerLocal := it_local_short_l I mn.2.1 (kp_pair_l hN) native.1
    (loc.rank_absolute_l hN source.omega rankX height source.code)
  have nextCount := cert.power_l hZFC tree.omega root mn map mn.2.1 native
    X (ρ.bound 19) (ρ.bound 24) L F V X K j₁ (ρ.bound 21) numbers ownerLocal height.1 hLδ powerCount
    ω₀ (ρ.bound 21) (ρ.bound 21) X hω₀ above₀ regular₀ strong₀ rankX (fun _ h => h) image₀ powerCount
  have hκV := ZF.v_ordinal_mem_l (kp_pair_l hN) native rankV growth
  obtain ⟨hU,hE,hu,hq,hm',hb,hz,hσ⟩ :=
    td_round_native_scope_l native ρ valid rankV limitτ hκV
  have hτδ := height.1.transitive L hLδ (ρ.bound 0) hτL
  obtain ⟨mt',target,embed',fromRoot,rootGraph,_,_,l,W₂,Δ,g,common,_,smallW,Kκ,rankKκ,lowSquare,pool⟩ :=
    cert.demand_reply_l hZF tree.omega root mn.2.1 native rankX source height loc mx my ultra crit
      limitκ iU iE iu reply rankV limitτ hτδ hU hE hu rankW hDW hq hm' hb hz hσ
  obtain ⟨_,_,_,_,Dp,t,_,_,_,_,ft,restrict,endpoint,layer,_,_,pred,commute,
    ε,points,truth,nums,omegaPoint,hq',hn',hm'',cap⟩ := pool
  have square (x : N₀.Domain) (hx : N₀.mem x Kκ) (E) :
      Rd_entry_d x.val E g ↔ Rd_entry_d x.val E j₂ := by
    have hKX := ZF.v_mono_l (kp_pair_l hN) native rankKκ rankX
      (height.1.transitive (ρ.bound 24)
        (height.1.transitive L hLδ (ρ.bound 24) image.2.2.2.1))
    have ix := (idGraph x.val x.val).mpr ⟨(carrier x.val).mpr ⟨x.property,hKX x hx⟩,rfl⟩
    exact lowSquare x x.val E hx ix
  obtain ⟨vct,ict⟩ := Classical.axiomOfChoice
    (fun i : Fin 4 => embed'.1.1.2.2 (ctl.bound i).val (ctl.bound i).property)
  let ctl' : Env (smdl_structure_l I (R := R₂) mt'.2.1) 4 :=
    ⟨fun i => ⟨vct i,(ict i).1⟩,fun _ => ⟨vct 0,(ict 0).1⟩⟩
  obtain ⟨zt,numsTarget⟩ := nums
  have historyPoints : ∀ i : Fin 4,
      Rd_entry_d ([(ctl.bound 0).val,(ctl.bound 1).val,(ctl.bound 2).val,(ctl.bound 3).val].get i)
        ([(ctl'.bound 0).val,(ctl'.bound 1).val,(ctl'.bound 2).val,(ctl'.bound 3).val].get i) j₂ :=
    Fin.cases (ict 0).2 (Fin.cases (ict 1).2 (Fin.cases (ict 2).2
      (Fin.cases (ict 3).2 (fun i => Fin.elim0 i))))
  have roots : It_comp_d q j₂ q₂ := ⟨fromRoot.1.1.1.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨a,xa,ay⟩ => ⟨map.1.1.input_mem_of_pairMember xa,a,xa,ay⟩⟩⟩
  have nextArchive := archive.step_l hZF common tree.omega mn mt' embed' hN target.ext
    numbers numsTarget (ρ.bound 24) Kκ rankKκ image.2.2.2.1 archiveBound square roots historyPoints
  -- 实际施加证书同时指定新模型、原边、根图及可插入原树的活动步。
  have used := cert
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,mt,_,_,_,embed,rootMap,_,_,payload,active,certificate,rootGraph,
    _,_,_,_,_,_,_,_,_,_,_,_,tail⟩ := used
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := tail
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,build⟩ := rest
  obtain ⟨_,_,_,extend⟩ := build.2 root
  -- 填充边不改变原父模型；随后按同一证书把新超幂接到原节点 n。
  obtain ⟨θ,T₁,Q₁,G₁,E₁,c',j,succ,next,extension,old,node,edge,identity,_,noMove⟩ :=
    it_pad_l hZF tree hm
  have equal := tree.diagram.model_function.2 n c' c old qn
  subst c'
  have parent := extension.2.2.1 n c qn
  have oldRoot := (extension.2.2.2.1 o n q hm.predecessor_mem).mpr origin
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,next₂,extension₂,node₂,edge₂,move₂,root₂,preserve⟩ :=
    extend θ m T₁ Q₁ G₁ E₁ n o next succ node parent oldRoot
  have critical γ (lower : It_lower_d I γ N R (ρ.bound 24).val)
      (old : It_critical_bound_d I γ Q E) : It_critical_bound_d I γ Q₂ E₂ := by
    apply preserve γ lower
    apply extension.critical_bound_l I old
    rintro p κ L F hp ⟨s,⟨a,b,_,_,pair⟩,_⟩
    exact (noMove p hp a ((pair a).mpr (Or.inl rfl))).elim
  exact ⟨dep,tab,zero,depth,chosen,L,W,X,K,R₁,F,c₁,d₁,Y,S,j₁,κ',U',E',u',
    image,cofinal,V,Γ,k,rankV,carrier,idGraph,small,
    Ls,Js,Os,Zs,Ds,ps,Vs,Ws,qs,c₂,P,R₂,j₂,q₂,p₂,cert,certificate root,embed,rootMap,rootGraph,payload,active,
    mt',l,W₂,Δ,g,Dp,t,common,smallW,ft,restrict,endpoint,layer,pred,commute,
    ε,points,truth,⟨zt,numsTarget⟩,omegaPoint,hq',hn',hm'',cap,Kκ,rankKκ,square,
    ctl',zt,fun i => (ict i).2,numsTarget,nextArchive,
    θ,T₁,Q₁,G₁,E₁,j,succ,next,extension,node,edge,identity,noMove,
    θ₂,T₂,Q₂,G₂,E₂,next₂,extension₂,node₂,edge₂,move₂,root₂,critical,nextCount⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 重置请求的完整原生回合

已发重置请求先产生同一原生回合，再施加恒等填充边与扩展器后继；
请求沿同一实际原边整体搬运，回答槽与请求槽逐项识别。根切片推进后，
同一回答对每个实数输入产生下一请求和精确追加的档案。枚举由内部字母
编码与幂集计数实际构造，不要求整个当前模型可数。两项不变量沿同一原边
保持至下一请求；新档案行同时保存源编码、计数与支撑上界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} {Ar Sr : M.Domain} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原重置一次选定两条树边及回答；随后对每个实数落子登记同一原回合。 -/
theorem td_raw_reset_l
    {Ω c₀ X₀ R₀ n m T Q G E o cN N R qN zn Da D₀ : M.Domain}
    (root : Zc_model_d I Ω c₀ X₀ R₀)
    (tree : It_tree_d hZF Ω c₀ m T Q G E) (owned : It_owned_d I Ω Q E) (hm : M.SuccessorOf m n)
    (qr : Rd_entry_d o c₀ Q) (qn : Rd_entry_d n cN Q)
    (mn : Smdl_d I cN N R) (origin : It_map_d G o n qN)
    (ι : Env (smdl_structure_l I (R := R) mn.2.1) 47)
    (issued : Formula.satisfies ι td_issued0_m)
    (lettersRoot : Rd_entry_d Ar (ι.bound 6).val qN)
    (treeRoot : Rd_entry_d Sr (ι.bound 7).val qN)
    (control : Formula.satisfies (ι.reindex (fun i : Fin 19 => i.castAdd 28))
      (td_reset_control_m (tg_control_params_d Term.bound)))
    (reset : ι.bound 23 = ι.bound 1)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    {U₁ U₂ z χn : (smdl_structure_l I (R := R) mn.2.1).Domain}
    (treeS : Td_tree_d (kp_pair_l hN) (ι.bound 0) (ι.bound 6) (ι.bound 7))
    (alphabet : Td_alphabet_d (ι.bound 7) U₁ U₂)
    (chosen : (smdl_structure_l I (R := R) mn.2.1).mem z U₁)
    (hχ : (smdl_structure_l I (R := R) mn.2.1).mem χn (ι.bound 5))
    (separated : Td_separated_d (ι.bound 7))
    (numbers : Rr_layer_d I Ω N R (ι.bound 0).val zn)
    (archive : Td_archive_d I Ω c₀ X₀ Ar Sr Da N R χn.val
      (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val zn (ι.bound 20).val D₀ qN)
    (treeLinks : Td_archive_links_d o Q G E Da)
    (archiveBound : Rd_entry_d χn.val (ι.bound 24).val R)
    {wr zr γ₀ C₀ C γ Vγ tγ mA : M.Domain}
    (rootNumbers : Rr_layer_d I Ω X₀ R₀ wr zr)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C qN γ Vγ tγ)
    (below : ∀ x, Rd_entry_d x γ R → Rd_entry_d x (ι.bound 24).val R)
    (omegaLow : Rd_entry_d (ι.bound 0).val Vγ R)
    (lettersLow : Rd_entry_d (ι.bound 6).val Vγ R)
    (alphabetCode : Td_code_d I N R (ι.bound 7).val (ι.bound 5).val)
    (powerCount : Pc_count_d I Ω N R (ι.bound 5).val)
    (hmA : M.mem mA Ω) (sequence : M.IsSequenceOfLength I Da mA)
    (index : Rd_entry_d mA (ι.bound 19).val zn) :
    ∃ θ T₁ Q₁ G₁ E₁ j θ₂ T₂ Q₂ G₂ E₂ c₂ P R₂ j₂ q₂ p₂,
      M.SuccessorOf θ m ∧ It_tree_d hZF Ω c₀ θ T₁ Q₁ G₁ E₁ ∧
      It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m cN Q₁ ∧ It_map_d G₁ n m j ∧
      (∀ x y, Rd_entry_d x y j → x = y) ∧
      It_tree_d hZF Ω c₀ θ₂ T₂ Q₂ G₂ E₂ ∧
      It_owned_d I Ω Q₂ E₂ ∧
      It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂ ∧
      Rd_entry_d θ c₂ Q₂ ∧ It_map_d G₂ n θ j₂ ∧ Rd_entry_d m p₂ E₂ ∧ It_map_d G₂ o θ q₂ ∧
      (∀ β, It_lower_d I β N R (ι.bound 24).val → It_critical_bound_d I β Q E →
        It_critical_bound_d I β Q₂ E₂) ∧
      (Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E →
        Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂) ∧
    ∃ mt : Smdl_d I c₂ P R₂, ∃ target : Zc_model_d I Ω c₂ P R₂,
      Smap_d I Ω cN c₂ N P j₂ ∧ Smap_d I Ω c₀ c₂ X₀ P q₂ ∧
      It_comp_d qN j₂ q₂ ∧
    ∃ C' γ' Vγ' tγ' l zt,
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P R₂ C' q₂ γ' Vγ' tγ' ∧ Rd_entry_d γ' l R₂ ∧
      Ic_round_d hZF Ω (fun i => [n,m,T,Q,G,E,N,R,χn.val].get i)
        (fun i => [θ,θ₂,T₂,Q₂,G₂,E₂,P,R₂,l].get i) ∧
    ∃ ι' : Env (smdl_structure_l I (R := R₂) mt.2.1) 47,
    ∃ ε : Env (smdl_structure_l I (R := R₂) mt.2.1) 23,
      (∀ i, Rd_entry_d (ι.bound i).val (ι'.bound i).val j₂) ∧
      Formula.satisfies ι' td_issued0_m ∧ Formula.satisfies ε td_reply0_m ∧
      Td_reply_link_d Eq ι'.bound ε.bound ∧
      Rd_entry_d Ar (ι'.bound 6).val q₂ ∧ Rd_entry_d Sr (ι'.bound 7).val q₂ ∧
      Rr_layer_d I Ω P R₂ (ι'.bound 0).val zt ∧
      Rd_entry_d (ι'.bound 0).val Vγ' R₂ ∧ Rd_entry_d (ι'.bound 6).val Vγ' R₂ ∧
    ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x (ι.bound 6) →
    let Pn := smdl_structure_l I (R := R₂) mt.2.1
    let hP := ZF.modelsKP (ZFC.models_zf_l (target.native_l I hZF tree.omega))
    ∃ a y b h t : Pn.Domain, ∃ ψ : Env Pn 47, ∃ m' Da' r, ∃ s : Td_archive_row_d M.Domain,
      Rd_entry_d x.val a.val j₂ ∧ Pn.mem y (ι'.bound 6) ∧
      (Gm_even_d (kp_pair_l hP) (ι'.bound 0) (ι'.bound 19) → y = a) ∧
      (¬ Gm_even_d (kp_pair_l hP) (ι'.bound 0) (ι'.bound 19) → Rd_entry_d h y (ι'.bound 17)) ∧
      KPair_d Pn b (ε.bound 5) (ε.bound 10) ∧
      Fseq_end_d (kp_pair_l hP) (ι'.bound 0) h (ι'.bound 20) b ∧
      Fseq_end_d (kp_pair_l hP) (ι'.bound 0) t h y ∧
      Fseq_end_d (kp_pair_l hP) (ι'.bound 0) (ψ.bound 20) t (ψ.bound 21) ∧
      Rd_entry_d t (ψ.bound 21) (ι'.bound 17) ∧
      (∀ i : Fin 19, ψ.bound (i.castAdd 28) = ι'.bound (i.castAdd 28)) ∧
      Formula.satisfies ψ td_issued0_m ∧
      Rd_entry_d Ar (ψ.bound 6).val q₂ ∧ Rd_entry_d Sr (ψ.bound 7).val q₂ ∧
      M.mem m' Ω ∧ M.SuccessorOf m' mA ∧ M.IsSequenceOfLength I Da' m' ∧
      (∀ k s, Rd_entry_d k s Da' ↔ Rd_entry_d k s Da ∨ k = mA ∧ s = r) ∧
      Rt_tuple_d s.values_d r ∧ s.i = m ∧ s.c = cN ∧ s.X = N ∧ s.R = R ∧ s.p = qN ∧
      (∀ x, ¬ M.mem x s.depth) ∧ s.v 47 = U₁.val ∧ s.v 49 = z.val ∧
      Rd_entry_d m' (ψ.bound 19).val zt ∧ Pn.mem (ι'.bound 24) (ψ.bound 24) ∧
      Rd_entry_d l (ψ.bound 24).val R₂ ∧ Pn.MemberSubset h (ψ.bound 20) ∧
      Td_archive_d I Ω c₀ X₀ Ar Sr Da' P R₂ l
        (ψ.bound 4).val (ψ.bound 1).val (ψ.bound 2).val zt (ψ.bound 20).val D₀ q₂ ∧
      Td_archive_links_d o Q₂ G₂ E₂ Da' ∧
      Td_rank_step_d (N := smdl_structure_l I (R := R) mn.2.1) (P := Pn)
        (fun x y => Rd_entry_d x.val y.val j₂) ι.bound ψ.bound ∧
      Pc_count_d I Ω P R₂ (ψ.bound 5).val ∧
      Td_code_d I P R₂ (ψ.bound 7).val (ψ.bound 5).val := by
  have map := tree.diagram.elementary o n qN c₀ X₀ R₀ cN N R origin qr qn root.model mn
  have ground := (root.map_l hZF tree.omega mn map).native_l I hZF tree.omega
  obtain ⟨ξ,seed,hξχ,low,mid,ρ,hρ,round,hU₁,_,hz₁⟩ :=
    td_issued_reset_l ground ι issued control reset treeS alphabet chosen hχ separated
  let ctl : Env (smdl_structure_l I (R := R) mn.2.1) 4 :=
    ⟨fun i => [ι.bound 4,ι.bound 1,ι.bound 2,ι.bound 20].get i,fun _ => ι.bound 4⟩
  have hρ0 : ρ.bound 19 = ι.bound 0 := (hρ 0).trans (low 0)
  have hρ24 : ρ.bound 24 = ι.bound 24 := (hρ 5).trans (mid 2)
  have hρ21 : ρ.bound 21 = ι.bound 5 := (hρ 2).trans (low 2)
  have countρ : Pc_count_d I Ω N R (ρ.bound 21).val := (congrArg Subtype.val hρ21).symm ▸ powerCount
  have codeρ : Td_code_d I N R (ρ.bound 22).val (ρ.bound 21).val :=
    (congrArg Subtype.val ((hρ 3).trans (low 3))).symm ▸
      (congrArg Subtype.val hρ21).symm ▸ alphabetCode
  have numsρ : Rr_layer_d I Ω N R (ρ.bound 19).val zn :=
    (congrArg Subtype.val hρ0).symm ▸ numbers
  have boundρ : Rd_entry_d χn.val (ρ.bound 24).val R :=
    (congrArg Subtype.val hρ24).symm ▸ archiveBound
  have out := td_reset_tree_l hZFC root tree hm qr qn mn origin ρ round
    numsρ ctl archive boundρ countρ
  obtain ⟨dep,tab,zero,depth,chosen',out⟩ := out
  obtain ⟨L,W,X,K,R₁,F,c₁,d₁,Y,S,j₁,κ',U',E',u',image,cofinal,out⟩ := out
  obtain ⟨V,Γ,k,rankV,carrierΓ,idGraph,smallX,out⟩ := out
  obtain ⟨_,_,_,_,_,_,_,_,_,c₂,P,R₂,j₂,q₂,p₂,cert,targetP,embed,rootMap,rootGraph,payload,_,out⟩ := out
  obtain ⟨mt,l,W₂,Δ,g,Dp,t,common,smallW,ft,restrict,_,_,pred,commute,out⟩ := out
  obtain ⟨ε,points,truth,_,_,_,_,_,cap,Kκ,rankKκ,lowSquare,out⟩ := out
  obtain ⟨ctl',zt,ictl,numsTarget,nextArchive,out⟩ := out
  obtain ⟨θ,T₁,Q₁,G₁,E₁,j,succ,next,extension,node,edge,identity,noMove,out⟩ := out
  obtain ⟨θ₂,T₂,Q₂,G₂,E₂,next₂,extension₂,node₂,edge₂,move₂,root₂,critical,nextCount⟩ := out
  have treeLinks' := (treeLinks.extend_l hZF tree extension).extend_l hZF next extension₂
  have rootAt : It_map_d G₁ o m qN := by
    have origin' := (extension.2.2.2.1 o n qN hm.predecessor_mem).mpr origin
    have pad := next.diagram.elementary n m j cN N R cN N R edge
      (extension.2.2.1 n cN qn) node mn mn
    obtain ⟨q,leg⟩ := next.diagram.map_l hZF
      ((extension.2.1 o m).mpr (Or.inr ⟨rfl,Or.inr (tree.diagram.map_bound_l hZF origin)⟩))
    have embed := next.diagram.elementary o m q c₀ X₀ R₀ cN N R leg
      (extension.2.2.1 o c₀ qr) node root.model mn
    have keep x y (xy : Rd_entry_d x y qN) : Rd_entry_d x y q := by
      obtain ⟨v,_,yv⟩ := pad.1.1.2.2 y (map.1.1.output_mem_of_pairMember xy)
      exact next.diagram.comp o n m qN j q origin' edge leg x y y xy
        ((identity y v yv).symm ▸ yv)
    have same x y : Rd_entry_d x y q ↔ Rd_entry_d x y qN := by
      refine ⟨fun xy => ?_,keep x y⟩
      obtain ⟨v,_,xv⟩ := map.1.1.2.2 x (embed.1.1.input_mem_of_pairMember xy)
      exact embed.1.1.1.2 x v y (keep x v xv) xy ▸ xv
    exact (embed.1.1.1.1.eq_of_pairMember_iff hZF.1 map.1.1.1.1 same) ▸ leg
  have native := ZFC.models_zf_l ground
  have rawCritical (old : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E) :
      Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q₂ G₂ E₂ := by
    have kept := extension.raw_critical_pad_l I
      (fun i c hi => (tree.diagram.model_domain i).mpr ⟨c,hi⟩) old noMove
    exact extension₂.raw_critical_apply_l I (ZF.modelsKP hZF)
      (fun i c hi => (next.diagram.model_domain i).mpr ⟨c,hi⟩) kept next₂.move_function move₂ payload
      (extension₂.2.2.1 m cN node) mn
      ((extension₂.2.2.2.1 o m qN succ.predecessor_mem).mpr rootAt) slice
      (fun x hx => (congrArg Subtype.val hρ24).symm ▸ below x hx)
  have nativeP := ZFC.models_zf_l (targetP.native_l I hZF tree.omega)
  have hP := ZF.modelsKP nativeP
  have data := image
  obtain ⟨rankX,source,hLδ,hκL,hτL,rankW,hDW,loc,card,strong,mx,my,ultra,crit,bound,
    limitκ,iU,iE,iu,_,reply⟩ := data
  have height := (td_round_native_l (ZF.modelsKP native) ρ round).2.1
  have quality := it_owner_l I mn (ZF.modelsKP native) (ρ.bound 19) (ρ.bound 24) L F
    (ρ.bound 21) X K R₁ numsρ rankX height source loc card strong
  have owned₂ := extension₂.owned_apply_l I (extension.owned_pad_l I owned noMove)
    next₂.move_function.2 move₂ payload (extension₂.2.2.1 m cN node) quality
  have copy := td_copy_reset_l hZFC tree hm mn qn (ZF.modelsKP native)
    (ρ.bound 19) (ρ.bound 24) L F V X K j₁ (ρ.bound 21) R₁ cert
      numsρ source rankX height loc quality idGraph smallX common
      ((loc.ordinals_l (ZF.modelsKP native) source.transitive source.code).2.transitive
        (ρ.bound 24) hκL χn boundρ)
      next extension noMove node next₂ extension₂ node₂ edge₂ move₂ payload
  have limitτ := (td_round_native_l (ZF.modelsKP native) ρ round).2.2.1
  have growth := (td_round_native_l (ZF.modelsKP native) ρ round).2.2.2.1
  have hκV := ZF.v_ordinal_mem_l (kp_pair_l (ZF.modelsKP native)) native rankV growth
  obtain ⟨hU,hE,hu,hq,hm',hb,hz,hσ⟩ := td_round_native_scope_l native ρ round rankV limitτ hκV
  have elementary := ultra.elementary_l native mx.1 my.1
  have transTarget := ultra.transitive_l native my.1
  have natural := elementary.natural_l native source.omega source.transitive transTarget mx my
    source.omega_mem
  have omegaFixed := elementary.omega_l (kp_pair_l (ZF.modelsKP native)) native source.omega
    source.transitive transTarget mx my source.omega_mem
  let N₀ := smdl_structure_l I (R := R) mn.2.1
  have hVX : N₀.MemberSubset V X :=
    ZF.v_mono_l (kp_pair_l (ZF.modelsKP native)) native rankV rankX
      (height.1.transitive (ρ.bound 0) (height.1.transitive L hLδ (ρ.bound 0) hτL))
  have carry (x y : N₀.Domain) (E : M.Domain) (hx : N₀.mem x V)
      (xy : Rd_entry_d x y j₁) (value : Rd_entry_d y.val E t) : Rd_entry_d x.val E j₂ :=
    (commute x y x.val E hx xy ((idGraph x.val x.val).mpr
      ⟨(carrierΓ x.val).mpr ⟨x.property,hVX x hx⟩,rfl⟩)).mp value
  have sourceSeed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at sourceSeed
  have language := sourceSeed.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [ee_language_m,Formula.satisfies_bind,ee_language0_m,Formula.satisfies_conj_iff,
    ee_domain_pack_m,ee_domain_pack0_m,Formula.satisfies_mem_iff] at language
  have ωU : N₀.mem (ρ.bound 19) (ρ.bound 35) := language.1.1
  have ωV := (v_transitive_l (kp_pair_l (ZF.modelsKP native)) rankV) _ hU _ ωU
  have sourceRound := ((Formula.satisfies_conj_iff ..).mp round).2
  simp only [td_witness0_m,td_round_m,Formula.satisfies_conj_iff] at sourceRound
  have record := (td_record_sat_l (kp_pair_l (ZF.modelsKP native)) native.1 ..).mp
    sourceRound.2.2.2.2.2.2.2.2.2.2.1
  have hnN := source.omega.transitive (ZF.modelsKP native) (ρ.bound 9) hm' (ρ.bound 28)
    record.height_end.predecessor_mem
  have carryNat (x : N₀.Domain) (E : M.Domain) (hx : N₀.mem x (ρ.bound 19))
      (value : Rd_entry_d x.val E t) : Rd_entry_d x.val E j₂ :=
    carry x x E ((v_transitive_l (kp_pair_l (ZF.modelsKP native)) rankV) _ ωV x hx)
      (natural x hx) value
  have conv {a b : N₀.Domain} (h : a = b) {E : M.Domain}
      (v : Rd_entry_d a.val E j₂) : Rd_entry_d b.val E j₂ := h ▸ v
  have pw := conv hρ0 (carry (ρ.bound 19) (ρ.bound 19) _ ωV omegaFixed (points 0))
  have pq := conv ((hρ 8).trans (mid 3)) (carryNat (ρ.bound 27) _ hq (points 1))
  have pn := conv ((hρ 9).trans (mid 4)) (carryNat (ρ.bound 28) _ hnN (points 2))
  have pk := conv hρ24 (carry (ρ.bound 24) κ' _ hκV crit.image (points 4))
  have pU := conv ((hρ 16).trans (mid 6)) (carry (ρ.bound 35) U' _ hU iU (points 6))
  have pE := conv ((hρ 17).trans (mid 7)) (carry (ρ.bound 36) E' _ hE iE (points 7))
  have pu := conv ((hρ 19).trans (mid 5)) (carry (ρ.bound 38) u' _ hu iu (points 9))
  have pb := conv ((hρ 21).trans (mid 8)) (carryNat (ρ.bound 40) _ hb (points 11))
  have pz := conv ((hρ 23).trans (mid 9)) (carryNat (ρ.bound 42) _ hz (points 12))
  have ps (i : Fin 7) : Rd_entry_d (ι.bound ⟨39+i.val,by omega⟩).val
      (ε.bound ⟨16+i.val,by omega⟩).val j₂ := by
    match i with
    | ⟨0,_⟩ => exact conv ((hρ 36).trans (mid 10)) (carryNat (ρ.bound 55) _ (hσ 0) (points 16))
    | ⟨1,_⟩ => exact conv ((hρ 37).trans (mid 11)) (carryNat (ρ.bound 56) _ (hσ 1) (points 17))
    | ⟨2,_⟩ => exact conv ((hρ 38).trans (mid 12)) (carryNat (ρ.bound 57) _ (hσ 2) (points 18))
    | ⟨3,_⟩ => exact conv ((hρ 39).trans (mid 13)) (carryNat (ρ.bound 58) _ (hσ 3) (points 19))
    | ⟨4,_⟩ => exact conv ((hρ 40).trans (mid 14)) (carryNat (ρ.bound 59) _ (hσ 4) (points 20))
    | ⟨5,_⟩ => exact conv ((hρ 41).trans (mid 15)) (carryNat (ρ.bound 60) _ (hσ 5) (points 21))
    | ⟨6,_⟩ => exact conv ((hρ 42).trans (mid 16)) (carryNat (ρ.bound 61) _ (hσ 6) (points 22))
  obtain ⟨vι,iι⟩ := Classical.axiomOfChoice
    (fun i : Fin 47 => embed.1.1.2.2 (ι.bound i).val (ι.bound i).property)
  let ι' : Env (smdl_structure_l I (R := R₂) mt.2.1) 47 :=
    ⟨fun i => ⟨vι i,(iι i).1⟩,fun _ => ⟨vι 0,(iι 0).1⟩⟩
  have issued' : Formula.satisfies ι' td_issued0_m :=
    (smap_source_l I hZF tree.omega mn mt embed td_issued0_m td_issued0_closed_l
      ι ι' (fun i => (iι i).2)).mp issued
  let Pn := smdl_structure_l I (R := R₂) mt.2.1
  have align {i : Fin 47} {y : Pn.Domain}
      (h : Rd_entry_d (ι.bound i).val y.val j₂) : ι'.bound i = y :=
    Subtype.ext (embed.1.1.1.2 _ _ _ (iι i).2 h)
  have eqn : ι'.bound 28 = ε.bound 2 := align pn
  -- 两个回答元数由完整池图保持同一后继关系，从而唯一识别。
  have sm : Pn.SuccessorOf (ε.bound 3) (ε.bound 2) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a,ha,ia⟩ := (pred _ _ (points 3) x.val).mp hx
      let aN : N₀.Domain := ⟨a,(mn.2.2.2 a (ρ.bound 9).val ha).1⟩
      rcases (record.height_end aN).mp ha with h | eq
      · exact Or.inl ((pred _ _ (points 2) x.val).mpr ⟨a,h,ia⟩)
      · have eq : aN = ρ.bound 28 := native.1.eq_of_same_members _ _ eq
        have ex : x = ε.bound 2 :=
          Subtype.ext (ft.1.1.2 _ _ _ (congrArg Subtype.val eq ▸ ia) (points 2))
        exact Or.inr (fun y => ex ▸ Iff.rfl)
    · rintro (hx | eq)
      · obtain ⟨a,ha,ia⟩ := (pred _ _ (points 2) x.val).mp hx
        exact (pred _ _ (points 3) x.val).mpr
          ⟨a,(record.height_end ⟨a,(mn.2.2.2 a (ρ.bound 28).val ha).1⟩).mpr (Or.inl ha),ia⟩
      · have ex : x = ε.bound 2 := nativeP.1.eq_of_same_members _ _ eq
        subst x
        exact (pred _ _ (points 3) (ε.bound 2).val).mpr
          ⟨(ρ.bound 28).val,record.height_end.predecessor_mem,points 2⟩
  have targetState := td_issued_read_l (kp_pair_l hP) nativeP.1 ι' issued'
  have sm' : Pn.SuccessorOf (ι'.bound 29) (ε.bound 2) := eqn ▸ targetState.payload.2.2.2.1.2.2.2
  have eqm : ι'.bound 29 = ε.bound 3 := sm'.eq nativeP.1 sm
  have links : Td_reply_link_d Eq ι'.bound ε.bound :=
    Fin.cases (align pw) (Fin.cases (align pq) (Fin.cases eqn (Fin.cases eqm
      (Fin.cases (align pk) (Fin.cases (align pU) (Fin.cases (align pE)
        (Fin.cases (align pu) (Fin.cases (align pb) (Fin.cases (align pz)
          (Fin.cases (align (ps 0)) (Fin.cases (align (ps 1)) (Fin.cases (align (ps 2))
            (Fin.cases (align (ps 3)) (Fin.cases (align (ps 4)) (Fin.cases (align (ps 5))
              (Fin.cases (align (ps 6)) (fun i => Fin.elim0 i)))))))))))))))))
  -- 根切片沿本次低秩方块推进；保留同一根图，而不另选模型或解释。
  have roots : It_comp_d qN j₂ q₂ := ⟨rootMap.1.1.1.1,fun x y => (rootGraph x y).trans
    ⟨And.right,fun ⟨v,xv,vy⟩ => ⟨map.1.1.input_mem_of_pairMember xv,v,xv,vy⟩⟩⟩
  obtain ⟨C',_,iC⟩ := embed.1.1.2.2 C (map.1.1.output_mem_of_pairMember slice.context)
  have belowρ : ∀ x, Rd_entry_d x γ R → Rd_entry_d x (ρ.bound 24).val R :=
    fun x hx => (congrArg Subtype.val hρ24).symm ▸ below x hx
  obtain ⟨γ',Vγ',tγ',iγ,iV,comp,slice',high,square⟩ :=
    slice.step_l hZF common mn mt (ZF.modelsKP native) hP
      (ρ.bound 24) Kκ rankKκ image.2.2.2.1 belowρ lowSquare map.1.1.1 roots iC
  have rankγ := (rr_rank_native_l I mn.2.1 (ZF.modelsKP native)
    ⟨γ,slice.rank.1⟩ ⟨Vγ,slice.rank.2.1⟩).mp slice.rank
  have sub : N₀.MemberSubset ⟨Vγ,slice.rank.2.1⟩ Kκ :=
    (KP.v_compare_l (ZF.modelsKP native) rankγ rankKκ (fun x hx => belowρ x.val hx)).1
  have keep (i : Fin 47) (hx : N₀.mem (ι.bound i) Kκ) :
      Rd_entry_d (ι.bound i).val (ι'.bound i).val g :=
    (lowSquare (ι.bound i) hx _).mpr (iι i).2
  have wK : N₀.mem (ι.bound 0) Kκ := sub _ omegaLow
  have aK : N₀.mem (ι.bound 6) Kκ := sub _ lettersLow
  have wLow : Rd_entry_d (ι'.bound 0).val Vγ' R₂ :=
    (common.pred Vγ Vγ' iV _).mpr ⟨_,omegaLow,keep 0 wK⟩
  have aLow : Rd_entry_d (ι'.bound 6).val Vγ' R₂ :=
    (common.pred Vγ Vγ' iV _).mpr ⟨_,lettersLow,keep 6 aK⟩
  -- 空标签、当前标签和实数字母域都使用共同图的同一限制。
  have state := td_issued_read_l (kp_pair_l (ZF.modelsKP native)) native.1 ι issued
  have finite (i : Fin 47) (hi : N₀.mem (ι.bound i) (ι.bound 0)) :
      Rd_entry_d (ι.bound i).val (ι'.bound i).val t :=
    ((restrict.2 _ _).mp (keep i ((v_transitive_l (kp_pair_l (ZF.modelsKP native)) rankKκ)
      _ wK _ hi))).2
  have names : ∀ i : Fin 3, Rd_entry_d (ρ.bound ([20,25,50].get i)).val
      (ι'.bound ([1,23,6].get i)).val t :=
    Fin.cases ((congrArg Subtype.val ((hρ 1).trans (low 1))).symm ▸
      finite 1 (reset ▸ state.payload.2.1))
      (Fin.cases ((congrArg Subtype.val ((hρ 6).trans (mid 1))).symm ▸
        finite 23 state.payload.2.1)
        (Fin.cases ((congrArg Subtype.val ((hρ 31).trans (low 5))).symm ▸
          ((restrict.2 _ _).mp (keep 6 aK)).2) (fun i => Fin.elim0 i)))
  have pts : ∀ i : Fin 5, Rd_entry_d (ρ.bound ([19,0,9,3,4].get i)).val
      (ε.bound ([0,5,3,8,10].get i)).val t :=
    Fin.cases (points 0) (Fin.cases (points 5) (Fin.cases (points 3)
      (Fin.cases (points 8) (Fin.cases (points 10) (fun i => Fin.elim0 i)))))
  have nums : Rr_layer_d I Ω P R₂ (ι'.bound 0).val zt :=
    (congrArg Subtype.val (links 0)).symm ▸ numsTarget
  have ct (i : Fin 4) : (ctl'.bound i).val =
      (ι'.bound ([4,1,2,20].get i)).val :=
    embed.1.1.1.2 _ _ _ (ictl i) (by
      match i with
      | ⟨0,_⟩ => exact (iι 4).2
      | ⟨1,_⟩ => exact (iι 1).2
      | ⟨2,_⟩ => exact (iι 2).2
      | ⟨3,_⟩ => exact (iι 20).2)
  have old : Td_archive_d I Ω c₀ X₀ Ar Sr Da P R₂ l
      (ι'.bound 4).val (ι'.bound 1).val (ι'.bound 2).val zt (ι'.bound 20).val D₀ q₂ :=
    ct 0 ▸ ct 1 ▸ ct 2 ▸ ct 3 ▸ nextArchive
  obtain ⟨k,hk,ik⟩ := nums.injection.1.2.2 mA hmA
  have naturalMap := (numbers.omega_map_l I hZF tree.omega mn mt embed
    (root.map_l hZF tree.omega mn map).ext targetP.ext nums).2
  have eqk := embed.1.1.1.2 _ _ _ (naturalMap mA _ _ index ik) (iι 19).2
  have index' : Rd_entry_d mA (ι'.bound 19).val zt := by
    change Rd_entry_d mA (vι 19) zt
    exact eqk ▸ ik
  -- 根切片低于候选，而新类型严格高于候选；此事实随原行永久保存。
  obtain ⟨rankτ,_⟩ := td_round_letters_l native ρ round
  have subτ : N₀.MemberSubset ⟨Vγ,slice.rank.2.1⟩ (ρ.bound 1) :=
    (KP.v_compare_l (ZF.modelsKP native) rankγ rankτ
      (fun x hx => limitτ.1.transitive (ρ.bound 24) growth x (belowρ x.val hx))).1
  have rootLow a x (ha : M.mem a D₀) (ax : Rd_entry_d a x qN) :
      Rd_entry_d x (ρ.bound 1).val R := by
    obtain ⟨y,hy,ay⟩ := slice.injection.1.2.2 a ha
    have eq := map.1.1.1.2 a y x (slice.root a y ay) ax
    exact eq ▸ subτ ⟨y,hy⟩ ((slice.image y).mpr ⟨a,ha,ay⟩)
  have lettersRoot' : Rd_entry_d Ar (ι'.bound 6).val q₂ :=
    (roots.2 _ _).mpr ⟨_,lettersRoot,(iι 6).2⟩
  have treeRoot' : Rd_entry_d Sr (ι'.bound 7).val q₂ :=
    (roots.2 _ _).mpr ⟨_,treeRoot,(iι 7).2⟩
  have roundLetters : Rd_entry_d Ar (ρ.bound 50).val qN :=
    (congrArg Subtype.val ((hρ 31).trans (low 5))).symm ▸ lettersRoot
  have roundTree : Rd_entry_d Sr (ρ.bound 22).val qN :=
    (congrArg Subtype.val ((hρ 3).trans (low 3))).symm ▸ treeRoot
  have zeroReal : ρ.bound 25 = ρ.bound 20 :=
    ((hρ 6).trans (mid 1)).trans (reset.trans ((hρ 1).trans (low 1)).symm)
  have realEmpty := td_round_real_empty_l (ZF.modelsKP native) ρ round zeroReal
  have realPoint : Rd_entry_d (ρ.bound 44).val (ι'.bound 1).val g :=
    (congrArg Subtype.val (realEmpty.trans ((hρ 1).trans (low 1)))).symm ▸
      keep 1 ((v_transitive_l (kp_pair_l (ZF.modelsKP native)) rankKκ) _ wK _ (reset ▸ state.payload.2.1))
  have controlP := (td_issued_sat_l (kp_pair_l hP) nativeP.1 ι').mp issued' |>.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at controlP
  have rulesP := (td_rules_sat_l nativeP ..).mp controlP.2.2.1
  let realEnv : Env Pn 4 := ⟨fun i => [ι'.bound 4,ι'.bound 2,ι'.bound 20,ι'.bound 1].get i,ι'.free⟩
  have realPlay : Td_play_at_d I P R₂ (ι'.bound 4).val (ι'.bound 2).val (ι'.bound 20).val (ι'.bound 1).val :=
    (td_play_native_l I mt.2.1 hP realEnv).mpr ⟨ι'.bound 3,rulesP.two,fun _ _ ⟨p,_,hp⟩ => (rulesP.empty p hp).elim⟩
  refine ⟨θ,T₁,Q₁,G₁,E₁,j,θ₂,T₂,Q₂,G₂,E₂,c₂,P,R₂,j₂,q₂,p₂,
    succ,next,extension,node,edge,identity,next₂,owned₂,extension₂,node₂,edge₂,move₂,root₂,
    (fun β hβ h => critical β ((congrArg Subtype.val hρ24).symm ▸ hβ) h),
    rawCritical,
    mt,targetP,embed,rootMap,roots,C',γ',Vγ',tγ',l,zt,slice',high,copy,
    ι',ε,(fun i => (iι i).2),issued',truth,links,lettersRoot',treeRoot',nums,wLow,aLow,?_⟩
  -- 工厂先于落子固定；每个输入只执行回答后的原策略及两次历史追加。
  intro x hx
  dsimp only
  obtain ⟨a,ha,xa⟩ := embed.1.1.2.2 x.val x.property
  let a' : Pn.Domain := ⟨a,ha⟩
  have ha' : Pn.mem a' (ι'.bound 6) :=
    (embed.relation_l I hZF tree.omega mn mt xa (iι 6).2).mp hx
  obtain ⟨b,h,k,m',Da',r,En,pair,ending,_,_,_,_,_,hm',sm,seq,tuple,append,
    y,t',ψ,hy,even,odd,digit,aux,value,head,_,valid,indexNext,increase,boundNext,history,archive'⟩ :=
    Td_archive_d.finish_round_l hZF (i := m) tree.omega root mn mt map rootMap rootNumbers ρ round
      rootLow roundLetters roundTree depth chosen' codeρ countρ hLδ ι' issued' ε truth links numsρ nums
      common hτL smallW cofinal ft restrict pred pts names cap slice' square wLow aLow
      hmA sequence index' old ⟨(ι'.bound 1).val,realPoint,realPlay⟩ a' ha'
  exact ⟨a',y,b,h,t',ψ,m',Da',r,
    ⟨fun i => (ρ.bound i).val,m,cN,N,R,qN,L.val,W.val,zn,dep,tab,En⟩,
    xa,hy,even,odd,pair,ending,digit,aux,value,head,valid,
    (congrArg Subtype.val (head 6)).symm ▸ lettersRoot',
    (congrArg Subtype.val (head 7)).symm ▸ treeRoot',
    hm',sm,seq,append,tuple,rfl,rfl,rfl,rfl,rfl,zero,
    congrArg Subtype.val hU₁,congrArg Subtype.val hz₁,
    indexNext,increase,boundNext,history,archive',
    treeLinks'.push_l tuple (extension₂.2.2.1 m cN node)
      ((extension₂.2.2.2.1 o m qN succ.predecessor_mem).mpr rootAt) move₂ payload append,
    Smap_d.demand_rank_step_l hZF tree.omega mn mt embed (ZF.modelsKP native) hP
      ι issued ι' ψ (fun i => (iι i).2) head valid ending history,
    (congrArg Subtype.val (head 5)).symm ▸ nextCount (ι'.bound 5).val
      ((congrArg Subtype.val hρ21).symm ▸ (iι 5).2),
    (congrArg Subtype.val (head 7)).symm ▸ (congrArg Subtype.val (head 5)).symm ▸
      alphabetCode.map_l hZF tree.omega mn mt embed (iι 7).2 (iι 5).2⟩

end YesMetaZFC.SetTheory.LargeCardinal
