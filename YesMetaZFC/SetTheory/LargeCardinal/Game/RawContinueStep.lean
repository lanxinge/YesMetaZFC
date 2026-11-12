import YesMetaZFC.SetTheory.LargeCardinal.Game.PreparedResult
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRootContinueStep
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical

/-! # 固定继续工厂的第一次原树延伸

输入来自同一次原继续选择及其 subtype。完整代表池先与 subtype 已选图
逐点识别，再追加证书中的原活动边和支撑。新共同图从当前所属模型出发，
实际嵌入从旧档案模型出发；根切片经逆图方块推进，不构造所属模型的全嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 固定 cert 与已恢复 subtype 共用原目标、代表池、活动边及新根切片。 -/
theorem Er_rank_cut_at_d.continue_step_l
    {ω c₀ Xᵣ Rᵣ c X Rₓ b N Rₕ q Γ ks zs n m T Q G E Λ k o qN Cᵣ D₀ γ₀ CN γ Vγ tγ
      Ls Js Os Zs Ds ps Vs Ws qs d P Rₚ j q' p Dₛ tₛ wₚ Cₚ wₛ Cₛ gold : M.Domain}
    (mx : Smdl_d I c X Rₓ) (mn : Smdl_d I b N Rₕ)
    (hN : (smdl_structure_l I (R := Rₕ) mn.2.1).Models KP)
    (U₀ w ξ ℓ e β X₀ K₀ jN : (smdl_structure_l I (R := Rₕ) mn.2.1).Domain)
    (data : Er_rank_cut_at_d hZF ω c₀ Xᵣ Rᵣ c X Rₓ q Γ ks N Rₕ zs b mn.2.1 hN
      U₀ w ξ ℓ e β X₀ K₀ jN Ls Js Os Zs Ds ps Vs Ws qs d P Rₚ j q' p)
    (Aₛ Qₛ Bₛ eₛ : (smdl_structure_l I (R := Rₕ) mn.2.1).Domain)
    (poolₛ : Eb_collapse_d w ξ ℓ K₀ X₀ β e Aₛ Qₛ Bₛ eₛ)
    (domainₛ : ∀ x, M.mem x Dₛ ↔ M.mem x N ∧ Rd_entry_d x Aₛ.val Rₕ)
    (relationₛ : M.IsSetRelation I tₛ)
    (presentₛ : Er_present_d I ω Ls N Rₕ zs Γ X ks qs eₛ.val Dₛ tₛ)
    (root : Zc_model_d I ω c₀ Xᵣ Rᵣ)
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (hc : Rd_entry_d k c Q) (hb : Rd_entry_d n b Q) (hr : Rd_entry_d o c₀ Q)
    (origin : It_map_d G o k q) (currentOrigin : It_map_d G o n qN)
    (function : M.IsSetFunction I Λ)
    (levels : ∀ i μ, Rd_entry_d i μ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ μ F)
    (slice : Tg_root_slice_d I Xᵣ Rᵣ γ₀ D₀ Cᵣ N Rₕ CN qN γ Vγ tγ)
    (omegaSlice : Rd_entry_d w.val Vγ Rₕ)
    (below : ∀ x, Rd_entry_d x γ Rₕ → Rd_entry_d x ξ.val Rₕ)
    (high : Rd_entry_d ξ.val ℓ.val Rₕ)
    (oldSquare : Tg_root_square_d D₀ q qN gold)
    (inverse : ∀ x y, Rd_entry_d x y ks ↔ Rd_entry_d y x gold)
    (rootDomain : M.MemberSubset D₀ Xᵣ)
    (omegaPoint : Rd_entry_d w.val wₚ ks) (iwₛ : Rd_entry_d wₚ wₛ j)
    (oldContext : Rd_entry_d Cᵣ Cₚ q) (iCₛ : Rd_entry_d Cₚ Cₛ j) :
    ∃ _ : Smdl_d I d P Rₚ,
      Zc_model_d I ω d P Rₚ ∧ Smap_d I ω c d X P j ∧ Smap_d I ω c₀ d Xᵣ P q' ∧
      Smap_d I ω c₀ b Xᵣ N qN ∧ It_comp_d q j q' ∧ Rd_entry_d Cᵣ Cₛ q' ∧
    ∃ θ T₁ Q₁ G₁ E₁ Λ₁,
      It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁ ∧ It_extension_d m n k T Q G E θ T₁ Q₁ G₁ E₁ ∧
      Rd_entry_d m d Q₁ ∧ It_map_d G₁ k m j ∧ Rd_entry_d n p E₁ ∧ It_map_d G₁ o m q' ∧
      M.IsSetFunction I Λ₁ ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ μ F) ∧
      (∀ i μ, Rd_entry_d i μ Λ₁ ↔ Rd_entry_d i μ Λ ∨ i = n ∧ μ = ℓ.val) ∧
      (Tg_raw_critical_d I Xᵣ Rᵣ γ₀ D₀ Cᵣ o Q G E →
        Tg_raw_critical_d I Xᵣ Rᵣ γ₀ D₀ Cᵣ o Q₁ G₁ E₁) ∧
    ∃ U₁ : (smdl_structure_l I (R := Rₕ) mn.2.1).Domain,
      V_d (kp_pair_l hN) ℓ U₁ ∧ Fs_read_d w U₁ ∧ Rr_small_d I N Rₕ U₁.val ∧
    ∃ l V₁ Γ₁ g₁, Ic_common_d I N Rₕ P Rₚ ℓ.val l U₁.val V₁ Γ₁ g₁ ∧
      M.IsRestrictionOf I g₁ tₛ Γ₁ ∧ Rd_entry_d ℓ.val l tₛ ∧ Rd_entry_d U₁.val V₁ tₛ ∧
    ∃ Bp, M.IsSetInjectionFromTo I tₛ Bp P ∧
    ∃ z₁, Rr_layer_d I ω P Rₚ wₛ z₁ ∧ Rd_entry_d w.val wₛ g₁ ∧
    ∃ Pκ : (smdl_structure_l I (R := Rₕ) mn.2.1).Domain,
      V_d (kp_pair_l hN) ξ Pκ ∧
      (∀ x : (smdl_structure_l I (R := Rₕ) mn.2.1).Domain, ∀ y Z,
        Rd_entry_d x.val Pκ.val Rₕ → Rd_entry_d x.val y ks →
          (Rd_entry_d x.val Z g₁ ↔ Rd_entry_d y Z j)) ∧
    ∃ bκ κ', Rd_entry_d ξ.val bκ ks ∧ Rd_entry_d bκ κ' j ∧
      (∀ Z, Rd_entry_d Z l Rₚ → Rd_entry_d Z κ' Rₚ) ∧
      Rr_truth_d I P Rₚ (KP.ord0_m .newest) (fun _ : Fin 1 => κ') ∧
    ∃ γ' Vγ' tγ', Rd_entry_d γ γ' g₁ ∧ Rd_entry_d Vγ Vγ' g₁ ∧ It_comp_d tγ g₁ tγ' ∧
      Tg_root_slice_d I Xᵣ Rᵣ γ₀ D₀ Cᵣ P Rₚ Cₛ q' γ' Vγ' tγ' ∧
      Rd_entry_d γ' l Rₚ ∧ Rd_entry_d wₛ Vγ' Rₚ ∧
      (∀ Z, Rd_entry_d Z γ' Rₚ → Rd_entry_d Z κ' Rₚ) ∧ Tg_root_square_d D₀ qN q' g₁ := by
  have fromRoot := tree.diagram.elementary o n qN c₀ Xᵣ Rᵣ b N Rₕ currentOrigin hr hb root.model mn
  have parent := tree.diagram.elementary o k q c₀ Xᵣ Rᵣ c X Rₓ origin hr hc root.model mx
  have native := ZFC.models_zf_l ((root.map_l hZF tree.omega mn fromRoot).native_l I hZF tree.omega)
  have rawData := data
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,mp,_,_,_,embed,rootMap,_,agreement,payload,_,certificate,rootGraph,
    U₁,rankU,readU,_,small,l,V₁,Γ₁,g₁,common,_,_,tail⟩ := rawData
  obtain ⟨Pκ,rankP,lowSquare,_,bκ,κ',_,hbκ,hκ',_,boundκ,_,_,_,_,ordκ',_,_,_,rest⟩ := tail
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨w₀,w₁,_,z₁,hww₀,hww₁,omegaEdge,_,newNumbers,_,_,_,_,_,_,_,_,_,_,_,pool,build⟩ := rest
  obtain ⟨A₀,_,_,e₀,Dp,Bp,_,_,t₀,pool,dc,_,_,_,_,_,ft,restrict,endpoint,layer,present,_,_⟩ := pool
  -- 两个已给定池来自同一次内部塌缩；表示方程识别完整池图，保留 subtype 的原图。
  obtain ⟨eqA,_,_,eqE⟩ := pool.unique_l native poolₛ
  have eqD : Dp = Dₛ := hZF.1.eq_of_same_members Dp Dₛ (fun x => by rw [dc x,domainₛ x,eqA])
  have fixed : Er_present_d I ω Ls N Rₕ zs Γ X ks qs e₀.val Dp tₛ := by
    rw [eqE,eqD]
    exact presentₛ
  have eqT := ft.1.1.1.eq_of_pairMember_iff hZF.1 relationₛ
    (fun x Z => (present x Z).trans (fixed x Z).symm)
  subst t₀
  have target := certificate root
  have hP := ZF.modelsKP (ZFC.models_zf_l (target.native_l I hZF tree.omega))
  have rootComp : It_comp_d q j q' := ⟨rootMap.1.1.1.1,fun x Z => (rootGraph x Z).trans
    ⟨And.right,fun ⟨y,xy,yZ⟩ => ⟨parent.1.1.input_mem_of_pairMember xy,y,xy,yZ⟩⟩⟩
  have targetContext : Rd_entry_d Cᵣ Cₛ q' := (rootComp.2 Cᵣ Cₛ).mpr ⟨Cₚ,oldContext,iCₛ⟩
  -- 已选证书的延伸闭包只改原树；同一 payload 的支撑随即进入原列。
  obtain ⟨_,_,_,extend⟩ := build.2 root
  obtain ⟨θ,T₁,Q₁,G₁,E₁,next,extension,node,edge,move,rootEdge,_⟩ :=
    extend m n T Q G E k o tree hm hb hc origin
  obtain ⟨Λ₁,lf₁,levels₁,entries⟩ := tree.levels_extend_l hZF hm function levels next extension move payload
  have critical (old : Tg_raw_critical_d I Xᵣ Rᵣ γ₀ D₀ Cᵣ o Q G E) :
      Tg_raw_critical_d I Xᵣ Rᵣ γ₀ D₀ Cᵣ o Q₁ G₁ E₁ :=
    extension.raw_critical_apply_l I (ZF.modelsKP hZF)
      (fun i c hi => (tree.diagram.model_domain i).mpr ⟨c,hi⟩) old next.move_function
      move payload (extension.2.2.1 n b hb) mn
      ((extension.2.2.2.1 o n qN hm.predecessor_mem).mpr currentOrigin) slice below
  have eq₀ := agreement.injection.1.1.2 w.val w₀ wₚ hww₀ omegaPoint
  have eq₁ := embed.1.1.1.2 wₚ w₁ wₛ (eq₀ ▸ omegaEdge) iwₛ
  have numbers : Rr_layer_d I ω P Rₚ wₛ z₁ := eq₁ ▸ newNumbers
  have iw : Rd_entry_d w.val wₛ g₁ := eq₁ ▸ hww₁
  -- 当前根图只经旧方块及逆图进入旧前驱；不假定它与原活动边直接复合。
  obtain ⟨γ',Vγ',tγ',iγ,iV,comp,newSlice,bound,roots⟩ :=
    slice.continue_step_l hZF common mn mp hN hP ξ Pκ rankP high below oldSquare inverse
      (fun x hx y Z hxy => lowSquare x y Z hx hxy) fromRoot.1.1.1 parent.1.1 rootDomain rootComp targetContext
  have omega : Rd_entry_d wₛ Vγ' Rₚ := (common.pred Vγ Vγ' iV wₛ).mpr ⟨w.val,omegaSlice,iw⟩
  let Pn := smdl_structure_l I (R := Rₚ) mp.2.1
  let kn : Pn.Domain := ⟨κ',ordκ'.1 0⟩
  have ordinal : Pn.IsOrdinal kn := (KP.ord0_sat_l hP _ .newest).mp
    ((rr_truth_native_l I mp.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => kn)).mp ordκ')
  have lower Z (hZ : Rd_entry_d Z γ' Rₚ) : Rd_entry_d Z κ' Rₚ :=
    ordinal.transitive ⟨γ',newSlice.rank.1⟩ (boundκ γ' bound) ⟨Z,(mp.2.2.2 Z γ' hZ).1⟩ hZ
  exact ⟨mp,target,embed,rootMap,fromRoot,rootComp,targetContext,
    θ,T₁,Q₁,G₁,E₁,Λ₁,next,extension,node,edge,move,rootEdge,lf₁,levels₁,entries,critical,
    U₁,rankU,readU,small,l,V₁,Γ₁,g₁,common,restrict,endpoint,layer,Bp,ft,z₁,numbers,iw,
    Pκ,rankP,(fun x y Z hx hxy => lowSquare x y Z hx hxy),bκ,κ',hbκ,hκ',boundκ,ordκ',
    γ',Vγ',tγ',iγ,iV,comp,newSlice,bound,omega,lower,roots⟩

end YesMetaZFC.SetTheory.LargeCardinal
