import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyExtend
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalResult

/-! # 指定原生施加证书的自动工作复制

完整代表池与商系统直接从实际证书读取，调用者只提供已经选定的原后继。
证书内部选出的共同层与档案共同层由完整前驱唯一性识别；新的历史界因此
就是档案已经记录的端点，不需要另给池相等、共同图相等或后继存在性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.copy_cert_l
    {ω c₀ Xᵣ Rᵣ θ T Q G E Λ n m H ST QT GT k χ p
      c X Rx A π z Z α b N R B σ u U β q Γ ks zs
      Ls Js Os Zs Ds ps Vs Ws qs d P Rp j₀ q'
      κ L F D₀ η Vₚ l U₁ V₂ Δ t : M.Domain}
    (mx : Smdl_d I c X Rx) (mn : Smdl_d I b N R)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (U₀ w ξ ℓ e β₀ X₀ K₀ jN δ R₀ : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (data : Er_rank_cut_at_d hZF ω c₀ Xᵣ Rᵣ c X Rx q Γ ks N R zs b mn.2.1 hN
      U₀ w ξ ℓ e β₀ X₀ K₀ jN Ls Js Os Zs Ds ps Vs Ws qs d P Rp j₀ q' p)
    (numbers : Rr_layer_d I ω N R w.val zs)
    (source : Ep_source_d (kp_pair_l hN) w ξ K₀ X₀ R₀)
    (rank : V_d (kp_pair_l hN) δ X₀)
    (height : (smdl_structure_l I (R := R) mn.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hN) w X₀ R₀ ξ ℓ e)
    (quality : It_owner_d I ω b ξ.val ℓ.val e.val)
    (hξ : Rd_entry_d ξ.val κ σ) (hℓ : Rd_entry_d ℓ.val L σ) (he : Rd_entry_d e.val F σ)
    (hU : Rd_entry_d U₀.val D₀ σ) (hD : M.mem D₀ A)
    (rA : Vr_d A η D₀) (rB : Vr_d B η D₀) (hη : M.IsLimitOrdinal η)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y ks → Rd_entry_d y x' π)
    (parent_image : ∀ y, Rd_entry_d y Vₚ Rx ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks)
    (parent_small : Rr_small_d I X Rx Vₚ)
    (common : Ic_common_d I N R P Rp ℓ.val l U₁ V₂ Δ t)
    (tree : It_tree_d hZF ω c₀ θ T Q G E)
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (pred : It_pred_d T k m)
    (hc : Rd_entry_d k c Q) (hb : Rd_entry_d n b Q) (hd : Rd_entry_d m d Q)
    (edge : It_map_d G k m j₀) (move : Rd_entry_d n p E)
    (active : Rd_entry_d n ℓ.val Λ) (lf : M.IsSetFunction I Λ)
    (ai : Ic_at_d H k X A π z Z α) (an : Ic_at_d H n N B σ u U β)
    (bound : Ic_bound_d I H Q N R σ n χ) (above : Rd_entry_d χ ℓ.val R) :
    ∃ Y v C γ τ r H' ST' QT' GT', M.SuccessorOf r m ∧
      Ic_history_d hZF ω T Q G E Λ r H' ST' QT' GT' ∧
      M.MemberSubset H H' ∧ M.MemberSubset QT QT' ∧ M.MemberSubset GT GT' ∧
      Ic_at_d H' m P C τ v Y γ ∧ Ic_bound_d I H' Q P Rp τ m l ∧
      Ic_agree_d I N R B σ P Rp C τ ℓ.val l L U₁ V₂ Δ t := by
  obtain ⟨finite,closed,carrier,hβU,hβX,transβ,products,length,raw,diagram,limit,mp,
    _,_,_,embed,_,constants,agreement,payload,_,_,_,
    Uc,_,_,_,_,lc,Vc,Dc,tc,common₀,_,_,rest⟩ := data
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,pool,_⟩ := rest
  obtain ⟨A₀,Q₀,B₀,e₀,Dp,Bp,_,_,t₀,pool,dc,bc,_,_,_,_,ft,restrict,endpoint,layer,present,prepare,_⟩ := pool
  obtain ⟨Y,v,C,γ,τ,r,H',ST',QT',GT',succ,result,rows,codes,maps,last,bnd,adjacent⟩ :=
    hist.copy_step_l hZFC mx mn hN w ξ ℓ e X₀ δ K₀ R₀ U₀ β₀ A₀ Q₀ B₀ e₀
      numbers source rank height loc quality hξ hℓ he finite closed carrier hU hD rA rB hη
      agreement square parent_image parent_small hβU hβX transβ products pool dc bc
      (fn0_of_function_l (ZF.modelsKP hZF) ft.1) present prepare length raw diagram limit mp
      (fn0_of_function_l (ZF.modelsKP hZF) embed.1.1) constants common₀ restrict endpoint layer
      tree hn hm pred hc hb hd edge move payload active lf ai an bound above
  -- 复制已经给出实际良基目标；其源证书提供原目标的外延性。
  obtain ⟨d',hd',_,next⟩ := result.row_l hZF last
  have eq := tree.diagram.model_function.2 m d' d hd' hd
  subst d'
  obtain ⟨P₀,Rp₀,_,_,_,mp₀,target,_⟩ := (next.source_l hZF).objects
  obtain ⟨eqP,eqR⟩ := smdl_unique_l I mp₀ mp
  subst P₀ Rp₀
  obtain ⟨b',hb',_,own⟩ := hist.row_l hZF an
  have eq := tree.diagram.model_function.2 n b' b hb' hb
  subst b'
  obtain ⟨R',S,_,a,_,_,mn',mb,_,_,_,_,_,_,map⟩ := own
  have eq := (smdl_unique_l I mn' mn).2
  subst R'
  obtain ⟨el,eU,eV,eD,et⟩ := adjacent.common_unique_l hZF common tree.omega mn mb map target.ext
  rw [el,eU,eV,eD,et] at adjacent
  exact ⟨Y,v,C,γ,τ,r,H',ST',QT',GT',succ,result,rows,codes,maps,last,el ▸ bnd,adjacent⟩

/-- 原操作列、支撑列及工作历史沿已选活动边同步延长。 -/
theorem Ic_history_d.copy_original_cert_l
    {ω c₀ Xᵣ Rᵣ n m θ T Q G E Λ H ST QT GT k χ p T₁ Q₁ G₁ E₁
      c X Rx A π z Z α b N R B σ u U β q Γ ks zs
      Ls Js Os Zs Ds ps Vs Ws qs d P Rp j₀ q'
      D₀ η Vₚ l U₁ V₂ Δ t : M.Domain}
    (mx : Smdl_d I c X Rx) (mn : Smdl_d I b N R)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (U₀ w ξ ℓ e β₀ X₀ K₀ jN δ R₀ : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (data : Er_rank_cut_at_d hZF ω c₀ Xᵣ Rᵣ c X Rx q Γ ks N R zs b mn.2.1 hN
      U₀ w ξ ℓ e β₀ X₀ K₀ jN Ls Js Os Zs Ds ps Vs Ws qs d P Rp j₀ q' p)
    (numbers : Rr_layer_d I ω N R w.val zs)
    (source : Ep_source_d (kp_pair_l hN) w ξ K₀ X₀ R₀)
    (rank : V_d (kp_pair_l hN) δ X₀)
    (height : (smdl_structure_l I (R := R) mn.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hN) w X₀ R₀ ξ ℓ e)
    (quality : It_owner_d I ω b ξ.val ℓ.val e.val)
    (hU : Rd_entry_d U₀.val D₀ σ) (hD : M.mem D₀ A)
    (rA : Vr_d A η D₀) (rB : Vr_d B η D₀) (hη : M.IsLimitOrdinal η)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y ks → Rd_entry_d y x' π)
    (parent_image : ∀ y, Rd_entry_d y Vₚ Rx ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks)
    (parent_small : Rr_small_d I X Rx Vₚ)
    (common : Ic_common_d I N R P Rp ℓ.val l U₁ V₂ Δ t)
    (tree : It_tree_d hZF ω c₀ m T Q G E)
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n)
    (next : It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁)
    (extension : It_extension_d m n k T Q G E θ T₁ Q₁ G₁ E₁)
    (hc : Rd_entry_d k c Q) (hb : Rd_entry_d n b Q) (hd : Rd_entry_d m d Q₁)
    (edge : It_map_d G₁ k m j₀) (move : Rd_entry_d n p E₁)
    (payload : It_payload_d p ξ.val ℓ.val e.val)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (ai : Ic_at_d H k X A π z Z α) (an : Ic_at_d H n N B σ u U β)
    (bound : Ic_bound_d I H Q N R σ n χ) (above : Rd_entry_d χ ℓ.val R) :
    ∃ Λ₁ Y v C γ τ H₁ ST₁ QT₁ GT₁ ψ, M.IsSetFunction I Λ₁ ∧
      (∀ i ρ, Rd_entry_d i ρ Λ₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F) ∧
      (∀ i ρ, Rd_entry_d i ρ Λ₁ ↔ Rd_entry_d i ρ Λ ∨ i = n ∧ ρ = ℓ.val) ∧
      Ic_history_d hZF ω T₁ Q₁ G₁ E₁ Λ₁ θ H₁ ST₁ QT₁ GT₁ ∧
      M.MemberSubset H H₁ ∧ M.MemberSubset QT QT₁ ∧ M.MemberSubset GT GT₁ ∧
      Ic_at_d H₁ m P C τ v Y γ ∧ Ic_bound_d I H₁ Q₁ P Rp τ m l ∧
      Ic_agree_d I N R B σ P Rp C τ ℓ.val l ψ U₁ V₂ Δ t := by
  obtain ⟨Λ₁,lf₁,levels₁,entries,hist₁⟩ := hist.original_extend_l hZF tree hm lf levels next extension move payload
  have bound₁ := hist.bound_extend_l hZF tree next extension hm.predecessor_mem bound
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hk := (tree.diagram.model_domain k).mpr ⟨c,hc⟩
  have order i : Rd_entry_d i k T₁ ↔ Rd_entry_d i k T :=
    (extension.2.1 i k).trans ⟨fun h => h.elim id (fun e => (ir m (e.1 ▸ hk)).elim),Or.inl⟩
  have pred : It_pred_d T₁ k m := by
    refine ⟨hk,fun i => (extension.2.1 i m).trans ?_⟩
    exact ⟨fun h => h.elim (fun h => (ir m (tree.diagram.order.bound i m h).2).elim)
      (fun h => h.2.imp_right (order i).mpr),fun h => Or.inr ⟨rfl,h.imp_right (order i).mp⟩⟩
  obtain ⟨b',hb',_,own⟩ := hist.row_l hZF an
  have eq := tree.diagram.model_function.2 n b' b hb' hb
  subst b'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,map⟩ := own
  obtain ⟨κ,_,hξ⟩ := map.1.1.2.2 ξ.val ξ.property
  obtain ⟨ψ,_,hℓ⟩ := map.1.1.2.2 ℓ.val ℓ.property
  obtain ⟨F,_,he⟩ := map.1.1.2.2 e.val e.property
  obtain ⟨Y,v,C,γ,τ,r,H₁,ST₁,QT₁,GT₁,succ,result,rows,codes,maps,last,bnd,adjacent⟩ :=
    hist₁.copy_cert_l hZFC mx mn hN U₀ w ξ ℓ e β₀ X₀ K₀ jN δ R₀ data numbers source rank height loc quality
      hξ hℓ he hU hD rA rB hη square parent_image parent_small common next hn hm pred
      (extension.2.2.1 k c hc) (extension.2.2.1 n b hb) hd edge move
      ((entries n ℓ.val).mpr (Or.inr ⟨rfl,rfl⟩)) lf₁ ai an bound₁ above
  have eq := succ.eq hZF.1 extension.1
  subst r
  exact ⟨Λ₁,Y,v,C,γ,τ,H₁,ST₁,QT₁,GT₁,ψ,lf₁,levels₁,entries,result,rows,codes,maps,last,bnd,adjacent⟩

end YesMetaZFC.SetTheory.LargeCardinal
