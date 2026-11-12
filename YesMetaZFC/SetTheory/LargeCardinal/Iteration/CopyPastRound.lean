import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyHistory
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRawStep
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax

/-! # 原活动支撑确定档案共同层的工作解释 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原档案支撑是同一操作的载荷时，历史中的共同层就是档案的实际共同层。 -/
theorem Ic_history_d.archive_agree_l
    {ω T Q G E Λ m H ST QT GT k n c X R A π z Z α d N S B σ u U β
      p κ L F l V W D t : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (hω : M.IsOmega ω) (qf : M.IsSetFunction I Q) (lf : M.IsSetFunction I Λ)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (old : Ic_at_d H k X A π z Z α) (top : Ic_at_d H n N B σ u U β) (lt : M.mem k n)
    (qc : Rd_entry_d k c Q) (qd : Rd_entry_d n d Q)
    (mx : Smdl_d I c X R) (mn : Smdl_d I d N S) (ext : Rf_ext_d I N S)
    (move : Rd_entry_d k p E) (payload : It_payload_d p κ L F)
    (common : Ic_common_d I X R N S L l V W D t) :
    ∃ φ, Ic_agree_d I X R A π N S B σ L l φ V W D t := by
  have support := (levels k L).mpr ⟨p,κ,F,move,payload⟩
  obtain ⟨l₀,φ,V₀,W₀,D₀,t₀,c₀,d₀,R₀,S₀,qc₀,qd₀,mx₀,mn₀,agree⟩ :=
    (hist.past k n X A π z Z α N B σ u U β old top lt).active_l (lf.2 k) support
  have ec := qf.2 k c₀ c qc₀ qc
  have ed := qf.2 n d₀ d qd₀ qd
  subst c₀ d₀
  have eR := (smdl_unique_l I mx₀ mx).2
  have eS := (smdl_unique_l I mn₀ mn).2
  subst R₀ S₀
  obtain ⟨c',qc',_,row⟩ := hist.row_l hZF old
  have ec := qf.2 k c' c qc' qc
  subst c'
  obtain ⟨R',_,_,_,_,_,mx',ma,_,_,_,_,_,_,map⟩ := row
  have eR := (smdl_unique_l I mx' mx).2
  subst R'
  obtain ⟨el,eV,eW,eD,et⟩ := agree.common_unique_l hZF common hω mx ma map ext
  rw [el,eV,eW,eD,et] at agree
  exact ⟨φ,agree⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 经旧活动共同层施加的已选回合

旧载荷确定历史中的同一支撑，完整前驱唯一性将档案共同图识别为工作共同图。
逆图随后给出施加所需的工作方块；同一原后继和它的档案端点均由证书复制保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_copy_past_l
    {ω c₀ Xᵣ Rᵣ n m T Q G E χ k c X Rx b N R q Γ ks zs
      θ T₁ Q₁ G₁ E₁ Ls Js Os Zs Ds ps Vs Ws qs d P Rp j₀ q' p
      p₀ κ₀ L₀ F₀ l₀ V₀ Δ₀ t₀ l W V Δ t : M.Domain}
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (mx : Smdl_d I c X Rx) (mn : Smdl_d I b N R)
    (parent : Rd_entry_d k c Q) (current : Rd_entry_d n b Q)
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
    (past : Ic_common_d I X Rx N R L₀ l₀ V₀ U₀.val Δ₀ t₀)
    (oldMove : Rd_entry_d k p₀ E) (oldPayload : It_payload_d p₀ κ₀ L₀ F₀)
    (inverse : ∀ x y, Rd_entry_d x y ks ↔ Rd_entry_d y x t₀)
    (small : Rr_small_d I X Rx V₀)
    (common : Ic_common_d I N R P Rp ℓ.val l W V Δ t)
    (above : Rd_entry_d χ ℓ.val R)
    (next : It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁)
    (extension : It_extension_d m n k T Q G E θ T₁ Q₁ G₁ E₁)
    (target : Rd_entry_d m d Q₁) (edge : It_map_d G₁ k m j₀)
    (move : Rd_entry_d n p E₁) (payload : It_payload_d p ξ.val ℓ.val e.val) :
    Ic_round_d hZF ω (fun i => [n,m,T,Q,G,E,N,R,χ].get i)
      (fun i => [m,θ,T₁,Q₁,G₁,E₁,P,Rp,l].get i) := by
  intro H ST QT GT ⟨hn,Λ,lf,levels,hist,B,σ,u,U,β,top,bound⟩
  obtain ⟨m₀,sm,hmω⟩ := tree.omega.1.2 n hn
  have em := sm.eq hZF.1 hm
  subst m₀
  have hk := (tree.diagram.model_domain k).mpr ⟨c,parent⟩
  have lt : M.mem k n := by
    rcases (hm k).mp hk with lt | eq
    · exact lt
    · have eq := hZF.1.eq_of_same_members k n eq
      subst k
      obtain ⟨r,hr,sr⟩ := (tree.move_domain n).mp ⟨p₀,oldMove⟩
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) m (sr.eq hZF.1 hm ▸ hr)).elim
  obtain ⟨c',X',A,π,z,Z,α,old,qc,_,row⟩ := hist.at_l hZF hk
  have ec := tree.diagram.model_function.2 k c' c qc parent
  subst c'
  obtain ⟨Rx',_,_,_,_,_,mx',_,_,_,_,_,_,_,left⟩ := row
  obtain ⟨eX,eR⟩ := smdl_unique_l I mx' mx
  subst X' Rx'
  obtain ⟨_,_,_,own⟩ := hist.row_l hZF top
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,right⟩ := own
  have ext : Rf_ext_d I N R := fun x hx y hy same => congrArg Subtype.val
    (hN.1.eq_of_same_members ⟨x,hx⟩ ⟨y,hy⟩ (fun z => same z.val z.property))
  obtain ⟨η,agree⟩ := hist.archive_agree_l hZF tree.omega tree.diagram.model_function lf levels
    old top lt parent current mx mn ext oldMove oldPayload past
  obtain ⟨D,hA,hB,rA,rB,_,hU⟩ := agree.work
  have square x x' y (xx : Rd_entry_d x x' σ) (xy : Rd_entry_d x y ks) : Rd_entry_d y x' π := by
    have yx := (inverse x y).mp xy
    obtain ⟨y',_,yy⟩ := left.1.1.2.2 y ((past.carrier y).mp (past.injection.1.input_mem_of_pairMember yx)).1
    exact right.1.1.1.2 x y' x' (agree.points y y' x yy yx) xx ▸ yy
  have carrier := data.2.2.1
  have image y : Rd_entry_d y V₀ Rx ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks := by
    constructor
    · intro hy
      have hd := (past.carrier y).mpr ⟨(mx.2.2.2 y V₀ hy).1,hy⟩
      obtain ⟨x,hx,yx⟩ := past.injection.1.2.2 y hd
      exact ⟨x,(carrier x).mpr ⟨hx,(past.image x).mpr ⟨y,hd,yx⟩⟩,(inverse x y).mpr yx⟩
    · rintro ⟨x,_,xy⟩
      exact ((past.carrier y).mp (past.injection.1.input_mem_of_pairMember ((inverse x y).mp xy))).2
  obtain ⟨Λ₁,Y,v,C,γ,τ,H₁,ST₁,QT₁,GT₁,ψ,lf₁,levels₁,_,hist₁,rows,codes,maps,last,bnd,_⟩ :=
    hist.copy_original_cert_l hZFC mx mn hN U₀ w ξ ℓ e β₀ X₀ K₀ jN δ R₀ data
      numbers source rank height loc quality hU hA rA rB agree.limit square image small common
      tree hn hm next extension parent current target edge move payload lf levels old top bound above
  exact ⟨H₁,ST₁,QT₁,GT₁,⟨hmω,Λ₁,lf₁,levels₁,hist₁,C,τ,v,Y,γ,last,bnd⟩,rows,codes,maps⟩

end YesMetaZFC.SetTheory.LargeCardinal
