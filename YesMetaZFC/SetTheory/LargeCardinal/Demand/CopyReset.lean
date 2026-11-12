import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRawStep
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalPad
import YesMetaZFC.Model.SetTheory.Relations.RankImage
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax

/-! # demanding 已选重置回合的完整工作复制

先复制原工厂已经选定的恒等边，再复制同一原生施加证书。
所属工作行和原父工作行相同，原生秩段的实际像自动提供共同工作切片。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_copy_reset_l
    {ω c₀ Xᵣ Rᵣ n m T Q G E c N R χ θ T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂
      q Γ ks zs Ls Js Os Zs Ds ps Vs Ws qs d P Rp j₀ q' p l W V Δ t : M.Domain}
    (tree : It_tree_d hZF ω c₀ m T Q G E) (hm : M.SuccessorOf m n)
    (mn : Smdl_d I c N R) (node : Rd_entry_d n c Q)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (w ξ ℓ e β₀ X₀ K₀ jN δ R₀ : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (data : Er_rank_cut_at_d hZF ω c₀ Xᵣ Rᵣ c N R q Γ ks N R zs c mn.2.1 hN
      X₀ w ξ ℓ e β₀ X₀ K₀ jN Ls Js Os Zs Ds ps Vs Ws qs d P Rp j₀ q' p)
    (numbers : Rr_layer_d I ω N R w.val zs)
    (source : Ep_source_d (kp_pair_l hN) w ξ K₀ X₀ R₀)
    (rank : V_d (kp_pair_l hN) δ X₀)
    (height : (smdl_structure_l I (R := R) mn.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hN) w X₀ R₀ ξ ℓ e)
    (quality : It_owner_d I ω c ξ.val ℓ.val e.val)
    (identity : ∀ x y, Rd_entry_d x y ks ↔ M.mem x Γ ∧ x = y)
    (small : Rr_small_d I N R X₀.val)
    (common : Ic_common_d I N R P Rp ℓ.val l W V Δ t)
    (above : Rd_entry_d χ ℓ.val R)
    (mid : It_tree_d hZF ω c₀ θ T₁ Q₁ G₁ E₁)
    (pad : It_extension_d m n n T Q G E θ T₁ Q₁ G₁ E₁)
    (empty : ∀ p, Rd_entry_d n p E₁ → ∀ x, ¬ M.mem x p)
    (current : Rd_entry_d m c Q₁)
    (next : It_tree_d hZF ω c₀ θ₂ T₂ Q₂ G₂ E₂)
    (apply : It_extension_d θ m n T₁ Q₁ G₁ E₁ θ₂ T₂ Q₂ G₂ E₂)
    (target : Rd_entry_d θ d Q₂) (edge : It_map_d G₂ n θ j₀)
    (move : Rd_entry_d m p E₂) (payload : It_payload_d p ξ.val ℓ.val e.val) :
    Ic_round_d hZF ω (fun i => [n,m,T,Q,G,E,N,R,χ].get i)
      (fun i => [θ,θ₂,T₂,Q₂,G₂,E₂,P,Rp,l].get i) := by
  intro H ST QT GT ⟨hn,Λ,lf,levels,hist,B,σ,u,U,β,here,bound⟩
  obtain ⟨m₀,sm,hmω⟩ := tree.omega.1.2 n hn
  have em := sm.eq hZF.1 hm
  subst m₀
  obtain ⟨θ₀,sθ,hθω⟩ := tree.omega.1.2 m hmω
  have eθ := sθ.eq hZF.1 pad.1
  subst θ₀
  obtain ⟨c',qc',_,row⟩ := hist.row_l hZF here
  have ec := tree.diagram.model_function.2 n c' c qc' node
  subst c'
  obtain ⟨R',S,_,a,_,_,mn',ma,_,sourceB,_,_,_,_,map⟩ := row
  have eR := (smdl_unique_l I mn' mn).2
  subst R'
  obtain ⟨η,D,hδη,hXD,hD,work,limit⟩ := map.rank_image_l hZF tree.omega mn ma sourceB.transitive hN δ X₀ rank height
  obtain ⟨H₁,ST₁,QT₁,GT₁,levels₁,hist₁,rows,codes,maps,last⟩ := hist.copy_pad_l hZF tree hm levels mid pad empty
  obtain ⟨at₁,bound₁⟩ := last N R B σ u U β χ here bound
  have parent : Ic_at_d H₁ n N B σ u U β := by
    obtain ⟨r,⟨p,pair,hp⟩,cell⟩ := here
    exact ⟨r,⟨p,pair,rows p hp⟩,cell⟩
  have carrier := data.2.2.1
  have image y : Rd_entry_d y X₀.val R ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks := by
    constructor
    · intro hy
      have hyΓ := (carrier y).mpr ⟨(mn.2.2.2 y X₀.val hy).1,hy⟩
      exact ⟨y,hyΓ,(identity y y).mpr ⟨hyΓ,rfl⟩⟩
    · rintro ⟨x,hx,xy⟩
      exact ((identity x y).mp xy).2 ▸ ((carrier x).mp hx).2
  have square x x' y (xx : Rd_entry_d x x' σ) (xy : Rd_entry_d x y ks) : Rd_entry_d y x' σ :=
    ((identity x y).mp xy).2 ▸ xx
  obtain ⟨Λ₂,Y,v,C,γ,τ,H₂,ST₂,QT₂,GT₂,ψ,lf₂,levels₂,_,hist₂,rows₂,codes₂,maps₂,at₂,bound₂,_⟩ :=
    hist₁.copy_original_cert_l hZFC mn mn hN X₀ w ξ ℓ e β₀ X₀ K₀ jN δ R₀ data
      numbers source rank height loc quality hXD hD work work limit square image small common
      mid hmω pad.1 next apply (pad.2.2.1 n c node) current target edge move payload lf levels₁ parent at₁ bound₁ above
  exact ⟨H₂,ST₂,QT₂,GT₂,⟨hθω,Λ₂,lf₂,levels₂,hist₂,C,τ,v,Y,γ,at₂,bound₂⟩,
    fun x hx => rows₂ x (rows x hx),fun x hx => codes₂ x (codes x hx),fun x hx => maps₂ x (maps x hx)⟩

end YesMetaZFC.SetTheory.LargeCardinal
