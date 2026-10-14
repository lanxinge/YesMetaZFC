import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddLimit
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRootTree
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameArchivePlay

/-! # 返回极限中的共同树及其到原树的实际像

原树作为壳参数回拉到根模型；每份存档的根箭头在同一返回锥中交换，
所以全部有限节点的树坐标相等。返回因子的原复合式把这棵共同树送回原树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_return_tree_d (ω c X N H π P S S' σ f : M.Domain) : Prop :=
  ∃ d W, Smem_d I d N W ∧ Smap_d I ω d c N X σ ∧ M.mem S' N ∧ Rd_entry_d S' S σ ∧
    (∀ m i n T s t g, Tg_return_node_d ω H π P m i n T s t g → T = S') ∧
    ∀ m i n T s t g, Tg_return_node_d ω H π P m i n T s t g → ∃ s₀, Rd_entry_d s s₀ σ ∧ M.MemberSubset s₀ f

theorem Tg_odd_limit_d.tree_l {ω o c X T Q G b H π N P S f : M.Domain}
    (limit : Tg_odd_limit_d hZF ω o c X T Q G b H π N P)
    (hw : M.IsOmega ω) (ho : ∀ x, ¬ M.mem x o) (diagram : It_diagram_d hZF ω ω T Q G)
    (root : Rd_entry_d o c Q) (memS : M.mem S X) (preimage : ∃ a, Rd_entry_d a S π)
    (names : Tg_root_tree_d ω H G o S) (plays : Tg_archive_play_d ω H G o X f) :
    ∃ S' σ, Tg_return_tree_d hZF ω c X N H π P S S' σ f := by
  obtain ⟨B, Rₐ, a, U, Rᵤ, u, Q₀, G₀, H₀, c₀, X₀, R₀, π₀, d, W, σ,
    bt, ut, hwB, mb, mu, hj, hQ, hG, _, mx₀, hcc, hXX, restrict,
    small, mn, cone, _, hs, ⟨r, hr, factor⟩, _⟩ := limit
  obtain ⟨S₀, iS⟩ := preimage
  have hS₀ := (hj.member_l I hZF hw mb mu iS hXX).mpr memS
  have nat := hj.natural_l hZF hw bt ut mb mu hwB
  have root₀ := (hj.entry_l hZF hw bt ut mb mu
    (nat o (num_mem_l hZF.1 hw (show Num_d 0 o from ho))) hcc hQ).mpr root
  have leg := cone.elementary o r c₀ X₀ R₀ hr root₀ mx₀.1
  obtain ⟨S', hS', image⟩ := leg.1.1.2.2 S₀ hS₀
  have rootImage := (restrict.2 S₀ S).mpr ⟨hS₀, iS⟩
  obtain ⟨S'', value, iS''⟩ := (factor.2 S₀ S).mp rootImage
  have eq := leg.1.1.1.2 S₀ S'' S' value image
  subst S''
  refine ⟨S', σ, d, W, mn, hs, hS', iS'', ?_, ?_⟩
  · intro m i n T' s t g trace
    obtain ⟨Y, R, μ, K, η, C, L, V, q, v, row, code, _, a', _, _, _, j, ia, _, _, _, hjP, iv, _⟩ := trace
    obtain ⟨f, hf, treeImage⟩ := names m i Y R μ K η C L V q (v 19) (v 22) (v 40) (v 41) (v 42) row ⟨v, code, rfl, rfl, rfl, rfl, rfl⟩
    exact (it_cone_pull_entry_l hZF hw bt ut mb mu hj hwB hG small diagram cone.toIt_embedding_d
      hf iS ia treeImage hr hjP image iv).symm
  · intro m i n T' s t g trace
    obtain ⟨Y,R,μ,K,η,C,L,V,q,v,row,code,_,_,a',_,_,j,_,ia,_,_,hjP,_,iv,_⟩ := trace
    obtain ⟨mem,sub,f,hf,fixed⟩ := plays m i Y R μ K η C L V q v row code
    have own := (hj.member_l I hZF hw mb mu ia hXX).mpr mem
    obtain ⟨s₀,_,value⟩ := leg.1.1.2.2 a' own
    have eq := it_cone_pull_entry_l hZF hw bt ut mb mu hj hwB hG small diagram cone.toIt_embedding_d
      hf ia ia fixed hr hjP value iv
    obtain ⟨z,hz,iz⟩ := (factor.2 a' (v 40)).mp ((restrict.2 a' (v 40)).mpr ⟨own,ia⟩)
    have zs := leg.1.1.1.2 a' z s₀ hz value
    exact ⟨v 40,eq ▸ zs ▸ iz,sub⟩

end YesMetaZFC.SetTheory.LargeCardinal
