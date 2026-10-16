import YesMetaZFC.SetTheory.LargeCardinal.TypeGameEvenLimit
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReturnBranch
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunRoot

/-! # 任意原对局的统一历史返回原树分支

有限树取并产生共尾偶数不良基枝；回拉实际下降见证后得到不再重置的奇数尾枝。
三张坐标图在同一返回极限中取并。根图保留原树，固定锚点保留原实局前缀，
因此返回分支的第一坐标恰好是输入对局。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.branch_l {ω c o C γ Z A D H θ X R S x Y F : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D H) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (rank : V_d I θ X) (model : Smem_d I c X R) (memS : M.mem S X)
    (names : ∀ i r, Rd_entry_d i r H → Tg_run_name_d S r)
    (played : ∀ i r, Rd_entry_d i r H → ∃ n s, M.SuccessorOf n i ∧ Tg_run_real_d A n r s ∧ M.IsRestrictionOf I s x n)
    (input : Fn0_d ω A x) (space : Fseq_space_d I ω Y F) (closed : Tree_d F S) :
    ∃ q t u, Fn0_d ω Y q ∧ Branch_d F S q ∧ Tg_graph_d I ω t ∧ Tg_graph_d I ω u ∧ Tg_join_d I ω x t u q := by
  obtain ⟨U,tree,archive,columns⟩ := h.union_l hZF hw
  have root := tree.tree.root o ho
  have rootTree := h.root_tree_l hZF columns names
  have plays := h.archive_play_l hZF tree columns root model played
  obtain ⟨B,branch,bs⟩ := h.even_branch_l hZF tree columns
  have ill := h.even_limit_l hZF tree columns branch bs
  obtain ⟨b,back⟩ := it_hull_return_l hZFC tree model rank ho ill
    (Fin.cases (U 5) (Fin.cases H (fun _ : Fin 1 => S)))
  obtain ⟨odd,different⟩ := back.branch_l hZF
  obtain ⟨_,tail⟩ := h.odd_tail_l hZF tree columns branch bs odd different
  obtain ⟨π,N,P,returnedModel,limit,params⟩ := h.odd_limit_l hZF tree archive columns back
  obtain ⟨D',J,F',returned⟩ := h.return_sequence_l hZF tree archive columns odd tail limit
  obtain ⟨g₀,union₀⟩ := returned.union_l hZF 0
  obtain ⟨g₁,union₁⟩ := returned.union_l hZF 1
  obtain ⟨g₂,union₂⟩ := returned.union_l hZF 2
  let g : Fin 3 → M.Domain := Fin.cases g₀ (Fin.cases g₁ (fun _ => g₂))
  have unions : ∀ a, Tg_return_union_d hZF ω N F' a (g a) :=
    Fin.cases union₀ (Fin.cases union₁ (Fin.cases union₂ (fun a => Fin.elim0 a)))
  obtain ⟨S',σ,origin⟩ := returnedModel.tree_l hZF hw ho tree.tree.diagram root memS (params 1) rootTree plays
  obtain ⟨Y',q,t,u,cofinal,ft,fu,join⟩ := returned.image_l hZF (ZF.v_transitive_l I hZF rank) model origin input unions
  have full := cofinal.branch_l hZF hw space closed
  exact ⟨q,t,u,full.1,full.2,ft,fu,join⟩

end YesMetaZFC.SetTheory.LargeCardinal
