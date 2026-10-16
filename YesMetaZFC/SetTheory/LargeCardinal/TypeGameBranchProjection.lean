import YesMetaZFC.SetTheory.LargeCardinal.TypeGameBranchLimit
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameBranchTree
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameEvenLimit
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReturnBranch
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunRoot
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameProjection

/-! # 统一对局在任意共尾良基分支上的移位投影

给定分支后，先实际坍塌其直接极限；偶数枝不良基性迫使它具有奇数尾段。
恢复图在该分支自己的极限内取并，根腿固定低层保证第一坐标仍是原对局。
这里量化任意良基分支，不选择一个可返回原模型的分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.wf_projection_l {ω c o C γ Z A D H X R S x Y F b : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D H)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4)) (archive : M.IsSetFunction I (U 5))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ H x)
    (ho : ∀ z, ¬ M.mem z o) (model : Smem_d I c X R) (memS : M.mem S X) (memY : M.mem Y X)
    (names : ∀ i r, Rd_entry_d i r H → Tg_run_name_d S r)
    (played : ∀ i r, Rd_entry_d i r H → ∃ n s, M.SuccessorOf n i ∧ Tg_run_real_d A n r s ∧ M.IsRestrictionOf I s x n)
    (input : Fn0_d ω A x) (space : Fseq_space_d I ω Y F) (closed : Tree_d F S)
    (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b) :
    ∃ d N W P j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
      It_cone_d hZF ω b (U 1) (U 2) d N W P ∧ Rd_entry_d o j P ∧
      Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' x := by
  have hw := tree.tree.omega
  have branch := wf.1
  obtain ⟨B, evenBranch, even⟩ := h.even_branch_l hZF tree columns
  have ne : b ≠ B := fun eq => h.even_illfounded_l hZF tree columns even (eq ▸ wf)
  obtain ⟨odd, tail⟩ := h.odd_tail_l hZF tree columns evenBranch even branch ne
  obtain ⟨β, T', Q', G', ext⟩ := it_wf_branch_extend_l hZF tree.tree (hw.isLimitOrdinal hZF) wf
  obtain ⟨_, _, _, _, _, _, d, N, W, P, _, _, _, mn, cone, nodes, _⟩ := ext.limit
  have ready := ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨N₀, W₀, K, mn₀, sn⟩ := ready
  obtain ⟨eN, eW⟩ := smdl_unique_l I mn₀.1 mn.1
  subst N₀ W₀
  have root := tree.tree.root o ho
  obtain ⟨X₀, R₀, _, mx₀, sx⟩ := tree.tree.sources o c root
  obtain ⟨eX, eR⟩ := smdl_unique_l I mx₀.1 model.1
  subst X₀ R₀
  obtain ⟨k, hk, _⟩ := branch.cofinal o (num_mem_l hZF.1 hw (show Num_d 0 o from ho))
  have hob := branch.down o k (tree.tree.diagram.order.root_l hZF ho k (branch.subset k hk)) hk
  obtain ⟨j, hj⟩ := (cone.domain o).mp hob
  have map := cone.elementary o j c X R hj root model.1
  obtain ⟨π, identity, limit⟩ := h.branch_limit_l hZF tree archive columns branch mn sn.transitive sn.omega_mem cone
  obtain ⟨D', J, F₀, seq⟩ := h.return_sequence_l hZF tree archive columns branch tail limit
  obtain ⟨g₀, union₀⟩ := seq.union_l hZF 0
  obtain ⟨g₁, union₁⟩ := seq.union_l hZF 1
  obtain ⟨g₂, union₂⟩ := seq.union_l hZF 2
  have unions : ∀ a : Fin 3, Tg_return_union_d hZF ω N F₀ a ([g₀,g₁,g₂].get a) :=
    Fin.cases union₀ (Fin.cases union₁ (Fin.cases union₂ (fun a => Fin.elim0 a)))
  obtain ⟨S', σ, iS, origin⟩ := h.branch_tree_l hZF tree columns ho model memS branch odd mn sn.transitive cone hj identity
    (h.root_tree_l hZF columns names) (h.archive_play_l hZF tree columns root model played)
  obtain ⟨Y₀, q, t, u, cofinal, ft, fu, join⟩ := seq.image_l hZF sn.transitive mn origin input unions
  obtain ⟨F₁, hF₁, fs⟩ := sx.sequences.space Y memY
  have eq := hZF.1.eq_of_same_members F F₁ (fun p => (space p).trans (fs p).symm)
  obtain ⟨Y', _, iY⟩ := map.1.1.2.2 Y memY
  obtain ⟨F', _, iF⟩ := map.1.1.2.2 F (eq.symm ▸ hF₁)
  have targetSpace := map.sequences_l hZF hw sx.transitive sn.transitive model mn sn.theory sx.omega_mem iY iF space
  let ρ : Env M 2 := ⟨Fin.cases S (fun _ => F), fun _ => F⟩
  let η : Env M 2 := ⟨Fin.cases S' (fun _ => F'), fun _ => F'⟩
  have targetTree : Tree_d F' S' := (tree_sat_l η (.bound 1) .newest).mp
    ((smap_delta_l I hZF hw sx.transitive sn.transitive model mn map (tree_m (.bound 1) .newest)
      (by simp -implicitDefEqProofs) (.conj (.atom ..) (.forallMem _ (.forallMem _ (.imp (.atom ..) (.mem ..)))))
      ρ η (Fin.cases iS (fun _ => iF))).mp ((tree_sat_l ρ (.bound 1) .newest).mpr closed))
  have full := cofinal.branch_l hZF hw targetSpace targetTree
  exact ⟨d, N, W, P, j, Y', F', S', mn, ⟨N, W, K, mn, sn⟩, cone, hj, iY, iF, iS,
    targetSpace, targetTree, q, t, u, full.1, full.2, ft, fu, join⟩

end YesMetaZFC.SetTheory.LargeCardinal
