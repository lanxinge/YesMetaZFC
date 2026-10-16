import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddBranch
import YesMetaZFC.SetTheory.LargeCardinal.IterationConeFixed

/-! # 任意非偶数良基极限固定原局低层

奇数存档共尾性提供共尾多个实际根锚点。统一有限历史已经逐点固定这些
锚点，故极限锥固定整个原低层，包括每份已恢复的原局前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.branch_fixed_l {ω c o C γ Z A D f X R b d N W P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (ho : ∀ x, ¬ M.mem x o) (mx : Smem_d I c X R)
    (branch : It_branch_d ω (U 0) b) (odd : Tg_odd_cofinal_d ω b (U 5))
    (mn : Smem_d I d N W) (nt : M.TransitiveSet N) (cone : It_cone_d hZF ω b (U 1) (U 2) d N W P) :
    ∀ r, Rd_entry_d o r P → ∀ x, M.mem x Z → Rd_entry_d x x r := by
  have hw := tree.tree.omega
  have root := tree.tree.root o ho
  obtain ⟨X', R', _, mx', sx⟩ := tree.tree.sources o c root
  obtain ⟨eqX, eqR⟩ := smdl_unique_l I mx'.1 mx.1
  subst X' R'
  have hoω := num_mem_l hZF.1 hw (show Num_d 0 o from ho)
  obtain ⟨s, _, hs⟩ := h.function.2.1 o hoω
  obtain ⟨_, _, v, code, _⟩ := h.rows o s hs
  have run := (h.read_l hZF hs code).1
  have zt := run.anchor.rank.transitive_l hZF run.source.source.transitive run.anchor.member
  apply cone.fixed_l hZF hw tree.tree.diagram branch root mx sx.transitive mn nt
    (fun i c hc => by
      obtain ⟨Y, R, _, my, source⟩ := tree.tree.sources i c hc
      exact ⟨Y, R, my, source.transitive⟩) zt
  intro i hi
  obtain ⟨k, hk, ik, m, r, t, hr, pair⟩ := odd i (branch.subset i hi)
  obtain ⟨p, pp, hp⟩ := hr
  obtain ⟨v, l, s, ls, code, hp⟩ := (columns 5 p).mp hp
  have run := (h.read_l hZF ls code).1
  obtain ⟨k', Y, R, μ, K, η, C, L, V, q, cell, _, _⟩ := run.past.rows m r ⟨p, pp, hp⟩
  have eq : k' = k := (kpair_injective_l M cell.choose_spec.1 pair).1
  subst k'
  have row : Tg_past_at_d (v 13) m k Y R μ K η C L V q := ⟨r, ⟨p, pp, hp⟩, cell⟩
  obtain ⟨⟨j, edge, _, anchor⟩, _⟩ := run.roots m k Y R μ K η C L V q row
  obtain ⟨a, ap, b, bp, hb⟩ := edge
  exact ⟨k, j, hk, branch.forward_l tree.tree.diagram.order hi hk ik,
    ⟨a, ap, b, bp, (columns 2 b).mpr ⟨v, l, s, ls, code, hb⟩⟩, anchor.fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal
