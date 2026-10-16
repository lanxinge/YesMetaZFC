import YesMetaZFC.SetTheory.LargeCardinal.TypeGameBranchFixed
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReturnTree

/-! # 任意良基极限中的共同移位树与原第一坐标

根腿把原树送到一棵固定的目标树；锥交换律识别每份恢复节点的树坐标。
共尾锚点的极限固定性同时识别第一坐标，因此目标内取并仍延长原对局。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.branch_tree_l {ω c o C γ Z A D f X R b d N W P π r S x : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (ho : ∀ x, ¬ M.mem x o) (mx : Smem_d I c X R) (memS : M.mem S X)
    (branch : It_branch_d ω (U 0) b) (odd : Tg_odd_cofinal_d ω b (U 5))
    (mn : Smem_d I d N W) (nt : M.TransitiveSet N) (cone : It_cone_d hZF ω b (U 1) (U 2) d N W P)
    (hr : Rd_entry_d o r P) (identity : ∀ x y, Rd_entry_d x y π → x = y)
    (names : Tg_root_tree_d ω (U 5) (U 2) o S) (plays : Tg_archive_play_d ω (U 5) (U 2) o X Z x) :
    ∃ S' σ, Rd_entry_d S S' r ∧ Tg_return_tree_d hZF ω d N N (U 5) π P S' S' σ x := by
  have hw := tree.tree.omega
  have root := tree.tree.root o ho
  have jr := cone.elementary o r c X R hr root mx.1
  have fixed := h.branch_fixed_l hZF tree columns ho mx branch odd mn nt cone r hr
  obtain ⟨S', hS', iS⟩ := jr.1.1.2.2 S memS
  obtain ⟨σ, idmap, ids⟩ := smap_identity_l I hZF (X := N) (c := d) hw
  refine ⟨S', σ, iS, d, W, mn, idmap, hS', (ids _ _).mpr ⟨hS', rfl⟩, ?_, ?_⟩
  · intro m i n T s t g trace
    obtain ⟨Y, R, μ, K, η, C, L, V, q, v, row, code, _, a, _, _, _, j, ia, _, _, _, hj, val, _⟩ := trace
    obtain ⟨f, hf, image⟩ := names m i Y R μ K η C L V q (v 19) (v 22) (v 40) (v 41) (v 42)
      row ⟨v, code, rfl, rfl, rfl, rfl, rfl⟩
    have eq := identity a (v 19) ia
    exact jr.1.1.1.2 S T S' (cone.commute o i f r j hf hr hj S (v 19) T image (eq ▸ val)) iS
  · intro m i n T s t g trace
    obtain ⟨Y, R, μ, K, η, C, L, V, q, v, row, code, _, _, a, _, _, j, _, ia, _, _, hj, _, val, _⟩ := trace
    obtain ⟨_, low, sub, f, hf, image⟩ := plays m i Y R μ K η C L V q v row code
    have eq := identity a (v 40) ia
    have old := cone.commute o i f r j hf hr hj (v 40) (v 40) s image (eq ▸ val)
    have same := jr.1.1.1.2 (v 40) s (v 40) old (fixed (v 40) low)
    exact ⟨s, (ids _ _).mpr ⟨jr.1.1.output_mem_of_pairMember old, rfl⟩, same.symm ▸ sub⟩

end YesMetaZFC.SetTheory.LargeCardinal
