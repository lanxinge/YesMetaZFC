import YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnTree
import YesMetaZFC.SetTheory.LargeCardinal.Game.EvenLimit
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnBranch
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.TreeImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.StrategyPlay

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
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (ho : ∀ x, ¬ M.mem x o) (mx : Smem_d I c X R)
    (branch : It_branch_d ω (U 0) b) (odd : Tg_odd_cofinal_d ω b (U 5))
    (mn : Smem_d I d N W) (nt : M.TransitiveSet N) (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P) :
    ∀ r, Rd_entry_d o r P → ∀ x, M.mem x Z → Rd_entry_d x x r := by
  have hw := tree.tree.omega
  have root := tree.tree.root o ho
  apply cone.fixed_l hZF hw tree.tree.diagram branch root mx.1 mn nt
  intro i hi
  obtain ⟨k, hk, ik, m, r, t, hr, pair⟩ := odd i (branch.subset i hi)
  obtain ⟨p, pp, hp⟩ := hr
  obtain ⟨v, l, s, ls, code, hp⟩ := (columns 5 p).mp hp
  have run := (h.read_l hZF ls code).1
  obtain ⟨k', Y, R, μ, K, η, C, L, V, q, cell, source, _⟩ := run.past.rows m r ⟨p, pp, hp⟩
  have eq : k' = k := (kpair_injective_l M cell.choose_spec.1 pair).1
  subst k'
  have row : Tg_past_at_d (v 13) m k Y R μ K η C L V q := ⟨r, ⟨p, pp, hp⟩, cell⟩
  obtain ⟨⟨j, edge, _, anchor⟩, _⟩ := run.roots m k Y R μ K η C L V q row
  obtain ⟨a, node, my⟩ := run.links m k Y R μ K η C L V q row
  have node' : Rd_entry_d k a (U 1) := by
    obtain ⟨p, pair, hp⟩ := node
    exact ⟨p, pair, (columns 1 p).mpr ⟨v, l, s, ls, code, hp⟩⟩
  have edge' : It_map_d (U 2) o k j := by
    obtain ⟨a, ap, b, bp, hb⟩ := edge
    exact ⟨a, ap, b, bp, (columns 2 b).mpr ⟨v, l, s, ls, code, hb⟩⟩
  have jt := tree.tree.diagram.elementary o k j c X _ a Y R edge' root node' mx.1 my.1
  obtain ⟨_, H, _, t, _, layer, _, fixed⟩ := anchor
  refine ⟨k,j,a,Y,R,hk,branch.forward_l tree.tree.diagram.order hi hk ik,
    edge',node',my.1,layer.transitive,?_,?_⟩
  · intro x hx
    obtain ⟨y,_,xy⟩ := layer.injection.1.2.2 x hx
    exact ⟨y,fixed x y xy⟩
  · intro x y hx xy z
    obtain ⟨y',_,xy'⟩ := layer.injection.1.2.2 x hx
    have same := jt.1.1.1.2 x y' y (fixed x y' xy') xy
    apply (layer.predecessors x y (same ▸ xy') z).trans
    apply exists_congr
    intro a
    apply and_congr_right
    intro ax
    refine ⟨fixed a z,fun az => ?_⟩
    obtain ⟨z',_,az'⟩ := layer.injection.1.2.2 a (layer.transitive x hx a ax)
    exact jt.1.1.1.2 a z' z (fixed a z' az') az ▸ az'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定共尾分支上的实际恢复图

直接把各份奇数存档送入给定极限锥。恒等图只统一原存档的读法，取自实际
传递包络；目标无需返回原模型。良基分支的锥由原坍塌定理构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.branch_limit_l {ω c o C γ Z A D f b d N W P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (archive : M.IsSetFunction I (U 5))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (branch : It_branch_d ω (U 0) b) (mn : Smem_d I d N W) (nt : M.TransitiveSet N)
    (hwN : M.mem ω N) (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P) :
    ∃ π, (∀ x y, Rd_entry_d x y π → x = y) ∧ Tg_odd_limit_d hZF ω (U 0) (U 2) b (U 5) π N P := by
  have hw := tree.tree.omega
  obtain ⟨r, pack⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) (fun i : Fin 4 => [ω,U 1,U 2,U 5].get i)
  obtain ⟨K, hrK, kt⟩ := ZF.mem_hull_l M hZF I r
  have bound := Rt_tuple_d.members_l pack kt hrK
  obtain ⟨k, R, mk⟩ := smdl_membership_l I hZF ⟨ω, bound 0⟩
  obtain ⟨π, identity, values⟩ := smap_identity_l I hZF (X := K) (c := k) hw
  have ar := h.archive_l hZF hw columns
  have growth := cone.toIt_embedding_d.odd_l hZF hw tree.tree.diagram mn nt
    (fun x y h => ((values x y).mp h).2) ar.2.1 ar.2.2
  have nodes : ∀ m i r t₀, M.mem i b → Rd_entry_d m r (U 5) → KPair_d M r i t₀ → ∃ n S s t g,
      M.mem n ω ∧ M.mem S N ∧ M.mem s N ∧ M.mem t N ∧ M.mem g N ∧
      Tg_node_d I n S s t g ∧ Tg_return_node_d ω (U 5) π P m i n S s t g := by
    intro m i r t₀ hi hr pair
    obtain ⟨p, pr, hp⟩ := hr
    obtain ⟨v, l, z, hz, code, hp⟩ := (columns 5 p).mp hp
    obtain ⟨i', Y, R', μ, K', η, C', L, V, q, cell, _, saved, _⟩ := (h.read_l hZF hz code).1.past.rows m r ⟨p, pr, hp⟩
    have eq : i' = i := (kpair_injective_l M cell.choose_spec.1 pair).1
    subst i'
    have row : Tg_past_at_d (U 5) m i Y R' μ K' η C' L V q :=
      ⟨r, ⟨p, pr, (columns 5 p).mpr ⟨v, l, z, hz, code, hp⟩⟩, cell⟩
    obtain ⟨a, ha, my⟩ := ar.2.1 m i Y R' μ K' η C' L V q row
    have yt := (ar.2.2 m i Y R' μ K' η C' L V q row).1
    have yK := (my.1.1.mem_l M kt (rd_entry_transitive_l kt (bound 1) ha).2).1
    obtain ⟨ρ, cq, _, _, _⟩ := saved.membership_l I hZF.1 my (yt C' saved.context.member)
      ⟨⟨ω, saved.context.omega_l ⟨a, my⟩⟩⟩
    obtain ⟨hn, member, node⟩ := saved.node_l hZF hw my yt cq
    let w : Fin 54 → M.Domain := fun a => (ρ.bound a).val
    have fixed a : Rd_entry_d (w a) (w a) π := (values _ _).mpr ⟨kt Y yK (w a) (member a), rfl⟩
    obtain ⟨j, hj⟩ := (cone.domain i).mp hi
    have leg := cone.elementary i j a Y R' hj ha my.1
    obtain ⟨S, hS, iS⟩ := leg.1.1.2.2 (w 19) (member 19)
    obtain ⟨s, hs, is⟩ := leg.1.1.2.2 (w 40) (member 40)
    obtain ⟨t, ht, it⟩ := leg.1.1.2.2 (w 41) (member 41)
    obtain ⟨g, hg, ig⟩ := leg.1.1.2.2 (w 42) (member 42)
    have nat := leg.natural_l hZF hw yt nt my mn saved.context.omega_mem (w 22) hn
    have image : ∀ a : Fin 5, Rd_entry_d ([w 22,w 19,w 40,w 41,w 42].get a) ([w 22,S,s,t,g].get a) j :=
      Fin.cases nat (Fin.cases iS (Fin.cases is (Fin.cases it (Fin.cases ig (fun a => Fin.elim0 a)))))
    exact ⟨w 22, S, s, t, g, hn, hS, hs, ht, hg,
      (leg.tg_node_l hZF hw yt nt my mn image).mp node,
      Y, R', μ, K', η, C', L, V, q, w, row, cq, rfl,
      w 19, w 40, w 41, w 42, j, fixed 19, fixed 40, fixed 41, fixed 42, hj, iS, is, it, ig⟩
  refine ⟨π, fun x y h => ((values x y).mp h).2,
    ⟨nt, hwN, identity.1.2, cone.function, ?_, nodes,
      growth.growth_l hZF hw tree.tree.diagram.order branch archive nodes⟩⟩
  intro i j hij
  obtain ⟨c, hc⟩ := (tree.tree.diagram.model_domain i).mp (branch.subset i ((cone.domain i).mpr ⟨j, hij⟩))
  obtain ⟨X, R, mx⟩ := tree.tree.diagram.models i c hc
  exact (cone.elementary i j c X R hij hc mx).1.1.1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意良基极限中的共同移位树与原第一坐标

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
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (ho : ∀ x, ¬ M.mem x o) (mx : Smem_d I c X R) (memS : M.mem S X)
    (branch : It_branch_d ω (U 0) b) (odd : Tg_odd_cofinal_d ω b (U 5))
    (mn : Smem_d I d N W) (nt : M.TransitiveSet N) (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
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

/-! ## 统一对局在任意共尾良基分支上的移位投影

给定分支后，先实际坍塌其直接极限；偶数枝不良基性迫使它具有奇数尾段。
恢复图在该分支自己的极限内取并，根腿固定低层保证第一坐标仍是原对局。
这里量化任意良基分支，不选择一个可返回原模型的分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.wf_projection_l {ω c o C γ Z A D H X R w S x Y F b : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D H)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4)) (archive : M.IsSetFunction I (U 5))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ H x)
    (ho : ∀ z, ¬ M.mem z o) (model : Smem_d I c X R)
    (names : ∀ i r, Rd_entry_d i r H → Tg_run_name_d S r)
    (played : ∀ i r, Rd_entry_d i r H → ∃ n s, M.SuccessorOf n i ∧ Tg_run_real_d I A n r s ∧ M.IsRestrictionOf I s x n)
    (input : Fn0_d ω A x)
    (natural : Rr_truth_d I X R (Formula.isOmega .newest) (fun _ : Fin 1 => w))
    (space : Sc_fseq_d I w Y F X R)
    (closed : Rr_truth_d I X R (tree_m (.bound 1) .newest) (Fin.cases S (fun _ : Fin 1 => F)))
    (wf : It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) b) :
    ∃ d N W P j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P ∧ Rd_entry_d o j P ∧
      Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' x := by
  have hw := tree.tree.omega
  have hwX := (space.bounds_l I).1
  have memY := (space.bounds_l I).2.1
  have memF := (space.bounds_l I).2.2
  have memS : M.mem S X := closed.elim fun members _ => members 0
  have branch := wf.1
  obtain ⟨B, evenBranch, even⟩ := h.even_branch_l hZF tree.tree columns
  have ne : b ≠ B := fun eq => h.even_illfounded_l hZF tree columns even (eq ▸ wf)
  obtain ⟨odd, tail⟩ := h.odd_tail_l hZF tree columns evenBranch even branch ne
  obtain ⟨β, T', Q', G', ext⟩ := it_wf_branch_extend_l hZF tree.tree (hw.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_, _, _, _, _, _, d, N, W, P, _, _, _, mn, nt, cone, nodes, _⟩ := ext.limit
  have ready := ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨N₀, W₀, K, mn₀, sn⟩ := ready.mem_l hZF ⟨N, W, mn, nt⟩
  obtain ⟨eN, eW⟩ := smdl_unique_l I mn₀.1 mn.1
  subst N₀ W₀
  have root := tree.tree.root o ho
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
  -- 原树和有限空间在原根内解释；只有良基分支的实际坍塌目标作字面读取。
  obtain ⟨Y', hY', iY⟩ := map.1.1.2.2 Y memY
  obtain ⟨F', hF', iF⟩ := map.1.1.2.2 F memF
  obtain ⟨v, hv, iw⟩ := map.1.1.2.2 w hwX
  have omegaClosed : (Formula.isOmega (.newest : Term 1)).FreeClosed := by
    simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed]
  let N₀ := smdl_structure_l I (R := W) mn.1.2.1
  have read (a : N₀.Domain) (valid : Rr_truth_d I N W (Formula.isOmega .newest) (fun _ : Fin 1 => a.val)) :
      N₀.IsOmega a := (Formula.satisfies_isOmega_iff (⟨fun _ => a, fun _ => a⟩ : Env N₀ 1) .newest).mp
        ((rr_truth_native_l I mn.1.2.1 _ omegaClosed (fun _ => a)).mp valid)
  have nv := read ⟨v, hv⟩ (natural.map_l I hZF hw model.1 mn.1 map omegaClosed (fun _ => iw))
  have nw := read ⟨ω, sn.omega_mem⟩ sn.toEr_source_d.natural
  have eq : v = ω := congrArg Subtype.val ((sn.ext.native_l I mn.1.2.1).eq_of_same_members
    ⟨v, hv⟩ ⟨ω, sn.omega_mem⟩ (fun a => ⟨nv.2 _ nw.1 a, nw.2 _ nv.1 a⟩))
  subst v
  obtain ⟨targetSpace,targetTree⟩ := Smap_d.tree_space_l hZF hw model.1 mn nt map
    (sn.algebra_l (ZF.modelsKP hZF)).pair (sn.algebra_l (ZF.modelsKP hZF)).union
    iw iY iF iS space closed
  have projection := cofinal.projection_l hZF hw targetSpace targetTree ft fu join
  exact ⟨d, N, W, P, j, Y', F', S', mn, ready, cone, hj, iY, iF, iS,
    targetSpace, targetTree, projection⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际递归初值的全分支策略

从已实现的零轮状态统一选择后继表，构造一个原局策略。每个服从策略的
对局产生自己的整棵迭代树，每个活动扩展器的临界点都不低于原低层高度；
对这棵树的每条共尾良基分支，实际装配移位投影。
原树、自然数对象及有限空间均使用原根中的实际真值。
初值仍使用现有工作模型规格；任意地模型的相对初值不能用此规格代替。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

/-- 同一棵实际迭代树同时满足逐扩展器临界点界和全部良基共尾分支投影。 -/
def Tg_shifted_d (hZF : M.Models ZF) (ω o c γ Y F S x : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ T Q G E L, It_pnice_d hZF ω c ω T Q G E L ∧
    It_critical_bound_d I γ Q E ∧
    ∀ b, It_wf_branch_d hZF ω ω T Q G b →
      ∃ d N W P j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
        It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P ∧ Rd_entry_d o j P ∧
        Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
        Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' x

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_code_d.shifted_strategy_l {ω c o C γ Z A r S X R w Y F a : M.Domain}
    (initial : Tg_run_code_d hZF ω c o C γ Z A o r) (name : Tg_run_name_d S r)
    (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o) (limit : M.IsLimitOrdinal γ)
    (hwZ : M.mem ω Z) (hAZ : M.mem A Z) (ha : M.mem a A)
    (model : Smem_d I c X R)
    (natural : Rr_truth_d I X R (Formula.isOmega .newest) (fun _ : Fin 1 => w))
    (space : Sc_fseq_d I w Y F X R)
    (closed : Rr_truth_d I X R (tree_m (.bound 1) .newest) (Fin.cases S (fun _ : Fin 1 => F))) :
    ∃ K σ, Fseq_space_d I ω A K ∧ Fn0_d K A σ ∧
      ∀ x, Fn0_d ω A x → Gm_follows_d I false ω σ x → Tg_shifted_d hZF ω o c γ Y F S x := by
  obtain ⟨D, E, J, machine⟩ := initial.choice_l hZFC hw ho limit hwZ hAZ name
  obtain ⟨K, finite⟩ := ZF.fseq_space_exists_l I hZF hw A
  obtain ⟨σ, strategy, values⟩ := machine.strategy_l hZF hw ho ha finite
  refine ⟨K, σ, finite, strategy, fun x input follows => ?_⟩
  obtain ⟨H, sequence, names, played⟩ := machine.sequence_l hZF hw ho ha finite strategy values input follows
  obtain ⟨U, tree, archive, columns⟩ := sequence.union_l hZF hw
  exact ⟨U 0, U 1, U 2, U 3, U 4, tree, sequence.critical_bound_l hZF (columns 1) (columns 3),
    fun b wf => sequence.wf_projection_l hZF tree archive columns
    ho model names played input natural space closed (b := b) wf⟩

end YesMetaZFC.SetTheory.LargeCardinal
