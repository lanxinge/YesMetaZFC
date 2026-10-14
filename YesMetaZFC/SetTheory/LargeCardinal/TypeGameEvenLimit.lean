import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLimitControl
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRank
import YesMetaZFC.SetTheory.LargeCardinal.IterationBranchExtend

/-! # 偶数分支的直接极限不良基

假设良基后，已有坍塌构造产生真实传递目标和锥。原控制树在所有偶数节点
的像相同，历史像逐轮真延长；同一实际秩函数于是给出内部隶属下降链。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.even_illfounded_l {ω c o C γ Z A D f B : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (branch : ∀ x, M.mem x B ↔ Tg_even_d f (U 0) x) :
    ¬ It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) B := by
  intro wf
  have hw := tree.tree.omega
  obtain ⟨β, T', Q', G', ext⟩ := it_wf_branch_extend_l hZF tree.tree (hw.isLimitOrdinal hZF) wf
  obtain ⟨_, _, _, _, _, _, d, N, W, P, _, _, _, target, cone, nodes, _⟩ := ext.limit
  obtain ⟨N', W', K, target', source⟩ := ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨eqN, eqW⟩ := smdl_unique_l I target'.1 target.1
  subst N' W'
  have nt := source.transitive
  have node {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) : Rd_entry_d (v 7) (v 15) (U 1) := by
    obtain ⟨p, pair, hp⟩ := (h.read_l hZF hs code).1.node
    exact ⟨p, pair, (columns 1 p).mpr ⟨v, i, s, hs, code, hp⟩⟩
  have elem {i s j} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (hj : Rd_entry_d (v 7) j P) :=
    cone.elementary (v 7) j (v 15) (v 0) (v 1) hj (node hs code) (h.read_l hZF hs code).1.model.1
  obtain ⟨R, _, sameR⟩ := h.control_const_l hZF tree columns branch cone.toIt_embedding_d 18
  obtain ⟨F, ff, fs⟩ := h.limit_values_l hZF tree columns branch cone.toIt_embedding_d 20
  -- 任意历史像都是同一目标控制树 R 的成员。
  have position i x (hx : Tg_limit_value_d 20 f P i x) : M.mem x R := by
    obtain ⟨v, s, j, hs, code, hj, hx⟩ := hx
    have run := (h.read_l hZF hs code).1
    let nc : Nonempty {x // M.mem x (v 5)} := ⟨⟨ω, run.context.omega⟩⟩
    obtain ⟨ι, eq, valid⟩ := run.read_l hZF nc
    have ft := (run.context.read_l hZF run.source.source).1
    have state := (tg_issued_sat_l (rt_pair_l ft.transitive nc hZF.1 ft.pair) (rt_model_ext_l hZF.1 ft.transitive nc) ι).mp valid
    have e20 : (ι.bound 20).val = v 38 := eq 20
    have e18 : (ι.bound 18).val = v 36 := eq 18
    have old : M.mem (v 38) (v 36) := by
      rw [← e20, ← e18]
      exact state.position
    obtain ⟨r, _, hr⟩ := (elem hs code hj).1.1.2.2 (v 36)
      (run.source.source.transitive _ run.context.member _ (e18 ▸ (ι.bound 18).property))
    have er : r = R := sameR i r ⟨v, s, j, hs, code, hj, hr⟩
    exact er ▸ ((elem hs code hj).member_l I hZF hw run.model target hx hr).mp old
  have fn : Fn0_d ω R F := by
    have ft := fn0_function_l (ZF.modelsKP hZF) ff
    exact fn0_of_function_l (ZF.modelsKP hZF) ⟨ft.1, ft.2.1, fun i hi => by
      obtain ⟨x, _, hx⟩ := ft.2.2 i hi
      exact ⟨x, position i x ((fs i x).mp hx), hx⟩⟩
  -- 从一个实际阶段搬运完整控制记录，读取 R 的原序数秩。
  obtain ⟨e, _, heω⟩ := hw.1.1
  obtain ⟨s, _, hs⟩ := h.function.2.1 e heω
  obtain ⟨_, _, v, code, _⟩ := h.rows e s hs
  have run := (h.read_l hZF hs code).1
  obtain ⟨j, hj⟩ := (cone.domain (v 7)).mp ((branch _).mpr
    ⟨v, e, s, hs, code, tree.tree.diagram.order.refl _ run.finite⟩)
  have map := elem hs code hj
  obtain ⟨η', C', _, imageC, context⟩ := run.context.map_l hZF hw run.source.source.transitive nt run.model target map
  let nc : Nonempty {x // M.mem x (v 5)} := ⟨⟨ω, run.context.omega⟩⟩
  let nc' : Nonempty {x // M.mem x C'} := ⟨⟨ω, context.omega⟩⟩
  have oldFs := (run.context.read_l hZF run.source.source).1
  have newFs := (context.read_l hZF source).1
  obtain ⟨ι, eq, valid⟩ := run.read_l hZF nc
  obtain ⟨θ, images, moved⟩ := map.relative_image_l hZF hw run.source.source.transitive nt run.model target
    oldFs.transitive newFs.transitive nc nc' imageC tg_issued0_m tg_issued0_closed_l ι
  have state := (tg_issued_sat_l (rt_pair_l newFs.transitive nc' hZF.1 newFs.pair)
    (rt_model_ext_l hZF.1 newFs.transitive nc') θ).mp (moved.mp valid)
  obtain ⟨α, H, _, _, rank⟩ := tg_control_rank_l (ZF.modelsKP hZF) newFs.transitive nc' _ state.control
  have er : (θ.bound 18).val = R := sameR e _ ⟨v, s, j, hs, code, hj, (eq 18) ▸ images 18⟩
  have rank : Cg_rank_d (θ.bound 0).val (θ.bound 12).val R α H := er ▸ rank
  have proper i k x y (succ : M.SuccessorOf k i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d k y F) :
      M.MemberSubset x y ∧ x ≠ y := by
    obtain ⟨v, s, r, hs, ps, hr, hx⟩ := (fs i x).mp hx
    obtain ⟨w, t, l, ht, pt, hl, hy⟩ := (fs k y).mp hy
    have vr := (h.read_l hZF hs ps).1
    have wr := (h.read_l hZF ht pt).1
    obtain ⟨_, _, _, _, _, _, _, b, z, _, _, _, _, _, edge, _, hz, sub, ne, _⟩ :=
      (h.steps i k s t succ hs ht).read_l hZF ps pt
    have edge : It_map_d (U 2) (v 7) (w 7) b := by
      obtain ⟨q, pair, p, pp, hp⟩ := edge
      exact ⟨q, pair, p, pp, (columns 2 p).mpr ⟨w, k, t, ht, pt, hp⟩⟩
    have between := tree.tree.diagram.elementary (v 7) (w 7) b (v 15) (v 0) (v 1) (w 15) (w 0) (w 1)
      edge (node hs ps) (node ht pt) vr.model.1 wr.model.1
    obtain ⟨x', _, hz'⟩ := (elem ht pt hl).1.1.2.2 z (between.1.1.output_mem_of_pairMember hz)
    have ex : x' = x := (elem hs ps hr).1.1.1.2 _ x' x (cone.commute (v 7) (w 7) b r l edge hr hl _ z x' hz hz') hx
    have image : Rd_entry_d z x l := ex ▸ hz'
    exact ⟨((elem ht pt hl).subset_l hZF hw wr.source.source.transitive nt wr.model target image hy).mp sub,
      fun eq => ne ((elem ht pt hl).1.2 z (w 38) y (eq ▸ image) hy)⟩
  obtain ⟨J, jf, js⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) fn) (fn0_function_l (ZF.modelsKP hZF) rank.function)
  obtain ⟨E, wf, edges⟩ := wf_membership_l hZF α
  apply wf_no_desc_l hZF hw wf (fn0_of_function_l (ZF.modelsKP hZF) jf)
  intro i k a b succ ha hb
  obtain ⟨_, x, hx, xa⟩ := (js i a).mp ha
  obtain ⟨_, y, hy, yb⟩ := (js k b).mp hb
  have step := proper i k x y succ hx hy
  exact (edges b a).mpr ⟨jf.output_mem_of_pairMember hb, jf.output_mem_of_pairMember ha,
    rank.proper x y a b xa yb step.1 step.2⟩

/-- 同一共尾枝的原始直接极限实际存在，其商关系不良基。 -/
theorem Tg_sequence_d.even_limit_l {ω c o C γ Z A D f B : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (b : It_branch_d ω (U 0) B) (branch : ∀ x, M.mem x B ↔ Tg_even_d f (U 0) x) :
    It_ill_branch_d hZF ω ω (U 0) (U 1) (U 2) B := by
  obtain ⟨e, _, he⟩ := tree.tree.omega.1.1
  obtain ⟨i, hi, _⟩ := b.cofinal e he
  obtain ⟨L, V, p, G, R, q, d, N, W, order, system, elementary, limit, model⟩ :=
    it_branch_data_l hZF tree.tree.omega tree.tree.diagram b ⟨i, hi⟩
  exact ⟨b, L, V, p, G, R, q, d, N, W, order, system, elementary, limit, model,
    fun wf => h.even_illfounded_l hZF tree columns branch
      ⟨b, L, V, p, G, R, q, d, N, W, order, system, elementary, limit, model, wf⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
