import YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Padding
import YesMetaZFC.Model.SetTheory.Relations.RecordImage

/-! # 旧运行的原控制坐标在实际锥中的像列 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem Tg_sequence_d.limit_values_l {ω c o C γ Z A D f B d N W P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val,by omega⟩ f x)
    (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 64) f (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B (U 1) (U 2) d N W P) (a : Fin 46) :
    ∃ F, Fn0_d ω N F ∧ ∀ i x, Rd_entry_d i x F ↔ Tg_limit_value_d (7 : Fin 64) (Fin.natAdd 18 a) f P i x := by
  apply cone.record_values_l hZF (7 : Fin 64) (Fin.natAdd 18 a) h.function
  · intro i s hs
    obtain ⟨_,_,v,code,_⟩ := h.rows i s hs
    exact ⟨v,code⟩
  · intro i s v hs code
    have run := (h.read_l hZF hs code).1
    obtain ⟨p,pair,hp⟩ := run.node
    exact ⟨v 15,v 0,v 1,⟨p,pair,(columns 1 p).mpr ⟨v,i,s,hs,code,hp⟩⟩,run.model.1,
      run.values.elim (fun bounds _ => bounds a.succ),
      (branch _).mpr ⟨v,i,s,hs,code,tree.diagram.order.refl _ run.finite⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 控制参数在偶数极限中相同

相邻控制参数沿原偶数边搬运，锥的交换律使它们在目标中的像相等。
对真实像函数作内部 ω 关系归纳，得到统一的目标控制树及字母表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.control_const_l {ω c o C γ Z A D f B d N W P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 64) f (U 0) x)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B (U 1) (U 2) d N W P) (a : Fin 19) :
    ∃ z, M.mem z N ∧ ∀ i x, Tg_limit_value_d (7 : Fin 64) (Fin.natAdd 18 (a.castAdd 27)) f P i x → x = z := by
  obtain ⟨F, ff, fs⟩ := h.limit_values_l hZF tree.tree columns branch cone (a.castAdd 27)
  have step i j x y (succ : M.SuccessorOf j i) (hx : Rd_entry_d i x F) (hy : Rd_entry_d j y F) : x = y := by
    obtain ⟨v, s, r, hs, ps, hr, hx⟩ := (fs i x).mp hx
    obtain ⟨w, t, l, ht, pt, hl, hy⟩ := (fs j y).mp hy
    have next := (h.steps i j s t succ hs ht).read_l hZF ps pt
    obtain ⟨_, _, _, _, _, _, _, k, _, _, _, _, _, _, edge, control, _⟩ := next
    have edge : It_map_d (U 2) (v 7) (w 7) k := by
      obtain ⟨b, bp, q, qp, hq⟩ := edge
      exact ⟨b, bp, q, qp, (columns 2 q).mpr ⟨w, j, t, ht, pt, hq⟩⟩
    have node : Rd_entry_d (v 7) (v 15) (U 1) := by
      obtain ⟨q, qp, hq⟩ := (h.read_l hZF hs ps).1.node
      exact ⟨q, qp, (columns 1 q).mpr ⟨v, i, s, hs, ps, hq⟩⟩
    have elem := cone.elementary (v 7) r (v 15) (v 0) (v 1) hr node (h.read_l hZF hs ps).1.model.1
    exact elem.1.1.1.2 _ x y hx (cone.commute (v 7) (w 7) k r l edge hr hl _ _ y (control a) hy)
  let η : Env M 0 := ⟨Fin.elim0, fun _ => F⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  have eqv x y : φ.denote η x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  have all := ZF.rel_chain_l I hZF φ η tree.tree.omega (fn0_function_l (ZF.modelsKP hZF) ff)
    (fun _ _ _ _ _ _ hx hy => (eqv _ _).mpr (((eqv _ _).mp hx).trans ((eqv _ _).mp hy)))
    (fun i j x y succ hx hy => (eqv _ _).mpr (step i j x y succ hx hy))
  obtain ⟨e, he, heω⟩ := tree.tree.omega.1.1
  obtain ⟨z, hz, first⟩ := ff.2.1 e heω
  refine ⟨z, hz, fun i x hx => ?_⟩
  have hx := (fs i x).mpr hx
  rcases (tree.tree.omega.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare e heω i (ff.bound_l hx).1 with eq | ei | ie
  · have eq := hZF.1.eq_of_same_members e i eq
    exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 i x z hx (eq ▸ first)
  · exact ((eqv z x).mp (all e i z x ei first hx)).symm
  · exact (he i ie).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 偶数分支的直接极限不良基

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
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 64) f (U 0) x) :
    ¬ It_wf_branch_d hZF ω ω (U 0) (U 1) (U 2) B := by
  intro wf
  have hw := tree.tree.omega
  obtain ⟨β, T', Q', G', ext⟩ := it_wf_branch_extend_l hZF tree.tree (hw.isLimitOrdinal (ZF.modelsKP hZF)) wf
  obtain ⟨_, _, _, _, _, _, d, N, W, P, _, _, _, target, nt, cone, nodes, _⟩ := ext.limit
  obtain ⟨N', W', K, target', source⟩ :=
    (ext.tree.sources ω d ((nodes ω d).mpr (Or.inr ⟨rfl, rfl⟩))).mem_l hZF ⟨N, W, target, nt⟩
  obtain ⟨eqN, eqW⟩ := smdl_unique_l I target'.1 target.1
  subst N' W'
  have node {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) : Rd_entry_d (v 7) (v 15) (U 1) := by
    obtain ⟨p, pair, hp⟩ := (h.read_l hZF hs code).1.node
    exact ⟨p, pair, (columns 1 p).mpr ⟨v, i, s, hs, code, hp⟩⟩
  have elem {i s j} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (hj : Rd_entry_d (v 7) j P) :=
    cone.elementary (v 7) j (v 15) (v 0) (v 1) hj (node hs code) (h.read_l hZF hs code).1.model.1
  obtain ⟨R, _, sameR⟩ := h.control_const_l hZF tree columns branch cone.toIt_embedding_d 18
  obtain ⟨F, ff, fs⟩ := h.limit_values_l hZF tree.tree columns branch cone.toIt_embedding_d 20
  -- 任意历史像都是同一目标控制树 R 的成员。
  have position i x (hx : Tg_limit_value_d (7 : Fin 64) (38 : Fin 64) f P i x) : M.mem x R := by
    obtain ⟨v, s, j, hs, code, hj, hx⟩ := hx
    have run := (h.read_l hZF hs code).1
    let nc : Nonempty {x // M.mem x (v 5)} := ⟨⟨ω, (run.context.omega_l run.source.source.code)⟩⟩
    obtain ⟨nd, σ, eq, valid⟩ := run.read_l hZF
    let ι := run.model.slice_env_d I ⟨v 5, run.context.member⟩ nd nc σ
    have valid : Formula.satisfies ι tg_issued0_m :=
      (run.model.slice_formula_l I ⟨v 5, run.context.member⟩
        (run.source.source.transitive (v 5) run.context.member) nd nc tg_issued0_m σ).mp valid
    have ft := (run.context.read_l hZF run.source.source).1
    have state := (tg_issued_sat_l (rt_pair_l ft.transitive nc hZF.1 ft.pair) (rt_model_ext_l hZF.1 ft.transitive nc) ι).mp valid
    have e20 : (ι.bound 20).val = v 38 := eq 20
    have e18 : (ι.bound 18).val = v 36 := eq 18
    have old : M.mem (v 38) (v 36) := by
      rw [← e20, ← e18]
      exact state.position
    obtain ⟨r, _, hr⟩ := (elem hs code hj).1.1.2.2 (v 36) (run.values.elim fun bound _ => bound 19)
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
  obtain ⟨η', C', _, imageC, context⟩ := run.context.map_l hZF hw run.model.1 target.1 map
    (map.omega_l I hZF hw run.source.source.transitive nt run.model target run.source.source.omega_mem)
  let nc' : Nonempty {x // M.mem x C'} := ⟨⟨ω, (context.omega_l source.code)⟩⟩
  have newFs := (context.read_l hZF source).1
  let N₀ := smdl_structure_l I (R := W) target.1.2.1
  let C₀ : N₀.Domain := ⟨C', context.member⟩
  let nd : Nonempty {x : N₀.Domain // N₀.mem x C₀} :=
    ⟨⟨⟨ω, source.omega_mem⟩, (target.2 ω C').mpr ⟨source.omega_mem, context.member, (context.omega_l source.code)⟩⟩⟩
  -- 直接搬运完整记录；仅在已假设良基的分支目标中读取实际序数秩。
  obtain ⟨_, σ, _, images, _, _, valid⟩ := map.record_image_l I hZF hw run.model.1 target.1
    (smem_ext_l I target.1 target.2 nt hZF.1) C₀ imageC (target.slice_transitive_l I C₀ newFs.transitive)
      nd tg_issued0_m tg_issued0_closed_l run.record run.values
  let θ := target.slice_env_d I C₀ nd nc' σ
  have valid : Formula.satisfies θ tg_issued0_m :=
    (target.slice_formula_l I C₀ (nt C' context.member) nd nc' tg_issued0_m σ).mp valid
  have state := (tg_issued_sat_l (rt_pair_l newFs.transitive nc' hZF.1 newFs.pair)
    (rt_model_ext_l hZF.1 newFs.transitive nc') θ).mp valid
  obtain ⟨α, H, _, _, rank⟩ := tg_control_rank_l (ZF.modelsKP hZF) newFs.transitive nc' _ state.control
  have er : (θ.bound 18).val = R := sameR e _ ⟨v, s, j, hs, code, hj, images 18⟩
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
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (b : It_branch_d ω (U 0) B) (branch : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 64) f (U 0) x) :
    It_ill_branch_d hZF ω ω (U 0) (U 1) (U 2) B := by
  obtain ⟨e, _, he⟩ := tree.tree.omega.1.1
  obtain ⟨i, hi, _⟩ := b.cofinal e he
  obtain ⟨L, V, p, G, R, q, d, N, W, order, system, elementary, limit, model⟩ :=
    it_branch_data_l hZF tree.tree.omega tree.tree.diagram b ⟨i, hi⟩
  exact ⟨b, L, V, p, G, R, q, d, N, W, order, system, elementary, limit, model,
    fun wf => h.even_illfounded_l hZF tree columns branch
      ⟨b, L, V, p, G, R, q, d, N, W, order, system, elementary, limit, model, wf⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
