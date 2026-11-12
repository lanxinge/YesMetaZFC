import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnTree

/-! # 奇数尾枝上唯一的实际节点列

先由原存档与两层嵌入的单值性证明返回节点唯一，再用替代收集整列。
列的每个条目保留长度、树及全部三张坐标图，后续取并不另选有限节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_return_row_d (ω H π P i r : M.Domain) : Prop := ∃ m n S s t g,
  Tg_return_node_d ω H π P m i n S s t g ∧ Rt_tuple_d (Fin.cases n (Fin.cases S (Fin.cases s (Fin.cases t (fun _ : Fin 1 => g))))) r

def tg_return_row_m {d} (ω H π P i r : Term d) : Formula 1 d := set[d] ⟪∃ m n S s t g,
  ⌜tg_return_node_m⌝ₚ(⌜ω⌝ₛ, ⌜H⌝ₛ, ⌜π⌝ₛ, ⌜P⌝ₛ, m, ⌜i⌝ₛ, n, S, s, t, g) ∧
  ⌜fun n S s t g r => rt_tuple_m (Fin.cases n (Fin.cases S (Fin.cases s (Fin.cases t (fun _ : Fin 1 => g))))) r⌝ₚ(n, S, s, t, g, ⌜r⌝ₛ)⟫

@[simp] theorem tg_return_row_closed_l {d} (ω H π P i r : Term d)
    (hw : ω.freeSupport = []) (hH : H.freeSupport = []) (hπ : π.freeSupport = [])
    (hP : P.freeSupport = []) (hi : i.freeSupport = []) (hr : r.freeSupport = []) :
    (tg_return_row_m ω H π P i r).FreeClosed := by
  unfold tg_return_row_m
  constructor
  · unfold tg_return_node_m
    apply tg_return_node_closed_l
    simp -implicitDefEqProofs [Fin.forall_fin_succ, hw, hH, hπ, hP, hi]
  · exact rt_tuple_closed_l _ _ (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
      (by simpa using hr)

theorem tg_return_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H π P i r : Term d) :
    Formula.satisfies ρ (tg_return_row_m ω H π P i r) ↔
      Tg_return_row_d (ω.eval ρ) (H.eval ρ) (π.eval ρ) (P.eval ρ) (i.eval ρ) (r.eval ρ) := by
  simp only [tg_return_row_m, Tg_return_row_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_return_node_sat_l hE, rt_tuple_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.return_unique_l {ω c o C γ Z A D f π P i m n : M.Domain} {U : Fin 6 → M.Domain}
    {v w : Fin 5 → M.Domain} (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x) (archive : M.IsSetFunction I (U 5))
    (inj : ∀ a b x, Rd_entry_d a x π → Rd_entry_d b x π → a = b) (pf : M.IsSetFunction I P)
    (legs : ∀ i j, Rd_entry_d i j P → M.IsSetFunction I j)
    (hv : Tg_return_node_d ω (U 5) π P m i (v 0) (v 1) (v 2) (v 3) (v 4))
    (hw' : Tg_return_node_d ω (U 5) π P n i (w 0) (w 1) (w 2) (w 3) (w 4)) : v = w := by
  obtain ⟨Y, R, μ, K, η, C, L, V, q, a, row, code, num, a₀, a₁, a₂, a₃, j, i₀, i₁, i₂, i₃, hj, v₀, v₁, v₂, v₃⟩ := hv
  obtain ⟨Y', R', μ', K', η', C', L', V', q', b, row', code', num', b₀, b₁, b₂, b₃, j', i₀', i₁', i₂', i₃', hj', w₀, w₁, w₂, w₃⟩ := hw'
  obtain ⟨r, hr, cr⟩ := row
  obtain ⟨s, hs, cs⟩ := row'
  obtain ⟨_, eq⟩ := h.archive_unique_l hZF hw columns archive hr hs cr.choose_spec.1 cs.choose_spec.1
  subst s
  have eq := rt_tuple_inj_l cr cs
  have eY : Y = Y' := congrFun eq 1
  have eR : R = R' := congrFun eq 2
  have eV : V = V' := congrFun eq 8
  have eq : q = q' := congrFun eq 9
  subst Y' R' V' q'
  have eq := code.inj_l I hZF.1 code'
  have same (k : Fin 54) : a k = b k := congrFun eq k.succ.succ
  have ej := pf.2 i j' j hj' hj
  subst j'
  have image {x y a b z t} (hx : Rd_entry_d x a π) (hy : Rd_entry_d y b π) (eq : a = b)
      (hz : Rd_entry_d x z j) (ht : Rd_entry_d y t j) : z = t := by
    have eq := inj x y b (eq ▸ hx) hy
    exact (legs i j hj).2 x z t hz (eq.symm ▸ ht)
  funext k
  exact Fin.cases (num.trans ((same 22).trans num'.symm))
    (Fin.cases (image i₀ i₀' (same 19) v₀ w₀) (Fin.cases (image i₁ i₁' (same 40) v₁ w₁)
      (Fin.cases (image i₂ i₂' (same 41) v₂ w₂) (Fin.cases (image i₃ i₃' (same 42) v₃ w₃) (fun k => Fin.elim0 k))))) k

structure Tg_return_sequence_d (ω H π P N b D J F : M.Domain) : Prop where
  omega : M.IsOmega ω
  transitive : M.TransitiveSet N
  omega_mem : M.mem ω N
  indices : Fn0_d ω b J
  function : Fn0_d ω D F
  codes : ∀ i r, Rd_entry_d i r F → ∃ v : Fin 5 → M.Domain, Rt_tuple_d v r
  rows : ∀ i r (v : Fin 5 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    ∃ k m, Rd_entry_d i k J ∧ Tg_return_node_d ω H π P m k (v 0) (v 1) (v 2) (v 3) (v 4) ∧
      M.mem (v 0) ω ∧ (∀ a, M.mem (v a) N) ∧ Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4)
  steps : ∀ i j r s (v w : Fin 5 → M.Domain), M.SuccessorOf j i → Rd_entry_d i r F → Rd_entry_d j s F →
    Rt_tuple_d v r → Rt_tuple_d w s → M.SuccessorOf (w 0) (v 0) ∧
      ∀ a : Fin 3, M.MemberSubset (v ([2,3,4].get a)) (w ([2,3,4].get a))

theorem Tg_sequence_d.return_sequence_l {ω c o C γ Z A D f B b π N P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4)) (archive : M.IsSetFunction I (U 5))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (branch : It_branch_d ω (U 0) b) (tail : Tg_odd_tail_d ω (U 5) (U 0) (U 2) B b)
    (limit : Tg_odd_limit_d hZF ω (U 0) (U 2) b (U 5) π N P) :
    ∃ D' J F, Tg_return_sequence_d hZF ω (U 5) π P N b D' J F := by
  have nodes := limit.nodes
  have proper := limit.proper
  have hw := tree.tree.omega
  obtain ⟨z, hz, _, hzOdd, late⟩ := tail
  obtain ⟨J, jf, first, adjacent, above⟩ := branch.successor_sequence_l hZF hw tree.tree.diagram.order hz
  have unique {m n i} {v w : Fin 5 → M.Domain}
      (hv : Tg_return_node_d ω (U 5) π P m i (v 0) (v 1) (v 2) (v 3) (v 4))
      (hw' : Tg_return_node_d ω (U 5) π P n i (w 0) (w 1) (w 2) (w 3) (w 4)) : v = w :=
    h.return_unique_l hZF hw columns archive limit.injective limit.function limit.legs hv hw'
  let ρ : Env M 5 := ⟨fun i => [ω, U 5, π, P, J].get i, fun _ => ω⟩
  let φ : BinarySchema 5 := { body := set[7] ⟪∃ k,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ, k, ⌜(.bound 6 : Term 7)⌝ₛ) ∧
    ⌜tg_return_row_m⌝ₚ(⌜(.bound 2 : Term 7)⌝ₛ, ⌜(.bound 3 : Term 7)⌝ₛ, ⌜(.bound 4 : Term 7)⌝ₛ,
      ⌜(.bound 5 : Term 7)⌝ₛ, k, ⌜(.newest : Term 7)⌝ₛ)⟫ }
  have sat i r : φ.denote ρ i r ↔ ∃ k, Rd_entry_d i k J ∧ Tg_return_row_d ω (U 5) π P k r := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, tg_return_row_sat_l hZF.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl
  have total i (hi : M.mem i ω) : ∃ r, φ.denote ρ i r := by
    obtain ⟨k, hk, hik⟩ := jf.2.1 i hi
    have odd : Tg_odd_node_d (U 5) k := (above i k hik).elim (fun eq => eq ▸ hzOdd) (fun zk => (late k hk zk).1.1)
    obtain ⟨m, r, t, hr, pair⟩ := odd
    obtain ⟨n, S, s, t, g, _, _, _, _, _, _, trace⟩ := nodes m k r t hk hr pair
    let v : Fin 5 → M.Domain := Fin.cases n (Fin.cases S (Fin.cases s (Fin.cases t (fun _ => g))))
    obtain ⟨q, code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) v
    exact ⟨q, (sat i q).mpr ⟨k, hik, m, n, S, s, t, g, trace, code⟩⟩
  have one i r s (hr : φ.denote ρ i r) (hs : φ.denote ρ i s) : r = s := by
    obtain ⟨k, hk, m, n, S, s₀, t₀, g, trace, code⟩ := (sat i r).mp hr
    obtain ⟨l, hl, m', n', S', s', t', g', trace', code'⟩ := (sat i s).mp hs
    have eq := (fn0_function_l (ZF.modelsKP hZF) jf).1.2 i l k hl hk
    subst l
    let v : Fin 5 → M.Domain := Fin.cases n (Fin.cases S (Fin.cases s₀ (Fin.cases t₀ (fun _ => g))))
    let w : Fin 5 → M.Domain := Fin.cases n' (Fin.cases S' (Fin.cases s' (Fin.cases t' (fun _ => g'))))
    have eq : v = w := unique trace trace'
    have left : Rt_tuple_d v r := code
    have right : Rt_tuple_d w s := code'
    exact rt_tuple_unique_l hZF.1 left (eq.symm ▸ right)
  obtain ⟨D', ds⟩ := ZF.exists_functionalImage hZF φ ρ ω total one
  obtain ⟨F, ff, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun i _ => one i)
    (fun i r hi hr => (ds r).mpr ⟨i, hi, hr⟩)
  have read i r (v : Fin 5 → M.Domain) (hr : Rd_entry_d i r F) (code : Rt_tuple_d v r) :
      ∃ k m, Rd_entry_d i k J ∧ Tg_return_node_d ω (U 5) π P m k (v 0) (v 1) (v 2) (v 3) (v 4) ∧
        M.mem (v 0) ω ∧ (∀ a, M.mem (v a) N) ∧ Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4) := by
    obtain ⟨k, hk, m, n, S, s, t, g, trace, pack⟩ := (sat i r).mp ((fs i r).mp hr).2
    have eq := rt_tuple_inj_l pack code
    have trace : Tg_return_node_d ω (U 5) π P m k (v 0) (v 1) (v 2) (v 3) (v 4) :=
      congrFun eq 0 ▸ congrFun eq 1 ▸ congrFun eq 2 ▸ congrFun eq 3 ▸ congrFun eq 4 ▸ trace
    have copy := trace
    obtain ⟨_, _, _, _, _, _, _, _, _, _, row, _⟩ := copy
    obtain ⟨r, hr, cell⟩ := row
    obtain ⟨n', S', s', t', g', hn, hS, hs, ht, hg, node, tr⟩ :=
      nodes m k r cell.choose (jf.bound_l hk).2 hr cell.choose_spec.1
    let w : Fin 5 → M.Domain := Fin.cases n' (Fin.cases S' (Fin.cases s' (Fin.cases t' (fun _ => g'))))
    have eq : v = w := unique trace tr
    refine ⟨k, m, hk, trace, eq.symm ▸ hn, ?_, eq.symm ▸ node⟩
    intro a
    rw [eq]
    exact Fin.cases (limit.transitive ω limit.omega_mem n' hn) (Fin.cases hS (Fin.cases hs (Fin.cases ht (Fin.cases hg (fun a => Fin.elim0 a))))) a
  have coded i r (hr : Rd_entry_d i r F) : ∃ v : Fin 5 → M.Domain, Rt_tuple_d v r := by
    obtain ⟨_, _, _, n, S, s, t, g, _, pack⟩ := (sat i r).mp ((fs i r).mp hr).2
    exact ⟨_, pack⟩
  refine ⟨D', J, F, ⟨hw, limit.transitive, limit.omega_mem, jf, fn0_of_function_l (ZF.modelsKP hZF) ff, coded, read, ?_⟩⟩
  intro i j r s v w succ hr hs code pack
  obtain ⟨x, m, hx, tr, _, _, _⟩ := read i r v hr code
  obtain ⟨y, n, hy, tr', _, _, _⟩ := read j s w hs pack
  have pred := adjacent i j x y succ hx hy
  have zy : M.mem z y := (above i x hx).elim (fun eq => eq.symm ▸ pred.1)
    (fun zx => (hw.members_areOrdinals (ZF.modelsKP hZF) y (branch.subset y (jf.bound_l hy).2)).transitive x pred.1 z zx)
  obtain ⟨edge, prior⟩ := late y (jf.bound_l hy).2 zy
  obtain ⟨_, q, ξ, k, e, t, ℓ, Sₑ, Y, R, μ, K, η, C, L, V, c, S, l, digits, g, row, br, odd, pk, hξ⟩ := edge
  have eq := pk.unique_l hZF tree.tree.diagram.order pred (branch.subset y (jf.bound_l hy).2)
  subst k
  have ne : t ≠ e := by
    intro eq
    rcases odd with ⟨_, ex, _⟩ | ⟨ne, _⟩
    · exact (prior x pk).2.1 (ex.symm ▸ hξ)
    · exact ne eq
  obtain ⟨l', S', s', t', g', l₀, S₀, s₀, t₀, g₀, _, _, _, _, step, _, _, new, old, sub, _⟩ :=
    proper q ξ y x e t ℓ Sₑ Y R μ K η C L V c S l digits g (jf.bound_l hy).2 row br odd pk ne
  let v' : Fin 5 → M.Domain := Fin.cases l₀ (Fin.cases S₀ (Fin.cases s₀ (Fin.cases t₀ (fun _ => g₀))))
  let w' : Fin 5 → M.Domain := Fin.cases l' (Fin.cases S' (Fin.cases s' (Fin.cases t' (fun _ => g'))))
  have ev : v = v' := unique tr old
  have ew : w = w' := unique tr' new
  have sub' : ∀ a : Fin 3, M.MemberSubset (v' ([2,3,4].get a)) (w' ([2,3,4].get a)) :=
    Fin.cases (sub 0) (Fin.cases (sub 1) (Fin.cases (sub 2) (fun a => Fin.elim0 a)))
  exact ev.symm ▸ ew.symm ▸ ⟨step, sub'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原返回节点列直接使用统一的三图取并

原档案和锥的证书给出真实有限节点列，共同核心对同一列完成取并，
保留每份有限图的精确限制，不重新选择节点或恢复图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_return_sequence_d.union_l {ω H π P N b D J F : M.Domain}
    (h : Tg_return_sequence_d hZF ω H π P N b D J F) (a : Fin 3) : ∃ g, Tg_return_union_d hZF ω N F a g := by
  have sequence : Tg_node_sequence_d I ω N D F := {
    omega := h.omega
    transitive := h.transitive
    function := h.function
    codes := h.codes
    rows := by
      intro i r v hr code
      obtain ⟨_,_,_,_,finite,members,node⟩ := h.rows i r v hr code
      exact ⟨finite,members,node⟩
    steps := h.steps }
  exact sequence.union_l hZF a

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 三张并图沿初等图给出目标树中的共尾分支

并图不必是极限模型的元素。对它们的值逐点施加实际初等映射，有限图
的初等像则由自然数固定性识别。三张图合成一个 ω 列，其共尾多个前缀
属于目标树；目标树的前缀封闭性随后给出每个内部有限前缀。
5.15 使用返回因子；任意良基分支使用极限上的实际恒等图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_return_sequence_d.image_l {ω H π P N b D J F c X R S S' σ x A : M.Domain} {g : Fin 3 → M.Domain}
    (h : Tg_return_sequence_d hZF ω H π P N b D J F) (xt : M.TransitiveSet X) (mx : Smem_d I c X R)
    (origin : Tg_return_tree_d hZF ω c X N H π P S S' σ x) (input : Fn0_d ω A x)
    (unions : ∀ a, Tg_return_union_d hZF ω N F a (g a)) :
    ∃ Y q t u, Tg_cofinal_branch_d hZF ω Y S q ∧ Tg_graph_d I ω t ∧ Tg_graph_d I ω u ∧ Tg_join_d I ω x t u q := by
  obtain ⟨d, W, mn, map, _, treeImage, trees, plays⟩ := origin
  have nat := map.natural_l hZF h.omega h.transitive xt mn mx h.omega_mem
  have compose a := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) (unions a).1) map.1.1
  obtain ⟨f₀, fn₀, graph₀⟩ := compose 0
  obtain ⟨f₁, fn₁, graph₁⟩ := compose 1
  obtain ⟨f₂, fn₂, graph₂⟩ := compose 2
  let f : Fin 3 → M.Domain := Fin.cases f₀ (Fin.cases f₁ (fun _ => f₂))
  have fn : ∀ a, M.IsSetFunctionFromTo I (f a) ω X := Fin.cases fn₀ (Fin.cases fn₁ (Fin.cases fn₂ (fun a => Fin.elim0 a)))
  have graph : ∀ a i y, Rd_entry_d i y (f a) ↔ M.mem i ω ∧ ∃ x, Rd_entry_d i x (g a) ∧ Rd_entry_d x y σ :=
    Fin.cases graph₀ (Fin.cases graph₁ (Fin.cases graph₂ (fun a => Fin.elim0 a)))
  have front i y (iy : Rd_entry_d i y f₀) : Rd_entry_d i y x := by
    obtain ⟨hi,z,⟨p,pair,hp⟩,zy⟩ := (graph₀ i y).mp iy
    obtain ⟨j,r,v,jr,code,hp⟩ := ((unions 0).2.1 p).mp hp
    obtain ⟨k,m,_,trace,_,_,_⟩ := h.rows j r v jr code
    obtain ⟨s,is,sub⟩ := plays m k (v 0) (v 1) (v 2) (v 3) (v 4) trace
    have entry : Rd_entry_d i y s := (map.entry_l hZF h.omega h.transitive xt mn mx (nat i hi) zy is).mp ⟨p,pair,hp⟩
    exact entry.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  have fnx := fn0_function_l (ZF.modelsKP hZF) input
  have ex : f₀ = x := fn₀.1.1.eq_of_pairMember_iff hZF.1 fnx.1.1 (fun i y => ⟨front i y,fun iy => by
    obtain ⟨z,_,iz⟩ := fn₀.2.2 i (input.bound_l iy).1
    exact fnx.1.2 i z y (front i z iz) iy ▸ iz⟩)
  obtain ⟨V, Y, q, _, _, fq, join⟩ := tg_join_exists_l I hZF fn₀ fn₁ fn₂
  refine ⟨Y,q,f₁,f₂,⟨fn0_of_function_l (ZF.modelsKP hZF) fq,fun n hn => ?_⟩,
    ⟨fn₁.1,fn₁.2.1⟩,⟨fn₂.1,fn₂.2.1⟩,ex ▸ join⟩
  obtain ⟨z, _, ⟨p, pp, hp⟩⟩ := (unions 2).1.2.1 n hn
  obtain ⟨i, r, v, hr, code, hp⟩ := ((unions 2).2.1 p).mp hp
  obtain ⟨k, m, _, trace, hvω, member, node⟩ := h.rows i r v hr code
  have nlen : M.mem n (v 0) := (node.2.2.1.2 n).mpr ⟨z,p,pp,hp⟩
  have treeEq := trees m k (v 0) (v 1) (v 2) (v 3) (v 4) trace
  obtain ⟨s, _, is⟩ := map.1.1.2.2 (v 2) (member 2)
  obtain ⟨t, _, it⟩ := map.1.1.2.2 (v 3) (member 3)
  obtain ⟨u, _, iu⟩ := map.1.1.2.2 (v 4) (member 4)
  let w : Fin 5 → M.Domain := Fin.cases (v 0) (Fin.cases S (Fin.cases s (Fin.cases t (fun _ => u))))
  have images : ∀ a, Rd_entry_d (v a) (w a) σ := Fin.cases (nat _ hvω)
    (Fin.cases (treeEq.symm ▸ treeImage) (Fin.cases is (Fin.cases it (Fin.cases iu (fun a => Fin.elim0 a)))))
  have new := (map.tg_node_l hZF h.omega h.transitive xt mn mx images).mp node
  have sub : ∀ a : Fin 3, M.MemberSubset (w ([2,3,4].get a)) (f a) := by
    intro a
    have coord := images ([2,3,4].get a)
    have cut := (unions a).2.2 i r v hr code
    have oldGraph : Tg_graph_d I (v 0) (v ([2,3,4].get a)) :=
      Fin.cases node.1 (Fin.cases node.2.1 (Fin.cases node.2.2.1 (fun a => Fin.elim0 a))) a
    have newGraph := (map.tg_graph_l hZF h.omega h.transitive xt mn mx (nat _ hvω) coord).mp oldGraph
    intro p hp
    obtain ⟨j, y, pair⟩ := newGraph.1.1 p hp
    have entry : Rd_entry_d j y (w ([2,3,4].get a)) := ⟨p,pair,hp⟩
    have hj := (newGraph.2 j).mpr ⟨y,entry⟩
    have hjω := h.omega.transitive (ZF.modelsKP hZF) _ hvω j hj
    obtain ⟨x, ix⟩ := (oldGraph.2 j).mp hj
    have xN := (rd_entry_transitive_l h.transitive (member ([2,3,4].get a)) ix).2
    obtain ⟨y', _, iy⟩ := map.1.1.2.2 x xN
    have iy' := (map.entry_l hZF h.omega h.transitive xt mn mx (nat j hjω) iy coord).mp ix
    have eq := newGraph.1.2 j y' y iy' entry
    obtain ⟨p', pair', hp'⟩ := (graph a j y).mpr ⟨hjω, x, ((cut.2 j x).mp ix).2, eq ▸ iy⟩
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  obtain ⟨_, _, _, q', hq', joined⟩ := new
  exact ⟨v 0,q',nlen,hvω,hq',joined.1,Tg_join_d.subset_l joined join fn₀.1 fn₁.1 fn₂.1
    (h.omega.transitive (ZF.modelsKP hZF) _ hvω) (sub 0) (sub 1) (sub 2)⟩

end YesMetaZFC.SetTheory.LargeCardinal
