import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReturnSyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationBranchSequence

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
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x) (archive : M.IsSetFunction I (U 5))
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
  have eV : V = V' := congrFun eq 8
  have eq : q = q' := congrFun eq 9
  subst V' q'
  have eq := rt_tuple_inj_l code code'
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
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
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
    (fun zx => (hw.members_areOrdinals hZF y (branch.subset y (jf.bound_l hy).2)).transitive x pred.1 z zx)
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
