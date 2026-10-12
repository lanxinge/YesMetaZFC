import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyBase

/-! # 游戏查询的共同低参数基底

五条查询先在仅含 ω、两张有限坐标图和长度的常量域中构造。
基底与当前 κ 无关；同一查询随后延伸到游戏的完整 κ 型域。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def tq_basis_m {d} (ω s t k U : Term d) : Formula 1 d := set[d] ⟪
  ⌜ω⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜s⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜t⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜k⌝ₛ ∈ ⌜U⌝ₛ ∧
  (∀ x ∈ ⌜U⌝ₛ, x = ⌜ω⌝ₛ ∨ x = ⌜s⌝ₛ ∨ x = ⌜t⌝ₛ ∨ x = ⌜k⌝ₛ)⟫
derive_free_closed tq_basis_m

theorem tq_basis_delta_l {d} (ω s t k U : Term d) : (tq_basis_m ω s t k U).IsDelta0 :=
  .conj (.mem ..) (.conj (.mem ..) (.conj (.mem ..) (.conj (.mem ..)
    (.forallMem _ (.disj (.atom ..) (.disj (.atom ..) (.disj (.atom ..) (.atom ..))))))))

theorem tq_basis_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω s t k U : Term d) :
    Formula.satisfies ρ (tq_basis_m ω s t k U) ↔
      ∀ x, M.mem x (U.eval ρ) ↔ x = ω.eval ρ ∨ x = s.eval ρ ∨ x = t.eval ρ ∨ x = k.eval ρ := by
  simp only [tq_basis_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨hw, hs, ht, hk, sub⟩ x => ⟨sub x, fun h =>
    h.elim (fun eq => eq.symm ▸ hw) (fun h => h.elim (fun eq => eq.symm ▸ hs)
      (fun h => h.elim (fun eq => eq.symm ▸ ht) (fun eq => eq.symm ▸ hk)))⟩,
    fun h => ⟨(h _).mpr (Or.inl rfl), (h _).mpr (Or.inr (Or.inl rfl)),
      (h _).mpr (Or.inr (Or.inr (Or.inl rfl))), (h _).mpr (Or.inr (Or.inr (Or.inr rfl))), fun x => (h x).mp⟩⟩

def Tg_query_base_d (ω e l n k s t r m b h q : M.Domain) : Prop := (∃ U D,
  (∀ x, M.mem x U ↔ x = ω ∨ x = s ∨ x = t ∨ x = k) ∧ Tt_pool_d I ω n U D ∧
  Tg_root_query_d I ω e n U D r ∧ Tg_max_query_d I ω l n U D m ∧
  Tg_bound_query_d I ω e l n U D b ∧ Tg_height_query_d I ω l n U D h ∧ Tg_node_query_d I ω e n l U D s t k q) ∧
  Tg_reply_base_d I ω e l n r b h

def tg_query_base0_m : Formula 1 12 :=
  let ω := Term.bound 0; let e := Term.bound 1; let l := Term.bound 2; let n := Term.bound 3
  let k := Term.bound 4; let s := Term.bound 5; let t := Term.bound 6; let r := Term.bound 7
  let m := Term.bound 8; let b := Term.bound 9; let h := Term.bound 10; let q := Term.bound 11
  set[12] ⟪(∃ U D,
  ⌜tq_basis_m⌝ₚ(⌜ω⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜k⌝ₛ, U) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, U, D) ∧
  ⌜tg_root_query_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜n⌝ₛ, U, D, ⌜r⌝ₛ) ∧ ⌜tg_max_query_m⌝ₚ(⌜ω⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, U, D, ⌜m⌝ₛ) ∧
  ⌜tg_bound_query_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, U, D, ⌜b⌝ₛ) ∧ ⌜tg_height_query_m⌝ₚ(⌜ω⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, U, D, ⌜h⌝ₛ) ∧
  ⌜tg_node_query_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜n⌝ₛ, ⌜l⌝ₛ, U, D, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜k⌝ₛ, ⌜q⌝ₛ)) ∧
  ⌜tg_reply_base_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜b⌝ₛ, ⌜h⌝ₛ)⟫

theorem tg_query_base0_closed_l : tg_query_base0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_query_base0_m, Definitional.Formula.FreeClosed]

def tg_query_base_m {d} (ω e l n k s t r m b h q : Term d) : Formula 1 d :=
  tg_query_base0_m.bind (fun i => [ω, e, l, n, k, s, t, r, m, b, h, q].get i)

@[simp] theorem tg_query_base_closed_l {d} (ω e l n k s t r m b h q : Term d)
    (hω : ω.freeSupport = []) (he : e.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = [])
    (hk : k.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = []) (hr : r.freeSupport = [])
    (hm : m.freeSupport = []) (hb : b.freeSupport = []) (hh : h.freeSupport = []) (hq : q.freeSupport = []) :
    (tg_query_base_m ω e l n k s t r m b h q).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_query_base0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, he, hl, hn, hk, hs, ht, hr, hm, hb, hh, hq, fun i => Fin.elim0 i⟩

theorem tg_query_base_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e l n k s t r m b h q : Term d) :
    Formula.satisfies ρ (tg_query_base_m ω e l n k s t r m b h q) ↔
      Tg_query_base_d I (ω.eval ρ) (e.eval ρ) (l.eval ρ) (n.eval ρ) (k.eval ρ) (s.eval ρ) (t.eval ρ)
        (r.eval ρ) (m.eval ρ) (b.eval ρ) (h.eval ρ) (q.eval ρ) := by
  simp only [tg_query_base_m, Formula.satisfies_bind, tg_query_base0_m, Tg_query_base_d,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tq_basis_sat_l hKP.1, tt_pool_sat_l I hKP,
    tg_root_query_sat_l I hKP, tg_max_query_sat_l I hKP, tg_bound_query_sat_l I hKP,
    tg_height_query_sat_l I hKP, tg_node_query_sat_l I hKP, tg_reply_base_sat_l I hKP, Definitional.Term.eval_weaken]
  rfl

/-- 原游戏行同时保存 k、k+1、k+2 三个内部元数。 -/
def tg_query_row0_m : Formula 1 12 := .conj tg_query_base0_m
  (.conj (Formula.isSuccessor (.bound 2) (.bound 4)) (Formula.isSuccessor (.bound 3) (.bound 2)))

theorem tg_query_row0_closed_l : tg_query_row0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_query_row0_m, tg_query_base0_closed_l, Definitional.Formula.FreeClosed]

theorem tg_query_row_sat_l (hKP : M.Models KP) (ρ : Env M 12) :
    Formula.satisfies ρ tg_query_row0_m ↔
      Tg_query_base_d I (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) (ρ.bound 6)
        (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10) (ρ.bound 11) ∧
      M.SuccessorOf (ρ.bound 2) (ρ.bound 4) ∧ M.SuccessorOf (ρ.bound 3) (ρ.bound 2) := by
  have base := tg_query_base_sat_l I hKP ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11)
  have eq : (Definitional.Env.substitute ρ (fun i => [Term.bound 0, Term.bound 1, Term.bound 2, Term.bound 3,
      Term.bound 4, Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9, Term.bound 10, Term.bound 11].get i)).bound = ρ.bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  simp only [tg_query_base_m, Formula.satisfies_bind, Formula.closed_env_l _ tg_query_base0_closed_l eq] at base
  simp only [tg_query_row0_m, Formula.satisfies_conj_iff, base, Formula.satisfies_isSuccessor_iff]
  rfl

theorem Tg_query_base_d.scope_l (hKP : M.Models KP) {ω e l n k s t r m b h q V W : M.Domain}
    (base : Tg_query_base_d I ω e l n k s t r m b h q) (pool : Tt_pool_d I ω n V W)
    (hw : M.mem ω V) (hs : M.mem s V) (ht : M.mem t V) (hk : M.mem k V) :
    Tg_root_query_d I ω e n V W r ∧ Tg_max_query_d I ω l n V W m ∧
    Tg_bound_query_d I ω e l n V W b ∧ Tg_height_query_d I ω l n V W h ∧ Tg_node_query_d I ω e n l V W s t k q := by
  obtain ⟨U, D, basis, small, root, max, bound, height, node⟩ := base.1
  have sub : M.MemberSubset U V := by
    intro x hx
    rcases (basis x).mp hx with rfl | rfl | rfl | rfl
    exact hw
    exact hs
    exact ht
    exact hk
  exact ⟨root.scope_l I hKP small pool sub, max.scope_l I hKP small pool sub,
    bound.scope_l I hKP small pool sub, height.scope_l I hKP small pool sub, node.scope_l I hKP small pool sub⟩

theorem tg_query_base_l (hZF : M.Models ZF) {ω e l n k s t : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (hn : M.mem n ω) (hl : M.mem l n) (hel : M.mem e l) :
    ∃ r m b h q, Tg_query_base_d (kp_pair_l (ZF.modelsKP hZF)) ω e l n k s t r m b h q := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨A, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) ω s
  obtain ⟨B, pair'⟩ := KP.exists_pair (ZF.modelsKP hZF) t k
  obtain ⟨U, union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A B
  have basis x : M.mem x U ↔ x = ω ∨ x = s ∨ x = t ∨ x = k := by
    simpa only [or_assoc] using (union x).trans (or_congr (pair x) (pair' x))
  obtain ⟨D, pool⟩ := tt_pool_exists_l J hZF hω n U
  have hen := (hω.members_areOrdinals hZF n hn).transitive l hl e hel
  obtain ⟨r, b, h, reply⟩ := tg_reply_base_l hZF hω he hen hl
  obtain ⟨root, bound, height⟩ := reply.scope_l J (ZF.modelsKP hZF) pool ((basis ω).mpr (Or.inl rfl))
  obtain ⟨m, max⟩ := tt_max_query_l hZF hω hl pool
  obtain ⟨q, node⟩ := tt_node_query_l hZF hω hn hl hel pool
    ((basis s).mpr (Or.inr (Or.inl rfl))) ((basis t).mpr (Or.inr (Or.inr (Or.inl rfl))))
    ((basis k).mpr (Or.inr (Or.inr (Or.inr rfl))))
  exact ⟨r, m, b, h, q, ⟨U, D, basis, pool, root, max, bound, height, node⟩, reply⟩

/-- 查询只受四个低参数的秩控制，与随后使用的 κ 型常量域无关。 -/
theorem Tg_query_base_d.rank_l (hZF : M.Models ZF) {ω e l n k s t r m b h q β Z : M.Domain}
    (base : Tg_query_base_d (kp_pair_l (ZF.modelsKP hZF)) ω e l n k s t r m b h q)
    (hω : M.IsOmega ω) (rank : V_d (kp_pair_l (ZF.modelsKP hZF)) β Z) (limit : M.IsLimitOrdinal β)
    (hw : M.mem ω Z) (hn : M.mem n ω) (hs : M.mem s Z) (ht : M.mem t Z) (hk : M.mem k Z) :
    M.mem r Z ∧ M.mem m Z ∧ M.mem b Z ∧ M.mem h Z ∧ M.mem q Z := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨U, D, basis, pool, root, max, bound, height, node⟩ := base.1
  obtain ⟨A, hA, pair⟩ := sc_v_pair_l hZF limit rank ω s hw hs
  obtain ⟨B, hB, pair'⟩ := sc_v_pair_l hZF limit rank t k ht hk
  obtain ⟨W, hW, aw, bw⟩ := ZF.v_joint_bound_l J hZF rank hA hB
  have hU : M.mem U Z := ZF.v_subset_mem_l J hZF rank hW (fun x hx => by
    rcases (basis x).mp hx with eq | eq | eq | eq
    exact eq.symm ▸ aw ω ((pair ω).mpr (Or.inl rfl))
    exact eq.symm ▸ aw s ((pair s).mpr (Or.inr rfl))
    exact eq.symm ▸ bw t ((pair' t).mpr (Or.inl rfl))
    exact eq.symm ▸ bw k ((pair' k).mpr (Or.inr rfl)))
  have hD := pool.rank_mem_l hZF hω rank limit hw hn hU
  have trans := ZF.v_transitive_l J hZF rank D hD
  exact ⟨trans r root.1, trans m max.1, trans b bound.1, trans h height.1, trans q node.1⟩

end YesMetaZFC.SetTheory.LargeCardinal
