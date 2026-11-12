import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Game.Graph
import YesMetaZFC.Model.SetTheory.Types.SubtypeWitness
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax

/-! # 类型游戏的一张图恢复

读取游戏中已经构造的原节点、最大序数查询及任意子类型见证。原排列完整保留，
从完整节点、空根和最大序数恢复同一棵树、同一末位及恰好一个新标签。
长度均为内部自然数；不增加标签顺序规则，也不预设实现层高。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem tg_one_graph_recovery_l {ω e j k l n U D s t q₁ q₂ r δ S α a B ν u : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (hn : M.mem n ω) (hek : M.mem e k)
    (hk : M.SuccessorOf k j) (hl : M.SuccessorOf l k) (hln : M.SuccessorOf n l)
    (nodeQuery : Tg_node_query_d I ω e n l U D s t k q₁) (maxQuery : Tg_max_query_d I ω l n U D q₂)
    (hB : V_d I α B) (hS : M.mem S B) (rS : Rd_entry_d e S r) (rα : Rd_entry_d k α r)
    (ga : Tg_graph_d I j a) (sa : Sg_set_d I e k r a) (rootS : M.mem e S)
    (qn : M.mem q₁ u) (qm : M.mem q₂ u) (witness : Ts_at_d hZF ω δ l r n U D u ν) :
        ∃ A c H r' g z π, V_d I ν A ∧ Smem_d I c A H ∧ Tt_realized_d I ω c A H n r' δ U D u ∧
          M.IsSetBijectionFromTo I π n n ∧
          (∀ i v x, Rd_entry_d v i π → M.mem i l → (Rd_entry_d i x r ↔ Rd_entry_d v x r')) ∧
          M.SuccessorOf ν α ∧ Rd_entry_d e S r' ∧ Rd_entry_d l α r' ∧
          Sg_set_d I e l r' g ∧ Tg_node_d I k S s t g ∧ Rd_entry_d j z g ∧
          ∀ p, M.mem p g ↔ M.mem p a ∨ KPair_d M p j z := by
  have on := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have ol := on.mem hln.predecessor_mem
  have hel := ol.transitive k hl.predecessor_mem e hek
  obtain ⟨A, c, H, r', f, h, π, hA, newModel, newType, ff, _, graph, orig, bij, perm⟩ := witness
  have moved i v x (vi : Rd_entry_d v i π) (hi : M.mem i l) : Rd_entry_d i x r ↔ Rd_entry_d v x r' := by
    have hv := bij.1.1.input_mem_of_pairMember vi
    have hin := on.transitive l hln.predecessor_mem i hi
    constructor
    · intro hx
      have fx := (orig i x hi).mp hx
      exact (graph v x).mp ((perm v hv x (ff.output_mem_of_pairMember fx)).mpr ⟨i, hin, vi, fx⟩)
    · intro hx
      obtain ⟨i', _, vi', fx⟩ := (perm v hv x (newType.tuple.bound_l hx).2).mp ((graph v x).mpr hx)
      exact (orig i x hi).mpr (bij.1.1.1.2 v i' i vi' vi ▸ fx)
  have seen i x (hi : M.mem i l) (hx : Rd_entry_d i x r) : ∃ v, M.mem v n ∧ Rd_entry_d v x r' := by
    obtain ⟨v, hv, vi⟩ := bij.2 i (on.transitive l hln.predecessor_mem i hi)
    exact ⟨v, hv, (moved i v x vi hi).mp hx⟩
  obtain ⟨T, _, newRoot⟩ := newType.tuple.2.1 e (on.transitive l hln.predecessor_mem e hel)
  obtain ⟨β, _, newLast⟩ := newType.tuple.2.1 l hln.predecessor_mem
  obtain ⟨g, _, set, node⟩ := (nodeQuery.2 c A H r' δ u T newModel (v_transitive_l I hA) newType newRoot).mp qn
  have hα := v_ordinal_l I hB
  have ne : S ≠ α := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) α
    (ZF.v_ordinal_height_l hZF hB hα (eq ▸ hS))
  obtain ⟨eqT, eqβ, sub⟩ := tg_node_recover_l (ZF.modelsKP hZF).1 (KP.exists_pair (ZF.modelsKP hZF))
    (KP.mem_irrefl_d (ZF.modelsKP hZF)) he hek hln (fn0_function_l (ZF.modelsKP hZF) newType.tuple)
    newRoot newLast set node hα rootS ne ga.1.1 (seen e S hel rS) (seen k α hl.predecessor_mem rα)
    (fun p hp => by
      obtain ⟨i, hi, _, hx⟩ := (sa p).mp hp
      exact seen i p (ol.transitive k hl.predecessor_mem i hi) hx)
  subst T β
  obtain ⟨z, hz, extension⟩ := tg_graph_extend_l (ZF.modelsKP hZF).1 (KP.exists_pair (ZF.modelsKP hZF)) hk ga node.2.2.1 sub
  exact ⟨A, c, H, r', g, z, π, hA, newModel, newType, bij, moved,
    (maxQuery.2 ν A c H r' δ u α hA newModel newType newLast).mp qm, newRoot, newLast, set, node, hz, extension⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 回答查询只使用 ω 的共同基底

空根、严格秩界和末位加二三条原查询先在单一常量域 {ω} 中产生。
因此它们不随回答的较大 κ 型域改变，可沿固定低层搬运全部读取性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_reply_base_d (ω e l n r b h : M.Domain) : Prop := ∃ U D,
  Pair_d M U ω ω ∧ Tt_pool_d I ω n U D ∧ Tg_root_query_d I ω e n U D r ∧
    Tg_bound_query_d I ω e l n U D b ∧ Tg_height_query_d I ω l n U D h

def tg_reply_base0_m : Formula 1 7 :=
  let p : Fin 7 → Term 7 := Term.bound
  set[7] ⟪∃ U D,
    ⌜pair0_m⌝ₚ(U, ⌜p 0⌝ₛ, ⌜p 0⌝ₛ) ∧ ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 3⌝ₛ, U, D) ∧
    ⌜tg_root_query_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, U, D, ⌜p 4⌝ₛ) ∧
    ⌜tg_bound_query_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, U, D, ⌜p 5⌝ₛ) ∧
    ⌜tg_height_query_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, U, D, ⌜p 6⌝ₛ)⟫

theorem tg_reply_base0_closed_l : tg_reply_base0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reply_base0_m, Definitional.Formula.FreeClosed]

def tg_reply_base_m {d} (ω e l n r b h : Term d) : Formula 1 d :=
  tg_reply_base0_m.bind (fun i => [ω, e, l, n, r, b, h].get i)

@[simp] theorem tg_reply_base_closed_l {d} (ω e l n r b h : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = [])
    (hr : r.freeSupport = []) (hb : b.freeSupport = []) (hh : h.freeSupport = []) :
    (tg_reply_base_m ω e l n r b h).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_reply_base0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, hl, hn, hr, hb, hh, fun i => Fin.elim0 i⟩

theorem tg_reply_base_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e l n r b h : Term d) :
    Formula.satisfies ρ (tg_reply_base_m ω e l n r b h) ↔
      Tg_reply_base_d I (ω.eval ρ) (e.eval ρ) (l.eval ρ) (n.eval ρ) (r.eval ρ) (b.eval ρ) (h.eval ρ) := by
  simp only [tg_reply_base_m, Formula.satisfies_bind, tg_reply_base0_m, Tg_reply_base_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    pair0_sat_l hKP.1, tt_pool_sat_l I hKP, tg_root_query_sat_l I hKP, tg_bound_query_sat_l I hKP,
    tg_height_query_sat_l I hKP, Definitional.Term.eval_weaken]
  rfl

theorem Tg_reply_base_d.scope_l (hKP : M.Models KP) {ω e l n r b h V W : M.Domain}
    (base : Tg_reply_base_d I ω e l n r b h) (pool : Tt_pool_d I ω n V W) (hw : M.mem ω V) :
    Tg_root_query_d I ω e n V W r ∧ Tg_bound_query_d I ω e l n V W b ∧ Tg_height_query_d I ω l n V W h := by
  obtain ⟨U, D, pair, small, root, bound, height⟩ := base
  have sub : M.MemberSubset U V := fun x hx => ((pair x).mp hx).elim
    (fun eq => eq.symm ▸ hw) (fun eq => eq.symm ▸ hw)
  exact ⟨root.scope_l I hKP small pool sub, bound.scope_l I hKP small pool sub, height.scope_l I hKP small pool sub⟩

theorem tg_reply_base_l (hZF : M.Models ZF) {ω e l n : M.Domain} (hω : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (hen : M.mem e n) (hl : M.mem l n) :
    ∃ r b h, Tg_reply_base_d (kp_pair_l (ZF.modelsKP hZF)) ω e l n r b h := by
  let J := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨U, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) ω ω
  obtain ⟨D, pool⟩ := tt_pool_exists_l J hZF hω n U
  obtain ⟨r, root⟩ := tt_root_query_l hZF hω he hen pool
  obtain ⟨b, bound⟩ := tt_bound_query_l hZF hω hen hl ((pair ω).mpr (Or.inl rfl)) pool
  obtain ⟨h, height⟩ := tt_height_query_l hZF hω hl pool
  exact ⟨r, b, h, U, D, pair, pool, root, bound, height⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 游戏查询的共同低参数基底

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
  have hen := (hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive l hl e hel
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
  obtain ⟨A, hA, pair⟩ := sc_v_pair_l (ZF.modelsKP hZF) limit rank ω s hw hs
  obtain ⟨B, hB, pair'⟩ := sc_v_pair_l (ZF.modelsKP hZF) limit rank t k ht hk
  obtain ⟨W, hW, aw, bw⟩ := v_joint_bound_l J rank hA hB
  have hU : M.mem U Z := v_subset_mem_l J rank hW (fun x hx => by
    rcases (basis x).mp hx with eq | eq | eq | eq
    exact eq.symm ▸ aw ω ((pair ω).mpr (Or.inl rfl))
    exact eq.symm ▸ aw s ((pair s).mpr (Or.inr rfl))
    exact eq.symm ▸ bw t ((pair' t).mpr (Or.inl rfl))
    exact eq.symm ▸ bw k ((pair' k).mpr (Or.inr rfl)))
  have hD := pool.rank_mem_l (ZF.modelsKP hZF) hω rank limit hw hn hU
  have trans := v_transitive_l J rank D hD
  exact ⟨trans r root.1, trans m max.1, trans b bound.1, trans h height.1, trans q node.1⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 一张图恢复的原语言句子

只检查原节点查询、旧图及实际任意排列见证。最大序数查询固定实现高度，
新图恰为旧图并上一个标签对；输出保留排列以及所有旧坐标的对应关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- ω,e,j,k,l,n,U,D,s,t；五条查询；旧元组 r、δ、S、α、旧图 a、实现高度 ν、新类型 u。
def tc_recover_seed0_m : Formula 1 22 :=
  let p : Fin 22 → Term 22 := Term.bound
  set[22] ⟪⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜p 1⌝ₛ) ∧
    ⌜p 5⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 1⌝ₛ ∈ ⌜p 3⌝ₛ ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜p 3⌝ₛ, ⌜p 2⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜p 4⌝ₛ, ⌜p 3⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜p 5⌝ₛ, ⌜p 4⌝ₛ) ∧
    ⌜tg_query_base_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 3⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ,
      ⌜p 10⌝ₛ, ⌜p 11⌝ₛ, ⌜p 12⌝ₛ, ⌜p 13⌝ₛ, ⌜p 14⌝ₛ) ∧
    ⌜p 0⌝ₛ ∈ ⌜p 6⌝ₛ ∧ ⌜p 3⌝ₛ ∈ ⌜p 6⌝ₛ ∧ ⌜p 8⌝ₛ ∈ ⌜p 6⌝ₛ ∧ ⌜p 9⌝ₛ ∈ ⌜p 6⌝ₛ ∧
    ⌜tg_bound_raw_m⌝ₚ(⌜p 16⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 17⌝ₛ, ⌜p 15⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜p 3⌝ₛ, ⌜p 18⌝ₛ, ⌜p 15⌝ₛ) ∧
    ⌜tg_graph_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 19⌝ₛ) ∧ ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 15⌝ₛ, ⌜p 19⌝ₛ) ∧
    ⌜p 1⌝ₛ ∈ ⌜p 17⌝ₛ ∧ ⌜p 14⌝ₛ ∈ ⌜p 21⌝ₛ ∧ ⌜p 11⌝ₛ ∈ ⌜p 21⌝ₛ ∧
    ⌜ts_at_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 16⌝ₛ, ⌜p 4⌝ₛ, ⌜p 15⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ, ⌜p 21⌝ₛ, ⌜p 20⌝ₛ)⟫

def tc_recovered_m {d} (ω e j k l n U D s t r δ S α a ν u A c H r' g z π : Term d) : Formula 1 d := set[d] ⟪
  ⌜v_m kpair_convention_l⌝ₚ(⌜ν⌝ₛ, ⌜A⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜A⌝ₛ, ⌜H⌝ₛ) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜A⌝ₛ, ⌜H⌝ₛ, ⌜n⌝ₛ, ⌜r'⌝ₛ, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(⌜π⌝ₛ, ⌜n⌝ₛ, ⌜n⌝ₛ) ∧
  (∀ i v x, ⌜rd_entry0_m⌝ₚ(v, i, ⌜π⌝ₛ) → i ∈ ⌜l⌝ₛ →
    (⌜rd_entry0_m⌝ₚ(i, x, ⌜r⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(v, x, ⌜r'⌝ₛ))) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜ν⌝ₛ, ⌜α⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, ⌜r'⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜α⌝ₛ, ⌜r'⌝ₛ) ∧ ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, ⌜r'⌝ₛ, ⌜g⌝ₛ) ∧
  ⌜tg_node_m⌝ₚ(⌜k⌝ₛ, ⌜S⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜g⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜j⌝ₛ, ⌜z⌝ₛ, ⌜g⌝ₛ) ∧
  (∀ p, p ∈ ⌜g⌝ₛ ↔ p ∈ ⌜a⌝ₛ ∨ ⌜kpair0_m⌝ₚ(p, ⌜j⌝ₛ, ⌜z⌝ₛ))⟫
derive_free_closed tc_recovered_m

-- 七个新见证占据量词栈顶；其余二十二项原输入及查询原样保留。
def tc_recovered0_m : Formula 1 29 := tc_recovered_m
  (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14)
  (.bound 15) (.bound 16) (.bound 22) (.bound 23) (.bound 24) (.bound 25) (.bound 26) (.bound 27)
  (.bound 28) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)

theorem tc_recovered0_closed_l : tc_recovered0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_recovered0_m]

def tc_recover_result0_m : Formula 1 22 :=
  let p : Fin 22 → Term 22 := Term.bound
  set[22] ⟪∃ A c H r' g z π,
    ⌜tc_recovered_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ,
      ⌜p 8⌝ₛ, ⌜p 9⌝ₛ, ⌜p 15⌝ₛ, ⌜p 16⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ, ⌜p 20⌝ₛ, ⌜p 21⌝ₛ, A, c, H, r', g, z, π)⟫

theorem tc_recover_seed0_closed_l : tc_recover_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_recover_seed0_m, Definitional.Formula.FreeClosed]
theorem tc_recover_result0_closed_l : tc_recover_result0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_recover_result0_m, Definitional.Formula.FreeClosed]

def tc_recover_m : Formula 1 0 := Formula.forallClosure 22 (.imp tc_recover_seed0_m tc_recover_result0_m)

theorem tc_recover_closed_l : tc_recover_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tc_recover_seed0_closed_l, tc_recover_result0_closed_l⟩

theorem tc_recover_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tc_recover_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tc_recover_seed0_m, tc_recover_result0_m, tc_recovered_m, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, tg_query_base_sat_l I (ZF.modelsKP hZF),
    tg_bound_raw_sat_l I hZF.1, rd_entry0_sat_l hZF.1, tg_graph_sat_l I hZF.1, sg_set_sat_l I hZF.1,
    ts_at_sat_l hZF, Formula.satisfies_exists_iff, v_sat_l I hZF.1, smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_isBijectionFromTo_iff I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, tg_node_sat_l I hZF.1,
    Formula.satisfies_disj_iff, kpair0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rintro ⟨hw, he, hn, hek, hk, hl, hln, base, hwU, hkU, hsU, htU, ⟨_, _, B, rank, hS⟩,
    first, last, graph, set, root, qn, qm, witness⟩
  have data := witness
  obtain ⟨_, _, _, _, _, _, _, _, _, type, _⟩ := data
  obtain ⟨_, max, _, _, node⟩ := base.scope_l I (ZF.modelsKP hZF) type.pool hwU hsU htU hkU
  exact tg_one_graph_recovery_l hZF hw he hn hek hk hl hln node max rank hS first last graph set root qn qm witness

end YesMetaZFC.SetTheory.LargeCardinal
