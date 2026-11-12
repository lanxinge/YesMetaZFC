import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding

/-! # 从原历史恢复继续分支的查询与候选

辅助走法的解码唯一性识别已发出记录中的 ℓ、t、κ、u 和三个内部元数。
原表读取同一个节点查询与 dcp 弹性；非空分支保留所选旧轮及原超过关系。
全程只解包已反射的真公式，不给工作层附加 ZF 模型性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include I hE

theorem tg_issued_query_l (ρ : Env M 46) (valid : Formula.satisfies ρ tg_issued0_m) :
    ∃ h x s B U D r m b q f,
      Fseq_end_d I (ρ.bound 0) (ρ.bound 20) h (ρ.bound 21) ∧
      (Fn0_d (ρ.bound 19) (ρ.bound 6) x ∧ ∀ i v, M.mem i (ρ.bound 19) →
        (Rd_entry_d i v x ↔ Tg_event_d I (ρ.bound 4) i (ρ.bound 3) h v)) ∧
      M.IsRestrictionOf I s x (ρ.bound 26) ∧
      Tg_query_data_d (ρ.bound 11) (ρ.bound 24) (ρ.bound 26) s (ρ.bound 23) B U D r m b q f ∧
      M.MemberSubset (ρ.bound 25) D ∧ M.mem f (ρ.bound 25) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 27, ρ.bound 28, ρ.bound 26,
        s, ρ.bound 23, r, m, b, q, f].get i, ρ.free⟩ : Env M 12) tg_query_row0_m ∧
      ((ρ.bound 19 = ρ.bound 1 ∧ M.mem (ρ.bound 6) B) ∨
        ∃ j a ℓ t τ u, M.SuccessorOf (ρ.bound 19) j ∧ Tg_event_d I (ρ.bound 4) j (ρ.bound 1) h a ∧
          Tg_aux_data_d a ℓ t τ u ∧ M.mem τ (ρ.bound 24)) ∧
      (ρ.bound 23 ≠ ρ.bound 1 → Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 2,
        ρ.bound 4, ρ.bound 5, ρ.bound 19, h, ρ.bound 22, ρ.bound 23, ρ.bound 24, ρ.bound 26,
        ρ.bound 28, U, D, ρ.bound 25].get i, ρ.free⟩ : Env M 15) tg_continue0_m) ∧
      M.mem (ρ.bound 26) (ρ.bound 0) ∧ M.mem (ρ.bound 27) (ρ.bound 0) ∧ M.mem (ρ.bound 28) (ρ.bound 0) ∧
      ∃ χ : Env M 12, (∀ i : Fin 12, χ.bound i =
        [ρ.bound 25, ρ.bound 28, ρ.bound 0, ρ.bound 24, ρ.bound 27, ρ.bound 29,
          ρ.bound 30, ρ.bound 31, ρ.bound 32, ρ.bound 33, ρ.bound 34, ρ.bound 35].get i) ∧ Formula.satisfies χ tg_candidate0_m ∧
        Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 27, ρ.bound 28, ρ.bound 24,
          B, U, D, r, b, q].get i, ρ.free⟩ : Env M 11) tg_reply_language0_m := by
  have state := (tg_issued_sat_l I hE ρ).mp valid
  have original := state.auxiliary
  simp only [tg_issued_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, tg_aux_m, Formula.satisfies_bind, tg_aux0_m, tg_aux_data_sat_l hE,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_isRestriction_iff I, tg_query_data_sat_l hE, Formula.satisfies_subset_iff,
    tg_ee_data_sat_l hE, tg_elastic_sat_l I hE, Definitional.Term.eval_weaken] at original
  obtain ⟨h, endt, ℓ, t, κ, u, k, l, N, x, s, B, U, D, r, m, b, q, f, C, V, W, g₀, g₁, g₂, g₃,
    move, _, labels, first, last, digits, rest, request, row, sub, elastic, drop, node, growth, fork⟩ := original
  obtain ⟨eℓ, et, eκ, eu⟩ := move.unique_l state.move
  change ℓ = ρ.bound 22 at eℓ
  change t = ρ.bound 23 at et
  change κ = ρ.bound 24 at eκ
  change u = ρ.bound 25 at eu
  subst ℓ t κ u
  have ek : k = ρ.bound 26 := labels.domain_eq_l hE state.labels
  subst k
  have el : l = ρ.bound 27 := first.eq hE state.first
  subst l
  have eN : N = ρ.bound 28 := last.eq hE state.last
  subst N
  -- 同一表项的读取保留原节点常量；不会重新选择一份不同的查询。
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have tables := control.1
  simp only [tg_tables_m, Formula.satisfies_conj_iff] at tables
  have query := tables.1.2.2.2
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_query_data_sat_l hE, Formula.satisfies_isSuccessor_iff, tg_query_request_m,
    Formula.satisfies_bind, tg_query_base_m] at query
  simp only [tg_query_request_m, Formula.satisfies_bind] at request
  obtain ⟨l, N, first, last, replyLanguage, _, _, base⟩ :=
    query (ρ.bound 24) state.bound (ρ.bound 26) s (ρ.bound 23) B U D r m b q f (by
      apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := _) (η := _) ?_).mp request
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i) row
  have el : l = ρ.bound 27 := first.eq hE state.first
  subst l
  have eN : N = ρ.bound 28 := last.eq hE state.last
  subst N
  have facts := request
  simp only [tg_query_request0_m, Formula.satisfies_conj_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff] at facts
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have omega := (Formula.satisfies_isOmega_iff ..).mp rules.1
  obtain ⟨l, succ, hl⟩ := omega.1.2 (ρ.bound 26) facts.2.1
  have eq : l = ρ.bound 27 := succ.eq hE state.first
  have finite : M.mem (ρ.bound 27) (ρ.bound 0) := eq ▸ hl
  obtain ⟨N, succN, hN⟩ := omega.1.2 (ρ.bound 27) finite
  have eqN : N = ρ.bound 28 := succN.eq hE state.last
  have finiteN : M.mem (ρ.bound 28) (ρ.bound 0) := eqN ▸ hN
  have language := tables.1.1
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isLimitOrdinal_iff, tg_ee_data_sat_l hE, ee_language_m, Formula.satisfies_bind] at language
  have language := language (ρ.bound 24) state.bound (ρ.bound 27) finite C V W g₀ g₁ g₂ g₃ facts.1 elastic
  simp only [tg_growth_m, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hE, tg_aux_data_sat_l hE,
    Definitional.Term.eval_weaken] at growth
  simp only [tg_digits_m, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hE, tg_event_sat_l I hE, Definitional.Term.eval_weaken] at digits
  refine ⟨h, x, s, B, U, D, r, m, b, q, f, endt, digits, rest, row, sub, node, ?_, growth, ?_,
    facts.2.1, finite, finiteN, ?_⟩
  · apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨?_, (Formula.satisfies_conj_iff ..).mpr ⟨state.first, state.last⟩⟩
    apply (Formula.closed_env_l tg_query_base0_m tg_query_base0_closed_l (ρ := _) (η := _) ?_).mp base
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  · intro ne
    simp only [Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff,
      tg_continue_m, Formula.satisfies_bind] at fork
    have cont := fork.elim (fun reset => (ne reset.1).elim) And.right
    apply (Formula.closed_env_l tg_continue0_m tg_continue0_closed_l (ρ := _) (η := _) ?_).mp cont
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))) i
  · let χ : Env M 12 := ⟨fun i => [ρ.bound 25, ρ.bound 28, ρ.bound 0, ρ.bound 24, ρ.bound 27,
      C, V, W, g₀, g₁, g₂, g₃].get i, ρ.free⟩
    have fn := (Formula.satisfies_isFunction_iff I hE ..).mp tables.2.2.1
    obtain ⟨eC, eV, eW, eq⟩ := elastic.unique_l hE fn state.elastic
    refine ⟨χ, ?_, (Formula.satisfies_conj_iff ..).mpr ⟨?_, (tg_elastic_sat_l I hE ..).mpr drop⟩, ?_⟩
    · intro i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases eC (Fin.cases eV (Fin.cases eW (Fin.cases (congrArg Ee_queries_d.largest eq)
          (Fin.cases (congrArg Ee_queries_d.domain eq) (Fin.cases (congrArg Ee_queries_d.inaccessible eq)
            (Fin.cases (congrArg Ee_queries_d.stretch eq) (fun j => Fin.elim0 j)))))))))))) i
    · apply (Formula.satisfies_rename ..).mpr
      apply (Formula.closed_env_l ee_language0_m ee_language0_closed_l (ρ := _) (η := _) ?_).mp language
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
    · simp only [tg_reply_language_m, Formula.satisfies_bind] at replyLanguage
      apply (Formula.closed_env_l tg_reply_language0_m tg_reply_language0_closed_l (ρ := _) (η := _) ?_).mp replyLanguage
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原三阶段历史的旧事件与域增长

时钟的单值性来自原控制记录中的真公式。追加走法保留旧事件，因此规则 (4)
读到的前驱辅助走法就是实际上一轮的走法，其域严格小于下一轮的域。
每轮对应同时记录标签序列和回答有序对，供规则 (6) 读取同一旧回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)

include hE in
/-- 原控制记录在任意后继反射层内决定唯一事件值。 -/
theorem tg_control_event_unique_l (ρ : Env M 19) (valid : Formula.satisfies ρ tg_control0_m)
    {n r h v w m X : M.Domain} (fn : Fn0_d m X h)
    (left : Tg_event_d I (ρ.bound 4) n r h v) (right : Tg_event_d I (ρ.bound 4) n r h w) : v = w := by
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at valid
  have clock := (tg_index_sat_l I hE ..).mp valid.2.2.2.2.2.2.2.2.2
  obtain ⟨i, hi, vi⟩ := left
  obtain ⟨j, hj, wj⟩ := right
  have eq : i = j := clock n r i j hi hj
  subst j
  exact fn.2.2 i (fn.bound_l vi).1 v (fn.bound_l vi).2 w (fn.bound_l wj).2 vi wj

/-- 任意保留原图的延长都保留全部旧事件。 -/
theorem Tg_event_d.mono_l {c n r h t v : M.Domain}
    (event : Tg_event_d I c n r h v) (sub : M.MemberSubset h t) : Tg_event_d I c n r t v := by
  obtain ⟨i, clock, p, pair, hp⟩ := event
  exact ⟨i, clock, p, pair, sub p hp⟩

include I hE in
/-- 由两份真实请求及其历史包含关系直接读出规则 (4) 的严格增长。 -/
theorem tg_issued_growth_l (ρ θ : Env M 46)
    (valid : Formula.satisfies ρ tg_issued0_m) (next : Formula.satisfies θ tg_issued0_m)
    (same : ∀ i : Fin 19, θ.bound (i.castAdd 27) = ρ.bound (i.castAdd 27))
    (succ : M.SuccessorOf (θ.bound 19) (ρ.bound 19)) (sub : M.MemberSubset (ρ.bound 20) (θ.bound 20)) :
    M.mem (ρ.bound 24) (θ.bound 24) := by
  have old := (tg_issued_sat_l I hE ρ).mp valid
  have new := (tg_issued_sat_l I hE θ).mp next
  obtain ⟨h, _, _, _, _, _, _, _, _, _, _, endt, _, _, _, _, _, _, growth, _⟩ := tg_issued_query_l I hE θ next
  have event : Tg_event_d I (θ.bound 4) (ρ.bound 19) (θ.bound 1) (θ.bound 20) (ρ.bound 21) := by
    rw [show θ.bound 4 = ρ.bound 4 from same 4, show θ.bound 1 = ρ.bound 1 from same 1]
    exact old.event.mono_l I sub
  rcases growth with ⟨zero, _⟩ | ⟨j, a, l, t, κ, u, sj, past, move, below⟩
  · have control := new.control
    simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
    have rules := control.2.2.1
    simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
    have empty : ∀ x, ¬ M.mem x (θ.bound 1) := (Formula.satisfies_isEmpty_iff ..).mp rules.2.1
    exact (empty (ρ.bound 19) (zero ▸ succ.predecessor_mem)).elim
  · have eq : ρ.bound 19 = j := Structure.SuccessorOf.predecessor_eq hE old.clock.1 succ sj
    subst j
    have eq := tg_control_event_unique_l I hE _ new.control new.history (past.end_l endt) event
    have bound : κ = ρ.bound 24 := (move.unique_l (eq.symm ▸ old.move)).2.2.1
    exact bound ▸ below

/-- 一轮的标签、辅助走法与完整回答都在同一原历史中出现。 -/
def Tg_round_event_d (c e a n h t z : M.Domain) : Prop :=
  (∃ v l κ u, Tg_event_d I c n e h v ∧ Tg_aux_data_d v l t κ u) ∧ Tg_event_d I c n a h z

def tg_round_event_m {d} (c e a n h t z : Term d) : Formula 1 d := set[d] ⟪
  (∃ v l κ u, ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, ⌜n⌝ₛ, ⌜e⌝ₛ, ⌜h⌝ₛ, v) ∧ ⌜tg_aux_data_m⌝ₚ(v, l, ⌜t⌝ₛ, κ, u)) ∧
  ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, ⌜n⌝ₛ, ⌜a⌝ₛ, ⌜h⌝ₛ, ⌜z⌝ₛ)⟫
derive_free_closed tg_round_event_m

def tg_round_event0_m : Formula 1 7 :=
  tg_round_event_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)

theorem tg_round_event0_closed_l : tg_round_event0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_round_event0_m]

include hE in
theorem tg_round_event_sat_l {d} (ρ : Env M d) (c e a n h t z : Term d) :
    Formula.satisfies ρ (tg_round_event_m c e a n h t z) ↔
      Tg_round_event_d I (c.eval ρ) (e.eval ρ) (a.eval ρ) (n.eval ρ) (h.eval ρ) (t.eval ρ) (z.eval ρ) := by
  simp only [tg_round_event_m, Tg_round_event_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_event_sat_l I hE, tg_aux_data_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem Tg_round_event_d.mono_l {c e a n h h' t z : M.Domain}
    (event : Tg_round_event_d I c e a n h t z) (sub : M.MemberSubset h h') :
    Tg_round_event_d I c e a n h' t z := by
  obtain ⟨⟨v, l, κ, u, aux, data⟩, answer⟩ := event
  exact ⟨⟨v, l, κ, u, aux.mono_l I sub, data⟩, answer.mono_l I sub⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原模型内部的完整游戏查询秩界

先由真实有限前缀和自然数标签图得到七个低参数，再用同一基底与完整查询池
把五个原查询一并放入给定极限秩段。所属模型使用自己的关系和自然数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem tg_query_base_scope_l {ω C γ Z : M.Domain} (hω : M.IsOmega ω)
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 12)
    (rank : V_d I γ Z) (limit : M.IsLimitOrdinal γ) (hw : (ρ.bound 0).val = ω)
    (hn : M.mem (ρ.bound 3).val ω) (low : ∀ i : Fin 7, M.mem (ρ.bound (i.castAdd 5)).val Z)
    (valid : Formula.satisfies ρ tg_query_base0_m) : ∀ i, M.mem (ρ.bound i).val Z := by
  simp only [tg_query_base0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨⟨U, D, basis, pool, root, max, bound, height, node⟩, _⟩ := valid
  let ξ := (ρ.push U).push D
  have basis := (rt_model_delta_l fs.transitive nc
    (tq_basis_delta_l (.bound 2) (.bound 7) (.bound 8) (.bound 6) (.bound 1)) ξ).mp basis
  simp only [tq_basis_sat_l hKP.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at basis
  obtain ⟨N, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l hKP nc ξ (.bound 2) (.bound 5) (.bound 1) (.bound 0) hw).mp pool
  have joint a b (ha : M.mem a Z) (hb : M.mem b Z) : ∃ P, M.mem P Z ∧ M.mem a P ∧ M.mem b P := by
    obtain ⟨W, hW, aw, bw⟩ := v_joint_bound_l I rank ha hb
    obtain ⟨P, power⟩ := v_power_exists_l I hKP rank hW
    exact ⟨P, v_power_mem_l I rank limit hW power, (power a).mpr aw, (power b).mpr bw⟩
  obtain ⟨P, hP, hp₀, hp₅⟩ := joint _ _ (low 0) (low 5)
  obtain ⟨Q, hQ, hq₆, hq₄⟩ := joint _ _ (low 6) (low 4)
  obtain ⟨B, hB, pb, qb⟩ := v_joint_bound_l I rank hP hQ
  have hU : M.mem U.val Z := v_subset_mem_l I rank hB (fun x hx => by
    rcases (basis x).mp hx with eq | eq | eq | eq
    exact eq.symm ▸ pb _ hp₀
    exact eq.symm ▸ pb _ hp₅
    exact eq.symm ▸ qb _ hq₆
    exact eq.symm ▸ qb _ hq₄)
  have actual : Tt_pool_d I ω (ρ.bound 3).val U.val D.val := ⟨N, E, names, seq, product⟩
  have hD := actual.rank_mem_l hKP hω rank limit (hw ▸ low 0) hn hU
  have trans := v_transitive_l I rank D.val hD
  have hr : M.mem (ρ.bound 7).val D.val := ((Formula.satisfies_conj_iff ..).mp root).1
  have hm : M.mem (ρ.bound 8).val D.val := ((Formula.satisfies_conj_iff ..).mp max).1
  have hb : M.mem (ρ.bound 9).val D.val := ((Formula.satisfies_conj_iff ..).mp bound).1
  have hh : M.mem (ρ.bound 10).val D.val := ((Formula.satisfies_conj_iff ..).mp height).1
  have hq : M.mem (ρ.bound 11).val D.val := ((Formula.satisfies_conj_iff ..).mp node).1
  exact Fin.cases (low 0) (Fin.cases (low 1) (Fin.cases (low 2) (Fin.cases (low 3)
    (Fin.cases (low 4) (Fin.cases (low 5) (Fin.cases (low 6) (Fin.cases (trans _ hr)
      (Fin.cases (trans _ hm) (Fin.cases (trans _ hb) (Fin.cases (trans _ hh)
        (Fin.cases (trans _ hq) (fun i => Fin.elim0 i))))))))))))

theorem tg_issued_query_scope_l {ω C γ Z : M.Domain} (hω : M.IsOmega ω)
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 46)
    (rank : V_d I γ Z) (limit : M.IsLimitOrdinal γ) (hw : (ρ.bound 0).val = ω)
    (omega : M.mem ω Z) (letters : M.mem (ρ.bound 6).val Z)
    (valid : Formula.satisfies ρ tg_issued0_m) :
    ∃ ψ χ : Env (rt_model_l C nc) 12,
      Formula.satisfies ψ tg_query_row0_m ∧
      (∀ i : Fin 6, ψ.bound ([0,1,2,3,4,6].get i) = ρ.bound ([0,1,27,28,26,23].get i)) ∧
      M.mem (ψ.bound 11).val (ρ.bound 25).val ∧ (∀ i, M.mem (ψ.bound i).val Z) ∧
      (∀ i x, Rd_entry_d i x (ψ.bound 5) →
        Tg_event_d (rt_pair_l fs.transitive nc hKP.1 fs.pair)
          (ρ.bound 4) i (ρ.bound 3) (ρ.bound 20) x) ∧
      Formula.satisfies χ tg_candidate0_m ∧
      ∀ i : Fin 12, χ.bound i = ρ.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i) := by
  let J := rt_pair_l fs.transitive nc hKP.1 fs.pair
  have ext := rt_model_ext_l hKP.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ρ).mp valid
  obtain ⟨_, x, s, _, _, _, r, m, b, q, f, endt, digits, rest, _, _, node, query, _, _, hk, hl, hn,
    χ, same, candidate, _⟩ := tg_issued_query_l J ext ρ valid
  have play i y (entry : Rd_entry_d i y s) :
      Tg_event_d J (ρ.bound 4) i (ρ.bound 3) (ρ.bound 20) y := by
    have full := ((rest.2 i y).mp entry).2
    exact ((digits.2 i y (digits.1.bound_l full).1).mp full).end_l endt
  have fn {a b f : (rt_model_l C nc).Domain} (h : Fn0_d a b f) : Fn0_d a.val b.val f.val := by
    let ε : Env (rt_model_l C nc) 3 := ⟨fun i => [a,b,f].get i, fun _ => a⟩
    exact (fn0_sat_l hKP.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ε).mp
        ((fn0_sat_l ext ε (.bound 0) (.bound 1) (.bound 2)).mpr h))
  have fx := fn digits.1
  have ft := fn state.labels
  have rest := (rt_restriction_l hKP.1 (KP.exists_pair hKP) fs.transitive nc fs.pair s x (ρ.bound 26)).mp rest
  have trans := v_transitive_l I rank
  have natural (a : (rt_model_l C nc).Domain) (ha : (rt_model_l C nc).mem a (ρ.bound 0)) : M.mem a.val Z :=
    trans ω omega a.val (hw ▸ ha)
  obtain ⟨B, hB, wb, ab⟩ := v_joint_bound_l I rank omega letters
  have hs : M.mem s.val Z := v_relation_mem_l I rank limit hB (fun p hp => by
    obtain ⟨i, v, pair⟩ := rest.1 p hp
    have bound := fx.bound_l ((rest.2 i v).mp ⟨p, pair, hp⟩).2
    exact ⟨i, wb i (hω.transitive hKP _ (hw ▸ state.round) i bound.1), v, ab v bound.2, pair⟩)
  have ht : M.mem (ρ.bound 23).val Z := v_relation_mem_l I rank limit omega (fun p hp => by
    obtain ⟨i, hi, v, hv, pair⟩ := ft.1 p hp
    exact ⟨i, hω.transitive hKP _ (hw ▸ hk) i hi, v, hw ▸ hv, pair⟩)
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff, Formula.satisfies_isEmpty_iff] at rules
  have he : ∀ a, ¬ M.mem a (ρ.bound 1).val := fun a ha =>
    rules.2.1 ⟨a, fs.transitive _ (ρ.bound 1).property a ha⟩ ha
  have heω := num_mem_l hKP.1 hω (show Num_d 0 (ρ.bound 1).val from he)
  let ψ : Env (rt_model_l C nc) 12 := ⟨fun i => [ρ.bound 0,ρ.bound 1,ρ.bound 27,ρ.bound 28,
    ρ.bound 26,s,ρ.bound 23,r,m,b,q,f].get i, ρ.free⟩
  have low : ∀ i : Fin 7, M.mem (ψ.bound (i.castAdd 5)).val Z :=
    Fin.cases (hw.symm ▸ omega) (Fin.cases (trans ω omega _ heω) (Fin.cases (natural _ hl)
      (Fin.cases (natural _ hn) (Fin.cases (natural _ hk) (Fin.cases hs
        (Fin.cases ht (fun i => Fin.elim0 i)))))))
  refine ⟨ψ, χ, query, ?_, node,
    tg_query_base_scope_l hKP hω fs nc ψ rank limit hw (hw ▸ hn) low ((Formula.satisfies_conj_iff ..).mp query).1,
    play, candidate, ?_⟩
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun i => Fin.elim0 i))))))
  · exact Fin.cases (same 0) (Fin.cases (same 1) (Fin.cases (same 2) (Fin.cases (same 3)
      (Fin.cases (same 4) (Fin.cases (same 5) (Fin.cases (same 6) (Fin.cases (same 7)
        (Fin.cases (same 8) (Fin.cases (same 9) (Fin.cases (same 10)
          (Fin.cases (same 11) (fun i => Fin.elim0 i))))))))))))

/-- 旧回答的三个查询由同一自然数基底给出，其整个查询域属于任何含 ω 的极限秩段。 -/
theorem tg_reply_base_scope_l {ω C γ Z : M.Domain} (hω : M.IsOmega ω)
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 7)
    (rank : V_d I γ Z) (limit : M.IsLimitOrdinal γ) (hw : (ρ.bound 0).val = ω)
    (hn : M.mem (ρ.bound 3).val ω) (low : ∀ i : Fin 4, M.mem (ρ.bound (i.castAdd 3)).val Z)
    (valid : Formula.satisfies ρ tg_reply_base0_m) : ∀ i, M.mem (ρ.bound i).val Z := by
  simp only [tg_reply_base0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨U, D, pair, pool, root, bound, height⟩ := valid
  let ξ := (ρ.push U).push D
  have pair := (rt_model_delta_l fs.transitive nc (pair0_delta_l (.bound 1) (.bound 2) (.bound 2)) ξ).mp pair
  simp only [pair0_sat_l hKP.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at pair
  obtain ⟨P, power⟩ := v_power_exists_l I hKP rank (low 0)
  have hP := v_power_mem_l I rank limit (low 0) power
  have hU : M.mem U.val Z := v_subset_mem_l I rank hP (fun x hx =>
    (power x).mpr (((pair x).mp hx).elim (fun eq => eq.symm ▸ (fun _ h => h))
      (fun eq => eq.symm ▸ (fun _ h => h))))
  obtain ⟨A, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l hKP nc ξ (.bound 2) (.bound 5) (.bound 1) (.bound 0) hw).mp pool
  have actual : Tt_pool_d I ω (ρ.bound 3).val U.val D.val := ⟨A, E, names, seq, product⟩
  have hD := actual.rank_mem_l hKP hω rank limit (hw ▸ low 0) hn hU
  have trans := v_transitive_l I rank D.val hD
  have hr : M.mem (ρ.bound 4).val D.val := ((Formula.satisfies_conj_iff ..).mp root).1
  have hb : M.mem (ρ.bound 5).val D.val := ((Formula.satisfies_conj_iff ..).mp bound).1
  have hh : M.mem (ρ.bound 6).val D.val := ((Formula.satisfies_conj_iff ..).mp height).1
  exact Fin.cases (low 0) (Fin.cases (low 1) (Fin.cases (low 2) (Fin.cases (low 3)
    (Fin.cases (trans _ hr) (Fin.cases (trans _ hb) (Fin.cases (trans _ hh) (fun i => Fin.elim0 i)))))))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 旧轮与当前原策略历史的有界对应

对应携带原自然数标签列、回答的域和类型；事件量词仍限制在反射层内。
整份对应解释在当前模型的原关系中，初等图逐坐标搬运。构造和读取共用
所属结构内部的事件证明；原关系中的历史增长保留每一条旧对应。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_event_in0_m : Formula 1 8 := lr_rel_m tg_round_event0_m .newest (fun i => .bound i.succ)

theorem tg_event_in0_closed_l : tg_event_in0_m.FreeClosed :=
  lr_rel_closed_l _ tg_round_event0_closed_l _ _ rfl (fun _ => rfl)

theorem tg_event_in0_delta_l : tg_event_in0_m.IsDelta0 := lr_rel_delta_l ..

-- 十个坐标依次为 ω、反射层、三阶段时钟、零、一、轮号、当前历史、旧标签、旧域、旧类型。
def tg_trace0_m : Formula 1 10 :=
  let v : Fin 10 → Term 10 := Term.bound
  .conj (.mem (v 5) (v 1)) (.conj (.mem (v 7) (v 1))
    (Formula.existsMem (v 0) (Formula.existsMem (v 1).weaken
      (.conj (fn0_m (.bound 1) (.bound 2) (.bound 9))
        (.conj (kpair0_m .newest (.bound 10) (.bound 11))
          (tg_event_in0_m.bind
            (fun i => [.bound 3, .bound 4, .bound 5, .bound 6, .bound 7, .bound 8, .bound 9, .newest].get i)))))))

theorem tg_trace0_closed_l : tg_trace0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_trace0_m, Definitional.Formula.FreeClosed]
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_event_in0_closed_l
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))

theorem tg_trace0_delta_l : tg_trace0_m.IsDelta0 :=
  .conj (.mem ..) (.conj (.mem ..) (.existsMem _ (.existsMem _
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (tg_event_in0_delta_l.bind_l _))))))

variable (I : kpair_convention_l.Interpretation M)

def Tg_trace_d (X R ω C c e a n h t τ w : M.Domain) : Prop :=
  Rr_truth_d I X R tg_trace0_m (fun i => [ω,C,c,e,a,n,h,t,τ,w].get i)

def tg_trace_m {d} (X R ω C c e a n h t τ w : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) tg_trace0_m X R (fun i => [ω,C,c,e,a,n,h,t,τ,w].get i)

@[simp] theorem tg_trace_closed_l {d} (X R ω C c e a n h t τ w : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hw : ω.freeSupport = [])
    (hC : C.freeSupport = []) (hc : c.freeSupport = []) (he : e.freeSupport = [])
    (ha : a.freeSupport = []) (hn : n.freeSupport = []) (hh : h.freeSupport = [])
    (ht : t.freeSupport = []) (hτ : τ.freeSupport = []) (hw' : w.freeSupport = []) :
    (tg_trace_m X R ω C c e a n h t τ w).FreeClosed :=
  rr_truth_closed_l _ tg_trace0_closed_l _ _ _ hX hR
    (Fin.cases hw (Fin.cases hC (Fin.cases hc (Fin.cases he (Fin.cases ha
      (Fin.cases hn (Fin.cases hh (Fin.cases ht (Fin.cases hτ (Fin.cases hw' (fun i => Fin.elim0 i)))))))))))

theorem tg_trace_sat_l {d} (ρ : Env M d) (X R ω C c e a n h t τ w : Term d) :
    Formula.satisfies ρ (tg_trace_m X R ω C c e a n h t τ w) ↔
      Tg_trace_d I (X.eval ρ) (R.eval ρ) (ω.eval ρ) (C.eval ρ) (c.eval ρ) (e.eval ρ) (a.eval ρ) (n.eval ρ)
        (h.eval ρ) (t.eval ρ) (τ.eval ρ) (w.eval ρ) := by
  rw [tg_trace_m, rr_truth_sat_l I _ _ tg_trace0_closed_l]
  have row : (fun i : Fin 10 => ([ω,C,c,e,a,n,h,t,τ,w].get i).eval ρ) =
      (fun i => [ω.eval ρ,C.eval ρ,c.eval ρ,e.eval ρ,a.eval ρ,n.eval ρ,h.eval ρ,t.eval ρ,τ.eval ρ,w.eval ρ].get i) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
  exact row ▸ Iff.rfl

/-- 原结构内部的事件见证，构造与读取共用同一公式。 -/
theorem tg_trace0_build_l (hE : Extensional M) {ω C k τ w : M.Domain}
    (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (c e a n h t z : (rt_model_l C nc).Domain) (hk : M.mem k ω) (fn : Fn0_d k ω t.val)
    (pair : KPair_d M z.val τ w) (event : Formula.satisfies
      (⟨fun i => [c, e, a, n, h, t, z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7) tg_round_event0_m) :
    Formula.satisfies (⟨fun i => [ω,C,c.val,e.val,a.val,n.val,h.val,t.val,τ,w].get i, fun _ => ω⟩ : Env M 10)
      tg_trace0_m := by
  apply (Formula.satisfies_conj_iff ..).mpr
  refine ⟨n.property, (Formula.satisfies_conj_iff ..).mpr ⟨t.property, ?_⟩⟩
  apply (Formula.satisfies_existsMem_iff ..).mpr
  refine ⟨k, hk, (Formula.satisfies_existsMem_iff ..).mpr ⟨z.val, z.property, ?_⟩⟩
  apply (Formula.satisfies_conj_iff ..).mpr
  refine ⟨(fn0_sat_l hE ..).mpr fn, (Formula.satisfies_conj_iff ..).mpr ⟨(kpair0_sat_l hE ..).mpr pair, ?_⟩⟩
  have rel := (sc_relative_sat_l trans nc tg_round_event0_m tg_round_event0_closed_l
    (⟨fun i => [c, e, a, n, h, t, z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7)
    ((⟨fun i => [c.val, e.val, a.val, n.val, h.val, t.val, z.val].get i, fun _ => ω⟩ : Env M 7).push C)
    .newest (fun i => .bound i.succ)
    rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))).mpr event
  apply (Formula.satisfies_bind ..).mpr
  apply (Formula.closed_env_l tg_event_in0_m tg_event_in0_closed_l (ρ := _) (η := _) ?_).mp rel
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) i

/-- 隶属实例将同一原结构内部的事件见证写入其关系码。 -/
theorem tg_trace_build_l (hE : Extensional M) {b X R ω C k τ w : M.Domain}
    (model : Smem_d I b X R) (xt : M.TransitiveSet X) (hC : M.mem C X) (hw : M.mem ω X)
    (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (c e a n h t z : (rt_model_l C nc).Domain) (hk : M.mem k ω) (fn : Fn0_d k ω t.val)
    (pair : KPair_d M z.val τ w) (event : Formula.satisfies
      (⟨fun i => [c, e, a, n, h, t, z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7) tg_round_event0_m) :
    Tg_trace_d I X R ω C c.val e.val a.val n.val h.val t.val τ w := by
  apply (rr_truth_mem_l I xt model tg_trace0_m tg_trace0_delta_l _).mpr
  have low := pair.mem_l M trans z.property
  have member {v : M.Domain} (hv : M.mem v C) := xt C hC v hv
  exact ⟨Fin.cases hw (Fin.cases hC (Fin.cases (member c.property) (Fin.cases (member e.property)
    (Fin.cases (member a.property) (Fin.cases (member n.property) (Fin.cases (member h.property)
      (Fin.cases (member t.property) (Fin.cases (member low.1) (Fin.cases (member low.2) (fun i => Fin.elim0 i)))))))))),
    tg_trace0_build_l hE trans nc c e a n h t z hk fn pair event⟩

/-- 在所属结构内读取同一标签、回答对及原事件。 -/
theorem tg_trace0_read_l (hE : Extensional M) {ω C n t τ w : M.Domain}
    (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (c e a h : (rt_model_l C nc).Domain)
    (trace : Formula.satisfies
      (⟨fun i => [ω,C,c.val,e.val,a.val,n,h.val,t,τ,w].get i, fun _ => ω⟩ : Env M 10) tg_trace0_m) :
    ∃ k, M.mem k ω ∧ Fn0_d k ω t ∧ ∃ n' t' z : (rt_model_l C nc).Domain,
      n'.val = n ∧ t'.val = t ∧ KPair_d M z.val τ w ∧ Formula.satisfies
        (⟨fun i => [c, e, a, n', h, t', z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7) tg_round_event0_m := by
  obtain ⟨hn, trace⟩ := (Formula.satisfies_conj_iff ..).mp trace
  obtain ⟨ht, trace⟩ := (Formula.satisfies_conj_iff ..).mp trace
  obtain ⟨k, hk, trace⟩ := (Formula.satisfies_existsMem_iff ..).mp trace
  obtain ⟨z, hz, trace⟩ := (Formula.satisfies_existsMem_iff ..).mp trace
  obtain ⟨fn, trace⟩ := (Formula.satisfies_conj_iff ..).mp trace
  obtain ⟨pair, event⟩ := (Formula.satisfies_conj_iff ..).mp trace
  have fn := (fn0_sat_l hE ..).mp fn
  have pair := (kpair0_sat_l hE ..).mp pair
  refine ⟨k, hk, fn, ⟨n, hn⟩, ⟨t, ht⟩, ⟨z, hz⟩, rfl, rfl, pair, ?_⟩
  have event := (Formula.satisfies_bind ..).mp event
  have rel : Formula.satisfies
      ((⟨fun i => [c.val, e.val, a.val, n, h.val, t, z].get i, fun _ => ω⟩ : Env M 7).push C) tg_event_in0_m := by
    apply (Formula.closed_env_l tg_event_in0_m tg_event_in0_closed_l (ρ := _) (η := _) ?_).mp event
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))) i
  exact (sc_relative_sat_l trans nc tg_round_event0_m tg_round_event0_closed_l
    (⟨fun i => [c, e, a, ⟨n, hn⟩, h, ⟨t, ht⟩, ⟨z, hz⟩].get i, fun _ => ⟨z, hz⟩⟩ : Env (rt_model_l C nc) 7)
    ((⟨fun i => [c.val, e.val, a.val, n, h.val, t, z].get i, fun _ => ω⟩ : Env M 7).push C)
    .newest (fun i => .bound i.succ)
    rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))).mp rel

/-- 隶属实例沿现用语义读取，事件主体不再另证。 -/
theorem Tg_trace_d.read_l (hE : Extensional M) {b X R ω C n t τ w : M.Domain}
    (model : Smem_d I b X R) (xt : M.TransitiveSet X) (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (c e a h : (rt_model_l C nc).Domain)
    (trace : Tg_trace_d I X R ω C c.val e.val a.val n h.val t τ w) :
    ∃ k, M.mem k ω ∧ Fn0_d k ω t ∧ ∃ n' t' z : (rt_model_l C nc).Domain,
      n'.val = n ∧ t'.val = t ∧ KPair_d M z.val τ w ∧ Formula.satisfies
        (⟨fun i => [c, e, a, n', h, t', z].get i, fun _ => z⟩ : Env (rt_model_l C nc) 7) tg_round_event0_m :=
  tg_trace0_read_l hE trans nc c e a h ((rr_truth_mem_l I xt model tg_trace0_m tg_trace0_delta_l _).mp trace).2

/-- 十个对象码在其原所属结构中的逐坐标解释。 -/
theorem tg_trace_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (ω C c e a n h t τ w : (smdl_structure_l I (R := R) nx).Domain) :
    Tg_trace_d I X R ω.val C.val c.val e.val a.val n.val h.val t.val τ.val w.val ↔
      Formula.satisfies (⟨fun i => [ω,C,c,e,a,n,h,t,τ,w].get i, fun _ => ω⟩ :
        Env (smdl_structure_l I (R := R) nx) 10) tg_trace0_m := by
  have values : (fun i : Fin 10 => ([ω,C,c,e,a,n,h,t,τ,w].get i).val) =
      (fun i : Fin 10 => [ω.val,C.val,c.val,e.val,a.val,n.val,h.val,t.val,τ.val,w.val].get i) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
  change Rr_truth_d I X R tg_trace0_m _ ↔ _
  rw [← values]
  exact rr_truth_native_l I nx tg_trace0_m tg_trace0_closed_l _

/-- 同一原模型的历史增长保留每一条旧事件，不要求载体是背景传递集。 -/
theorem Tg_trace_d.native_mono_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (hE : Extensional (smdl_structure_l I (R := R) nx))
    (ω C : (smdl_structure_l I (R := R) nx).Domain)
    (trans : (smdl_structure_l I (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (c e a h h' : (rt_model_l C nc).Domain) (n t τ w : (smdl_structure_l I (R := R) nx).Domain)
    (trace : Tg_trace_d I X R ω.val C.val c.val.val e.val.val a.val.val n.val h.val.val t.val τ.val w.val)
    (sub : (smdl_structure_l I (R := R) nx).MemberSubset h.val h'.val) :
    Tg_trace_d I X R ω.val C.val c.val.val e.val.val a.val.val n.val h'.val.val t.val τ.val w.val := by
  have raw := (tg_trace_native_l I nx ω C c.val e.val a.val n h.val t τ w).mp trace
  obtain ⟨k, hk, fn, n', t', z, en, et, pair, event⟩ := tg_trace0_read_l hE trans nc c e a h raw
  have ext := rt_model_ext_l hE trans nc
  have event := ((tg_round_event_sat_l J ext ..).mp event).mono_l J (fun x hx => sub x.val hx)
  apply (tg_trace_native_l I nx ω C c.val e.val a.val n h'.val t τ w).mpr
  exact en ▸ et ▸ tg_trace0_build_l hE trans nc c e a n' h' t' z hk (et.symm ▸ fn) pair
    ((tg_round_event_sat_l J ext ..).mpr event)

/-- 旧历史逐项包含于新历史时，整份旧轮对应保留。 -/
theorem Tg_trace_d.mono_l (hE : Extensional M) {b X R ω C n t τ w : M.Domain}
    (model : Smem_d I b X R) (xt : M.TransitiveSet X) (trans : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (c e a h h' : (rt_model_l C nc).Domain) (trace : Tg_trace_d I X R ω C c.val e.val a.val n h.val t τ w)
    (sub : M.MemberSubset h.val h'.val) : Tg_trace_d I X R ω C c.val e.val a.val n h'.val t τ w := by
  obtain ⟨k, hk, fn, n', t', z, en, et, pair, event⟩ := trace.read_l I hE model xt trans nc c e a h
  have ext := rt_model_ext_l hE trans nc
  have event := ((tg_round_event_sat_l J ext ..).mp event).mono_l J (fun x hx => sub x.val hx)
  exact en ▸ et ▸ tg_trace_build_l I hE model xt
    (trace.elim fun dom _ => dom 1) (trace.elim fun dom _ => dom 0) trans nc c e a n' h' t' z
    hk (et.symm ▸ fn) pair ((tg_round_event_sat_l J ext ..).mpr event)

/-- 原关系初等图搬运全部十个坐标，不预设自然数、标签或回答的像等于原值。 -/
theorem Tg_trace_d.map_l (hZF : M.Models ZF)
    {ω X R b Y S d j o o' C C' c c' e e' a a' n n' h h' t t' τ τ' w w' : M.Domain}
    (hw : M.IsOmega ω) (mx : Smdl_d I b X R) (my : Smdl_d I d Y S) (map : Smap_d I ω b d X Y j)
    (io : M.PairMember I o o' j) (iC : M.PairMember I C C' j) (ic : M.PairMember I c c' j)
    (ie : M.PairMember I e e' j) (ia : M.PairMember I a a' j) (inn : M.PairMember I n n' j)
    (ih : M.PairMember I h h' j) (it : M.PairMember I t t' j)
    (iτ : M.PairMember I τ τ' j) (iw : M.PairMember I w w' j) (trace : Tg_trace_d I X R o C c e a n h t τ w) :
    Tg_trace_d I Y S o' C' c' e' a' n' h' t' τ' w' :=
  Rr_truth_d.map_l I hZF hw mx my map tg_trace0_closed_l trace
    (Fin.cases io (Fin.cases iC (Fin.cases ic (Fin.cases ie (Fin.cases ia (Fin.cases inn
      (Fin.cases ih (Fin.cases it (Fin.cases iτ (Fin.cases iw (fun i => Fin.elim0 i)))))))))))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实数前缀与同一原历史逐点对应

前缀证书在当前载体与原关系中解释，事件量词限制在该模型的反射层内。
初等图直接搬运这份真值；实际隶属实例再读取逐点事件，由时钟和历史函数
的单值性证明两份前缀一致。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_play_body0_m : Formula 1 4 := .forallE (.forallE
  (.imp (rd_entry0_m (.bound 1) .newest (.bound 5))
    (tg_event_m (.bound 2) (.bound 1) (.bound 3) (.bound 4) .newest)))

theorem tg_play_body0_closed_l : tg_play_body0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_play_body0_m, Definitional.Formula.FreeClosed]

def tg_play0_m : Formula 1 5 := .conj (.mem (.bound 4) (.bound 0))
  (lr_rel_m tg_play_body0_m (.bound 0) (fun i => .bound i.succ))
theorem tg_play0_closed_l : tg_play0_m.FreeClosed :=
  ⟨⟨rfl, rfl⟩, lr_rel_closed_l _ tg_play_body0_closed_l _ _ rfl (fun _ => rfl)⟩
theorem tg_play0_delta_l : tg_play0_m.IsDelta0 := .conj (.mem ..) (lr_rel_delta_l ..)

variable (I : kpair_convention_l.Interpretation M)

def Tg_play_d (X R C c b h s : M.Domain) : Prop :=
  Rr_truth_d I X R tg_play0_m (fun i => [C,c,b,h,s].get i)

def tg_play_m {d} (X R C c b h s : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) tg_play0_m X R (fun i => [C,c,b,h,s].get i)

@[simp] theorem tg_play_closed_l {d} (X R C c b h s : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hC : C.freeSupport = [])
    (hc : c.freeSupport = []) (hb : b.freeSupport = []) (hh : h.freeSupport = []) (hs : s.freeSupport = []) :
    (tg_play_m X R C c b h s).FreeClosed :=
  rr_truth_closed_l _ tg_play0_closed_l _ _ _ hX hR
    (Fin.cases hC (Fin.cases hc (Fin.cases hb (Fin.cases hh (Fin.cases hs (fun i => Fin.elim0 i))))))

theorem tg_play_sat_l {d} (ρ : Env M d) (X R C c b h s : Term d) :
    Formula.satisfies ρ (tg_play_m X R C c b h s) ↔
      Tg_play_d I (X.eval ρ) (R.eval ρ) (C.eval ρ) (c.eval ρ) (b.eval ρ) (h.eval ρ) (s.eval ρ) := by
  rw [tg_play_m, rr_truth_sat_l I _ _ tg_play0_closed_l]
  have row : (fun i : Fin 5 => ([C,c,b,h,s].get i).eval ρ) =
      (fun i => [C.eval ρ,c.eval ρ,b.eval ρ,h.eval ρ,s.eval ρ].get i) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))
  exact row ▸ Iff.rfl

theorem Tg_play_d.member_l {X R C c b h s : M.Domain} (p : Tg_play_d I X R C c b h s) : M.PairMember I s C R :=
  p.elim fun _ valid => ((Formula.satisfies_conj_iff ..).mp valid).1

/-- 只有实际隶属关系码才能把前缀成员关系读成背景成员关系。 -/
theorem Tg_play_d.mem_l {a X R C c b h s : M.Domain} (p : Tg_play_d I X R C c b h s)
    (model : Smem_d I a X R) : M.mem s C := ((model.2 s C).mp (p.member_l I)).2.2

/-- 原关系中的反射层直接读取全部前缀事件，不要求所属模型是背景隶属模型。 -/
theorem tg_play_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (ct : (smdl_structure_l I (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h s : (rt_model_l C nc).Domain) :
    Tg_play_d I X R C.val c.val.val b.val.val h.val.val s.val.val ↔
      ∀ i x, Rd_entry_d i x s → Tg_event_d J c i b h x := by
  let N := smdl_structure_l I (R := R) nx
  let ρ : Env (rt_model_l C nc) 4 := ⟨fun i => [c,b,h,s].get i,fun _ => c⟩
  let η : Env N 5 := ⟨fun i => [C,c.val,b.val,h.val,s.val].get i,fun _ => C⟩
  have row : (fun i : Fin 5 => (η.bound i).val) =
      (fun i => [C.val,c.val.val,b.val.val,h.val.val,s.val.val].get i) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))
  have native : Tg_play_d I X R C.val c.val.val b.val.val h.val.val s.val.val ↔
      Formula.satisfies η tg_play0_m :=
    Eq.mp (congrArg (fun v => Rr_truth_d I X R tg_play0_m v ↔ Formula.satisfies η tg_play0_m) row)
      (rr_truth_native_l I nx tg_play0_m tg_play0_closed_l η.bound)
  apply native.trans
  have rel := sc_relative_sat_l ct nc tg_play_body0_m tg_play_body0_closed_l ρ η
    (.bound 0) (fun i => .bound i.succ) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  change (N.mem s.val C ∧ Formula.satisfies η (lr_rel_m tg_play_body0_m (.bound 0) (fun i => .bound i.succ))) ↔ _
  rw [and_iff_right s.property,rel]
  simp only [tg_play_body0_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    rd_entry0_sat_l (rt_model_ext_l ext ct nc),tg_event_sat_l J (rt_model_ext_l ext ct nc)]
  rfl

/-- 原关系内的历史包含保留全部短前缀事件。 -/
theorem Tg_play_d.native_mono_l {X R s : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (ct : (smdl_structure_l I (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (c b h h' : (rt_model_l C nc).Domain)
    (play : Tg_play_d I X R C.val c.val.val b.val.val h.val.val s)
    (sub : (smdl_structure_l I (R := R) nx).MemberSubset h.val h'.val) :
    Tg_play_d I X R C.val c.val.val b.val.val h'.val.val s := by
  let s₀ : (smdl_structure_l I (R := R) nx).Domain := ⟨s,play.elim fun m _ => m 4⟩
  let t : (rt_model_l C nc).Domain := ⟨s₀,play.member_l I⟩
  exact (tg_play_native_l I nx ext C ct nc J c b h' t).mpr fun i x hi =>
    ((tg_play_native_l I nx ext C ct nc J c b h t).mp play i x hi).mono_l J (fun p hp => sub p.val hp)

/-- 传递隶属实例中的字面读取，关系码始终取自当前模型。 -/
theorem tg_play_read_l (hE : Extensional M) {a X R C : M.Domain} (model : Smem_d I a X R)
    (xt : M.TransitiveSet X) (hC : M.mem C X) (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h s : (rt_model_l C nc).Domain) :
    Tg_play_d I X R C c.val b.val h.val s.val ↔ ∀ i x, Rd_entry_d i x s → Tg_event_d J c i b h x := by
  let ρ : Env (rt_model_l C nc) 4 := ⟨fun i => [c,b,h,s].get i, fun _ => c⟩
  let η : Env M 5 := ⟨fun i => [C,c.val,b.val,h.val,s.val].get i, fun _ => C⟩
  have domain : ∀ i, M.mem (η.bound i) X := Fin.cases hC (Fin.cases (xt C hC c.val c.property)
    (Fin.cases (xt C hC b.val b.property) (Fin.cases (xt C hC h.val h.property)
      (Fin.cases (xt C hC s.val s.property) (fun i => Fin.elim0 i)))))
  apply (rr_truth_mem_l I xt model tg_play0_m tg_play0_delta_l η.bound).trans
  rw [and_iff_right domain]
  have rel := sc_relative_sat_l ct nc tg_play_body0_m tg_play_body0_closed_l ρ η
    (.bound 0) (fun i => .bound i.succ) rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  change (M.mem s.val C ∧ Formula.satisfies η (lr_rel_m tg_play_body0_m (.bound 0) (fun i => .bound i.succ))) ↔ _
  rw [and_iff_right s.property, rel]
  simp only [tg_play_body0_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l (rt_model_ext_l hE ct nc), tg_event_sat_l J (rt_model_ext_l hE ct nc)]
  rfl

theorem Tg_play_d.mono_l (hE : Extensional M) {a X R C s : M.Domain} (model : Smem_d I a X R)
    (xt : M.TransitiveSet X) (hC : M.mem C X) (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h h' : (rt_model_l C nc).Domain)
    (play : Tg_play_d I X R C c.val b.val h.val s) (sub : M.MemberSubset h.val h'.val) :
    Tg_play_d I X R C c.val b.val h'.val s := by
  have hs := play.mem_l I model
  exact (tg_play_read_l I hE model xt hC ct nc J c b h' ⟨s,hs⟩).mpr fun i x hi =>
    ((tg_play_read_l I hE model xt hC ct nc J c b h ⟨s,hs⟩).mp play i x hi).mono_l J (fun p hp => sub p.val hp)

/-- 原关系初等图搬运前缀证书，源与目标均不要求背景传递。 -/
theorem Tg_play_d.map_l (hZF : M.Models ZF) {ω X R d Y S e j C C' c c' b b' h h' s s' : M.Domain}
    (hw : M.IsOmega ω) (mx : Smdl_d I d X R) (my : Smdl_d I e Y S) (map : Smap_d I ω d e X Y j)
    (iC : M.PairMember I C C' j) (ic : M.PairMember I c c' j) (ib : M.PairMember I b b' j)
    (ih : M.PairMember I h h' j) (is : M.PairMember I s s' j) (play : Tg_play_d I X R C c b h s) :
    Tg_play_d I Y S C' c' b' h' s' :=
  Rr_truth_d.map_l I hZF hw mx my map tg_play0_closed_l play
    (Fin.cases iC (Fin.cases ic (Fin.cases ib (Fin.cases ih (Fin.cases is (fun i => Fin.elim0 i))))))

theorem Tg_play_d.entry_eq_l (hE : Extensional M) {a X R C s t i x y : M.Domain} (model : Smem_d I a X R)
    (xt : M.TransitiveSet X) (hC : M.mem C X) (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m)
    (left : Tg_play_d I X R C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val s)
    (right : Tg_play_d I X R C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val t)
    (hi : Rd_entry_d i x s) (hy : Rd_entry_d i y t) : x = y := by
  have hs := left.mem_l I model
  have ht := right.mem_l I model
  have state := (tg_issued_sat_l J (rt_model_ext_l hE ct nc) ρ).mp valid
  have ix := rd_entry_transitive_l ct hs hi
  have iy := rd_entry_transitive_l ct ht hy
  have ex := (tg_play_read_l I hE model xt hC ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) ⟨s,hs⟩).mp left
    ⟨i,ix.1⟩ ⟨x,ix.2⟩ ((rt_entry_l ct nc hE _ _ _).mpr hi)
  have ey := (tg_play_read_l I hE model xt hC ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) ⟨t,ht⟩).mp right
    ⟨i,ix.1⟩ ⟨y,iy.2⟩ ((rt_entry_l ct nc hE _ _ _).mpr hy)
  exact congrArg Subtype.val (tg_control_event_unique_l J (rt_model_ext_l hE ct nc) _ state.control state.history ex ey)

theorem Tg_play_d.subset_l (hE : Extensional M) {a X R C s t n m : M.Domain} (model : Smem_d I a X R)
    (xt : M.TransitiveSet X) (hC : M.mem C X) (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m)
    (left : Tg_play_d I X R C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val s)
    (right : Tg_play_d I X R C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val t)
    (gs : Tg_graph_d I n s) (gt : Tg_graph_d I m t) (nm : M.MemberSubset n m) : M.MemberSubset s t := by
  have read {p i x : M.Domain} : I.Codes p i x ↔ KPair_d M p i x :=
    (I.satisfies_code_iff (⟨fun k => [p,i,x].get k,fun _ => p⟩ : Env M 3) (.bound 0) (.bound 1) (.bound 2)).symm.trans
      (kpair_sat_l M hE _ _ _ _)
  intro p hp
  obtain ⟨i,x,pair⟩ := gs.1.1 p hp
  obtain ⟨y,q,qp,hq⟩ := (gt.2 i).mp (nm i ((gs.2 i).mpr ⟨x,p,pair,hp⟩))
  have eq := left.entry_eq_l I hE model xt hC ct nc J ρ valid right
    ⟨p,read.mp pair,hp⟩ ⟨q,read.mp qp,hq⟩
  exact I.unique qp (eq ▸ pair) ▸ hq

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系模型中两份真实前缀的包含

两图的定义域包含及同一历史的事件唯一性逐点确定相同字母。
全部配对和历史关系在所属模型中解释，不要求原对象码字面固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem Tg_play_d.native_subset_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (hE : Extensional (smdl_structure_l I (R := R) nx))
    (hP : ∀ a b : (smdl_structure_l I (R := R) nx).Domain, ∃ p, Pair_d _ p a b)
    (C : (smdl_structure_l I (R := R) nx).Domain)
    (ct : (smdl_structure_l I (R := R) nx).TransitiveSet C)
    (nc : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc))
    (ρ : Env (rt_model_l C nc) 46) (issued : Formula.satisfies ρ tg_issued0_m)
    (n m : (smdl_structure_l I (R := R) nx).Domain) (s t : (rt_model_l C nc).Domain)
    (left : Tg_play_d I X R C.val (ρ.bound 4).val.val (ρ.bound 3).val.val (ρ.bound 20).val.val s.val.val)
    (right : Tg_play_d I X R C.val (ρ.bound 4).val.val (ρ.bound 3).val.val (ρ.bound 20).val.val t.val.val)
    (gs : Tg_graph_d (kpair_interpretation_l _ hE hP) n s.val)
    (gt : Tg_graph_d (kpair_interpretation_l _ hE hP) m t.val)
    (nm : (smdl_structure_l I (R := R) nx).MemberSubset n m) :
    (smdl_structure_l I (R := R) nx).MemberSubset s.val t.val := by
  let N := smdl_structure_l I (R := R) nx
  have ext := rt_model_ext_l hE ct nc
  have state := (tg_issued_sat_l J ext ρ).mp issued
  have ls := (tg_play_native_l I nx hE C ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) s).mp left
  have lt := (tg_play_native_l I nx hE C ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) t).mp right
  intro p hp
  obtain ⟨i,x,pair⟩ := gs.1.1 p hp
  have ix : Rd_entry_d i x s.val := ⟨p,pair,hp⟩
  obtain ⟨y,q,qp,hq⟩ := (gt.2 i).mp (nm i ((gs.2 i).mpr ⟨x,ix⟩))
  have iy : Rd_entry_d i y t.val := ⟨q,qp,hq⟩
  have ins := rd_entry_transitive_l ct s.property ix
  have int := rd_entry_transitive_l ct t.property iy
  have eq := tg_control_event_unique_l J ext _ state.control state.history
    (ls ⟨i,ins.1⟩ ⟨x,ins.2⟩ ((rt_entry_l ct nc hE _ _ _).mpr ix))
    (lt ⟨i,ins.1⟩ ⟨y,int.2⟩ ((rt_entry_l ct nc hE _ _ _).mpr iy))
  have xy : x = y := congrArg Subtype.val eq
  exact kpair_unique_l N hE qp (xy ▸ pair) ▸ hq

end YesMetaZFC.SetTheory.LargeCardinal
