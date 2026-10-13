import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssuedQuery

/-! # 原三阶段历史的旧事件与域增长

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
