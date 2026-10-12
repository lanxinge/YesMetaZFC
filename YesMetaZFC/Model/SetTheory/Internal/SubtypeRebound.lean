import YesMetaZFC.Model.SetTheory.Internal.SubtypeColumn
import YesMetaZFC.Model.SetTheory.Internal.Subtype

/-! # 子类型查询的定义域参数更换

只更换名字列中较大定义域的槽位；候选类型、实际元组和排列均不变。
统一性质只在常量域、名字列空间和查询域内量化，因而可搬到超幂的新查询。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_rebound_d (ω n b z U N E D t : M.Domain) (σ : Fin 7 → M.Domain) : Prop :=
  ∀ κ, M.mem κ U → ∀ ξ, M.mem ξ U → ∀ τ, M.mem τ U → ∀ m, M.mem m ω → ∀ w, M.mem w U →
    M.IsLimitOrdinal κ ∧ M.IsLimitOrdinal ξ ∧ M.IsLimitOrdinal τ ∧ M.mem τ κ ∧ M.mem τ ξ →
    ∀ C, M.mem C E → Ts_column_d ω n κ τ m N w b σ C →
    ∀ C', M.mem C' E → Ts_column_d ω n ξ τ m N w b σ C' →
    ∀ q, M.mem q D → ∀ q', M.mem q' D → KPair_d M q z C → KPair_d M q' z C' →
      (M.mem q t ↔ M.mem q' t)

def ts_rebound_m {d} (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  let l₅ (x : Term d) := x.weaken.weaken.weaken.weaken.weaken
  let l₆ (x : Term d) := (l₅ x).weaken
  let l₇ (x : Term d) := (l₆ x).weaken
  let l₉ (x : Term d) := (l₇ x).weaken.weaken
  let last : Formula 1 (d+9) := .imp (kpair0_m (.bound 1) (l₉ z) (.bound 3))
    (.imp (kpair0_m .newest (l₉ z) (.bound 2)) (.iff (.mem (.bound 1) (l₉ t)) (.mem .newest (l₉ t))))
  let second : Formula 1 (d+7) := .imp
    (ts_column_m (l₇ ω) (l₇ n) (.bound 5) (.bound 4) (.bound 3) (l₇ N) (.bound 2) (l₇ b) .newest (fun i => l₇ (σ i)))
    (Formula.forallMem (l₇ D) (Formula.forallMem (l₇ D).weaken last))
  let first : Formula 1 (d+6) := .imp
    (ts_column_m (l₆ ω) (l₆ n) (.bound 5) (.bound 3) (.bound 2) (l₆ N) (.bound 1) (l₆ b) .newest (fun i => l₆ (σ i)))
    (Formula.forallMem (l₆ E) second)
  let guard : Formula 1 (d+5) := .conj (KP.limit0_m (.bound 4)) (.conj (KP.limit0_m (.bound 3))
    (.conj (KP.limit0_m (.bound 2)) (.conj (.mem (.bound 2) (.bound 4)) (.mem (.bound 2) (.bound 3)))))
  Formula.forallMem U (Formula.forallMem U.weaken (Formula.forallMem U.weaken.weaken
    (Formula.forallMem ω.weaken.weaken.weaken (Formula.forallMem U.weaken.weaken.weaken.weaken
      (.imp guard (Formula.forallMem (l₅ E) first))))))

@[simp] theorem ts_rebound_closed_l {d} (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hU : U.freeSupport = []) (hN : N.freeSupport = []) (hE : E.freeSupport = []) (hD : D.freeSupport = [])
    (ht : t.freeSupport = []) (hσ : ∀ i, (σ i).freeSupport = []) : (ts_rebound_m ω n b z U N E D t σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_rebound_m, Definitional.Formula.FreeClosed, hw, hn, hb, hz, hU, hN, hE, hD, ht, hσ]

theorem ts_rebound_delta_l {d} (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d) :
    (ts_rebound_m ω n b z U N E D t σ).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
    (.imp (.conj (KP.limit0_delta_l ..) (.conj (KP.limit0_delta_l ..) (.conj (KP.limit0_delta_l ..) (.conj (.mem ..) (.mem ..)))))
      (.forallMem _ (.imp (ts_column_delta_l ..) (.forallMem _ (.imp (ts_column_delta_l ..)
        (.forallMem _ (.forallMem _ (.imp (kpair0_delta_l ..) (.imp (kpair0_delta_l ..) (.iff (.mem ..) (.mem ..)))))))))))))))

theorem ts_rebound_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω n b z U N E D t : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_rebound_m ω n b z U N E D t σ) ↔ Ts_rebound_d
      (ω.eval ρ) (n.eval ρ) (b.eval ρ) (z.eval ρ) (U.eval ρ) (N.eval ρ) (E.eval ρ) (D.eval ρ) (t.eval ρ)
      (fun i => (σ i).eval ρ) := by
  simp only [ts_rebound_m, Ts_rebound_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, KP.limit0_sat_l hKP, Formula.satisfies_mem_iff, ts_column_sat_l hKP.1,
    kpair0_sat_l hKP.1, Formula.satisfies_iff_iff, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ts_program_d.rebound_l {ω n b a z η Y c R s δ U N E D t : M.Domain}
    (hω : M.IsOmega ω) {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n s δ U D t)
    (names : Tn_names_d n U N) (hωU : M.mem ω U) (hωsub : M.MemberSubset ω U) : Ts_rebound_d ω n b z U N E D t σ := by
  intro κ hκU ξ hξU τ hτU m hm w hw ⟨hκ, hξ, hτ, hτκ, hτξ⟩ C _ col C' _ col' q _ q' _ pair pair'
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hτ.1
  obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) τ τ
  obtain ⟨V, hV⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B p
  have constants x : M.mem x V ↔ M.mem x B ∨ x = τ :=
    (hV x).trans (or_congr Iff.rfl ((hp x).trans ⟨fun h => h.elim id id, Or.inl⟩))
  obtain ⟨Q, pool⟩ := tt_pool_exists_l I hZF hω m V
  have cq := col.query_l names ⟨hw, hωsub m hm, hωsub n prog.finite, hτU, hκU, hωU⟩ pair
  have cq' := col'.query_l names ⟨hw, hωsub m hm, hωsub n prog.finite, hτU, hξU, hωU⟩ pair'
  exact (cq.read_l hZF hω prog hY model type hκ hτ hτκ hm hB constants pool).trans
    (cq'.read_l hZF hω prog hY model type hξ hτ hτξ hm hB constants pool).symm

end YesMetaZFC.SetTheory.Internal
