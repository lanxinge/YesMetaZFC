import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakUnion
import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakLimit
import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakSuccessor

/-! # 弱迭代的实际应答及其三种延拓

应答记录所选枝和下一行状态。后继步保留该枝的原商投影与根腿；
极限步保留整段历史的规范腿。合法性只用于证明这些实际应答存在。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Wi_tree_d (t T Q G E L : M.Domain) : Prop := ∃ p, KPair_d M p E L ∧ Rd_quad_d t T Q G p
def Wi_past_d (H Q G P : M.Domain) : Prop :=
  ∀ i U Q' G' P', Wi_at_d H i U Q' G' P' → Wi_keep_d Q' G' P' Q G P

def Wi_success_d (hZF : M.Models ZF) (ω α t B Q G : M.Domain) : Prop :=
  ∃ ξ T₀ Q₀ G₀ E₀ L₀ c N W F j, M.SuccessorOf α ξ ∧ Wi_tree_d t T₀ Q₀ G₀ E₀ L₀ ∧
    Rd_entry_d α c Q ∧ It_branch_d ω T₀ B ∧ Wi_limit_d hZF ω B Q₀ G₀ c N W F ∧
    It_map_d G ξ α j ∧ ∀ o, (∀ x, ¬ M.mem x o) → Rd_entry_d o j F

def Wi_continuous_d (hZF : M.Models ZF) (ω a A S α H Q' G' : M.Domain) : Prop :=
  ∃ T Q G P c N W F, Wi_state_d hZF ω α T Q G a A S P ∧ Wi_past_d H Q G P ∧
    Rd_entry_d α c Q' ∧ Wi_limit_d hZF ω α Q G c N W F ∧
    ∀ i j, M.mem i α → (It_map_d G' i α j ↔ Rd_entry_d i j F)

def Wi_answer_d (hZF : M.Models ZF) (ω a A S o s₀ α H t B s : M.Domain) : Prop :=
  ∃ β T Q G P, M.SuccessorOf β α ∧ Rd_quad_d s T Q G P ∧ Wi_state_d hZF ω β T Q G a A S P ∧
    Wi_past_d H Q G P ∧ ((α = o ∧ B = o ∧ s = s₀) ∨ Wi_success_d hZF ω α t B Q G ∨
      (M.IsLimitOrdinal α ∧ B = o ∧ Wi_continuous_d hZF ω a A S α H Q G))

variable (hZF : M.Models ZF)

theorem Wi_history_d.last_keep_l {ω a A S α D H ξ T Q G P : M.Domain}
    (hist : Wi_history_d hZF ω a A S α D H) (hα : M.SuccessorOf α ξ) (last : Wi_at_d H ξ T Q G P) :
    Wi_past_d H Q G P := by
  intro i U Q' G' P' hi
  obtain ⟨s, hs, ps⟩ := hi
  rcases (hα i).mp (hist.function.bound_l hs).1 with hi | eq
  · exact hist.past i ξ U Q' G' P' T Q G P hi ⟨s, hs, ps⟩ last
  · have eq := hZF.1.eq_of_same_members i ξ eq
    subst i
    obtain ⟨t, ht, pt⟩ := last
    have eq := (fn0_function_l (ZF.modelsKP hZF) hist.function).1.2 ξ s t hs ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (eq ▸ ps).unique_l pt
    exact Wi_keep_d.refl_l Q' G' P'

theorem wi_answer_root_l {ω a A S o s₀ α D H t T Q G P : M.Domain}
    (ho : ∀ x, ¬ M.mem x o) (hα : M.SuccessorOf α o) (pack : Rd_quad_d s₀ T Q G P)
    (state : Wi_state_d hZF ω α T Q G a A S P) (hist : Wi_history_d hZF ω a A S o D H) :
    Wi_answer_d hZF ω a A S o s₀ o H t o s₀ :=
  ⟨α, T, Q, G, P, hα, pack, state, fun i _ _ _ _ ⟨_, hs, _⟩ => (ho i (hist.function.bound_l hs).1).elim,
    Or.inl ⟨rfl, rfl, rfl⟩⟩

variable (hZFC : M.Models ZFC)
local notation "hZF'" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF')

theorem wi_answer_successor_l {ω a A S o s₀ α D H ξ T Q G P θ c t T₀ Q₀ G₀ E₀ L₀ : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (hα : M.SuccessorOf α ξ)
    (last : Wi_at_d H ξ T Q G P) (hc : Rd_entry_d ξ c Q) (pack : Wi_tree_d t T₀ Q₀ G₀ E₀ L₀)
    (nice : It_nice_d hZF' ω c ω T₀ Q₀ G₀ E₀ L₀) (rank : V_d I θ A) (ma : Smem_d I a A S) :
    ∃ B s, Wi_answer_d hZF' ω a A S o s₀ α H t B s := by
  obtain ⟨α', hα', state⟩ := hist.at_l hZF' last
  have eq := Structure.SuccessorOf.eq hZF'.1 hα' hα
  subst α'
  obtain ⟨β, U, Q', G', P', B, d, N, W, F, σ, j, next, extension, hd, _, branch, limit, edge, root⟩ :=
    state.successor_l hZFC rank ma hα hc nice
  obtain ⟨s, ps⟩ := rd_quad_exists_l (ZF.modelsKP hZF') U Q' G' P'
  have keep := extension.keep_l hZF' state
  exact ⟨B, s, β, U, Q', G', P', extension.1, ps, next,
    fun i V Q₁ G₁ P₁ hi => (hist.last_keep_l hZF' hα last i V Q₁ G₁ P₁ hi).trans_l keep,
    Or.inr (Or.inl ⟨ξ, T₀, Q₀, G₀, E₀, L₀, d, N, W, F, j, hα, pack, hd, branch, limit, edge, root⟩)⟩

theorem wi_answer_limit_l {ω a A S o s₀ α D H t : M.Domain}
    (hist : Wi_history_d hZF' ω a A S α D H) (limit : M.IsLimitOrdinal α)
    (count : M.CardinalLessOrEqual I α ω) (ma : Smem_d I a A S) :
    ∃ s, Wi_answer_d hZF' ω a A S o s₀ α H t o s := by
  obtain ⟨T, Q, G, P, state, past⟩ := hist.union_l hZF' limit
  obtain ⟨β, U, Q', G', P', c, N, W, F, σ, next, extension, hc, _, lim, _, edges, _⟩ :=
    state.limit_l hZFC ma limit count
  obtain ⟨s, ps⟩ := rd_quad_exists_l (ZF.modelsKP hZF') U Q' G' P'
  exact ⟨s, β, U, Q', G', P', extension.1, ps, next,
    fun i V Q₁ G₁ P₁ hi => (past i V Q₁ G₁ P₁ hi).trans_l (extension.keep_l hZF' state),
    Or.inr (Or.inr ⟨limit, rfl, T, Q, G, P, c, N, W, F, state, past, hc, lim, edges⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal
