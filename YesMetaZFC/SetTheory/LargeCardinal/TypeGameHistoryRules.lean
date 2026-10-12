import YesMetaZFC.SetTheory.LargeCardinal.TypeGameParameters

/-! # 规则 (4)–(6)：域增长、重置与较早轮的继续

较早轮通过三阶段历史中的原位置读取。继续分支明确要求 tℓ=pred(t)，
并按原方向检查新 u 超过旧 w；重置分支要求原树和固定低不可分辨点的完整类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_reset_d (ω e δ S ν l n U D u : M.Domain) : Prop := ∃ η Y c R s,
  M.SuccessorOf η ν ∧ V_d I η Y ∧ Smem_d I c Y R ∧ Tt_realized_d I ω c Y R n s δ U D u ∧
    Rd_entry_d e S s ∧ Rd_entry_d l ν s

def tg_reset_m {d} (ω e δ S ν l n U D u : Term d) : Formula 1 d := set[d] ⟪∃ η Y c R s,
  ⌜Formula.isSuccessor⌝ₚ(η, ⌜ν⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(η, Y) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, s) ∧ ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜ν⌝ₛ, s)⟫
derive_free_closed tg_reset_m

theorem tg_reset_sat_l {d} (ρ : Env M d) (ω e δ S ν l n U D u : Term d) :
    Formula.satisfies ρ (tg_reset_m ω e δ S ν l n U D u) ↔ Tg_reset_d hZF
      (ω.eval ρ) (e.eval ρ) (δ.eval ρ) (S.eval ρ) (ν.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (u.eval ρ) := by
  simp only [tg_reset_m, Tg_reset_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def Tg_growth_d (e c A n h κ B : M.Domain) : Prop :=
  (n = e ∧ M.mem A B) ∨ ∃ j a ℓ t τ u, M.SuccessorOf n j ∧ Tg_event_d I c j e h a ∧
    Tg_aux_data_d a ℓ t τ u ∧ M.mem τ κ

def tg_growth_m {d} (e c A n h κ B : Term d) : Formula 1 d := set[d] ⟪
  (⌜n⌝ₛ = ⌜e⌝ₛ ∧ ⌜A⌝ₛ ∈ ⌜B⌝ₛ) ∨ (∃ j a ℓ t τ u,
    ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ, j) ∧ ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, j, ⌜e⌝ₛ, ⌜h⌝ₛ, a) ∧
    ⌜tg_aux_data_m⌝ₚ(a, ℓ, t, τ, u) ∧ τ ∈ ⌜κ⌝ₛ)⟫
derive_free_closed tg_growth_m

theorem tg_growth_sat_l {d} (ρ : Env M d) (e c A n h κ B : Term d) :
    Formula.satisfies ρ (tg_growth_m e c A n h κ B) ↔
      Tg_growth_d hZF (e.eval ρ) (c.eval ρ) (A.eval ρ) (n.eval ρ) (h.eval ρ) (κ.eval ρ) (B.eval ρ) := by
  simp only [tg_growth_m, Tg_growth_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def Tg_continue_d (ω e a c δ n h ℓ t κ k N U D u : M.Domain) : Prop :=
  M.mem ℓ n ∧ ∃ v w ℓ₀ t₀ κ₀ u₀ τ T j l m B V W,
    Tg_event_d I c ℓ e h v ∧ Tg_aux_data_d v ℓ₀ t₀ κ₀ u₀ ∧ Tg_event_d I c ℓ a h w ∧ KPair_d M w τ T ∧
    Fn0_d j ω t₀ ∧ M.SuccessorOf k j ∧ M.IsRestrictionOf I t₀ t j ∧ M.SuccessorOf l j ∧ M.SuccessorOf m l ∧
    M.IsLimitOrdinal τ ∧ V_d I τ B ∧ (∀ x, M.mem x V ↔ M.mem x B ∨ x = τ) ∧ Tt_pool_d I ω m V W ∧
    Tx_exceeds_d hZF ω δ τ m V W T κ N U D u

def tg_continue_m {d} (ω e a c δ n h ℓ t κ k N U D u : Term d) : Formula 1 d := set[d] ⟪⌜ℓ⌝ₛ ∈ ⌜n⌝ₛ ∧
  (∃ v w ℓ₀ t₀ κ₀ u₀ τ T j l m B V W,
    ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, ⌜ℓ⌝ₛ, ⌜e⌝ₛ, ⌜h⌝ₛ, v) ∧ ⌜tg_aux_data_m⌝ₚ(v, ℓ₀, t₀, κ₀, u₀) ∧
    ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, ⌜ℓ⌝ₛ, ⌜a⌝ₛ, ⌜h⌝ₛ, w) ∧ ⌜kpair0_m⌝ₚ(w, τ, T) ∧
    ⌜fn0_m⌝ₚ(j, ⌜ω⌝ₛ, t₀) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜k⌝ₛ, j) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(t₀, ⌜t⌝ₛ, j) ∧
    ⌜Formula.isSuccessor⌝ₚ(l, j) ∧ ⌜Formula.isSuccessor⌝ₚ(m, l) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(τ) ∧
    ⌜v_sigma_m⌝ₚ(τ, B) ∧ ⌜tt_constants0_m⌝ₚ(τ, B, V) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, m, V, W) ∧
    ⌜tx_exceeds_m⌝ₚ(⌜ω⌝ₛ, ⌜δ⌝ₛ, τ, m, V, W, T, ⌜κ⌝ₛ, ⌜N⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ))⟫
derive_free_closed tg_continue_m

theorem tg_continue_sat_l {d} (ρ : Env M d) (ω e a c δ n h ℓ t κ k N U D u : Term d) :
    Formula.satisfies ρ (tg_continue_m ω e a c δ n h ℓ t κ k N U D u) ↔ Tg_continue_d hZF
      (ω.eval ρ) (e.eval ρ) (a.eval ρ) (c.eval ρ) (δ.eval ρ) (n.eval ρ) (h.eval ρ) (ℓ.eval ρ) (t.eval ρ)
      (κ.eval ρ) (k.eval ρ) (N.eval ρ) (U.eval ρ) (D.eval ρ) (u.eval ρ) := by
  simp only [tg_continue_m, Tg_continue_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1, kpair0_sat_l hZF.1,
    fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_isLimitOrdinal_iff, v_sigma_sat_l (ZF.modelsKP hZF), tt_constants0_sat_l hZF.1,
    tt_pool_sat_l I (ZF.modelsKP hZF), tx_exceeds_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
