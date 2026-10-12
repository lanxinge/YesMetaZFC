import YesMetaZFC.Model.SetTheory.Internal.TypeTruthSyntax
import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeQuery
import YesMetaZFC.Model.SetTheory.Internal.TypeGameRoot
import YesMetaZFC.Model.SetTheory.Internal.TypeGameMax
import YesMetaZFC.Model.SetTheory.Internal.TypeGameBound
import YesMetaZFC.Model.SetTheory.Internal.TypeGameHeight

/-! # 节点与端点查询证书的一阶表示

每条证书量化全部实际完整类型；节点保留三张函数图及两个包含方向。
这些公式用于开局前固定查询表，不给裸类型加入额外封闭规则。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def tg_node_query_m {d} (ω e n l U D s t k q : Term d) : Formula 1 d := set[d] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ c X R r δ T S, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) → ⌜Formula.isTransitive⌝ₚ(X) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, S, r) →
    (⌜q⌝ₛ ∈ T ↔ ∃ g ∈ X, ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, r, g) ∧
      ⌜tg_node_m⌝ₚ(⌜k⌝ₛ, S, ⌜s⌝ₛ, ⌜t⌝ₛ, g)))⟫
derive_free_closed tg_node_query_m

theorem tg_node_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e n l U D s t k q : Term d) :
    Formula.satisfies ρ (tg_node_query_m ω e n l U D s t k q) ↔ Tg_node_query_d I
      (ω.eval ρ) (e.eval ρ) (n.eval ρ) (l.eval ρ) (U.eval ρ) (D.eval ρ) (s.eval ρ) (t.eval ρ) (k.eval ρ) (q.eval ρ) := by
  simp only [tg_node_query_m, Tg_node_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, smem_sat_l I, Formula.satisfies_isTransitive_iff,
    tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, sg_set_sat_l I hKP.1, tg_node_sat_l I hKP.1,
    Definitional.Term.eval_weaken]
  rfl

def tg_root_query_m {d} (ω e n U D q : Term d) : Formula 1 d := set[d] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ c X R r δ T S, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) → ⌜Formula.isTransitive⌝ₚ(X) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, S, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜e⌝ₛ ∈ S))⟫
derive_free_closed tg_root_query_m

theorem tg_root_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e n U D q : Term d) :
    Formula.satisfies ρ (tg_root_query_m ω e n U D q) ↔
      Tg_root_query_d I (ω.eval ρ) (e.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_root_query_m, Tg_root_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    smem_sat_l I, Formula.satisfies_isTransitive_iff, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1,
    Definitional.Term.eval_weaken]
  rfl

def tg_max_query_m {d} (ω l n U D q : Term d) : Formula 1 d := set[d] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ ν X c R r δ T α, ⌜v_m kpair_convention_l⌝ₚ(ν, X) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, α, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜Formula.isSuccessor⌝ₚ(ν, α)))⟫
derive_free_closed tg_max_query_m

theorem tg_max_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω l n U D q : Term d) :
    Formula.satisfies ρ (tg_max_query_m ω l n U D q) ↔
      Tg_max_query_d I (ω.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_max_query_m, Tg_max_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hKP.1,
    smem_sat_l I, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, Formula.satisfies_isSuccessor_iff,
    Definitional.Term.eval_weaken]
  rfl

def tg_bound_raw_m {d} (δ S α : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜α⌝ₛ) ∧ ⌜δ⌝ₛ ∈ ⌜α⌝ₛ ∧ (∃ B, ⌜v_m kpair_convention_l⌝ₚ(⌜α⌝ₛ, B) ∧ ⌜S⌝ₛ ∈ B)⟫
derive_free_closed tg_bound_raw_m

def tg_height_raw_m {d} (α η : Term d) : Formula 1 d := set[d] ⟪∃ β γ,
  ⌜Formula.isSuccessor⌝ₚ(β, ⌜α⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(γ, β) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜η⌝ₛ, γ)⟫
derive_free_closed tg_height_raw_m

theorem tg_bound_raw_sat_l (hE : Extensional M) {d} (ρ : Env M d) (δ S α : Term d) :
    Formula.satisfies ρ (tg_bound_raw_m δ S α) ↔ Tg_bound_d I (δ.eval ρ) (S.eval ρ) (α.eval ρ) := by
  simp only [tg_bound_raw_m, Tg_bound_d, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, v_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem tg_height_raw_sat_l {d} (ρ : Env M d) (α η : Term d) :
    Formula.satisfies ρ (tg_height_raw_m α η) ↔ Tg_height_d (α.eval ρ) (η.eval ρ) := by
  simp only [tg_height_raw_m, Tg_height_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]
  rfl

def tg_bound_query_m {d} (ω e l n U D q : Term d) : Formula 1 d := set[d] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ η X c R r δ T S α, ⌜v_m kpair_convention_l⌝ₚ(η, X) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) →
    ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, S, r) → ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, α, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜tg_bound_raw_m⌝ₚ(δ, S, α)))⟫
derive_free_closed tg_bound_query_m

theorem tg_bound_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω e l n U D q : Term d) :
    Formula.satisfies ρ (tg_bound_query_m ω e l n U D q) ↔ Tg_bound_query_d I
      (ω.eval ρ) (e.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_bound_query_m, Tg_bound_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hKP.1,
    smem_sat_l I, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, tg_bound_raw_sat_l I hKP.1,
    Definitional.Term.eval_weaken]
  rfl

def tg_height_query_m {d} (ω l n U D q : Term d) : Formula 1 d := set[d] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ η X c R r δ T α, ⌜v_m kpair_convention_l⌝ₚ(η, X) → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, X, R, ⌜n⌝ₛ, r, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, T) → ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, α, r) →
    (⌜q⌝ₛ ∈ T ↔ ⌜tg_height_raw_m⌝ₚ(α, η)))⟫
derive_free_closed tg_height_query_m

theorem tg_height_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω l n U D q : Term d) :
    Formula.satisfies ρ (tg_height_query_m ω l n U D q) ↔ Tg_height_query_d I
      (ω.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (q.eval ρ) := by
  simp only [tg_height_query_m, Tg_height_query_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, v_sat_l I hKP.1,
    smem_sat_l I, tt_realized_sat_l I hKP, rd_entry0_sat_l hKP.1, tg_height_raw_sat_l,
    Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
