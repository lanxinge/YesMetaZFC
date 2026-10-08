import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagram
import YesMetaZFC.SetTheory.Notation

/-! # 迭代树序和完整初等图列的原公式 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def it_pred_m {d} (T k j : Term d) : Formula 1 d := set[d] ⟪
  ⌜k⌝ₛ ∈ ⌜j⌝ₛ ∧ (∀ i, ⌜rd_entry0_m⌝ₚ(i, ⌜j⌝ₛ, ⌜T⌝ₛ) ↔ i = ⌜j⌝ₛ ∨ ⌜rd_entry0_m⌝ₚ(i, ⌜k⌝ₛ, ⌜T⌝ₛ))⟫
derive_free_closed it_pred_m
theorem it_pred_sat_l (hE : Extensional M) {d} (η : Env M d) (T k j : Term d) :
    Formula.satisfies η (it_pred_m T k j) ↔ It_pred_d (T.eval η) (k.eval η) (j.eval η) := by
  simp only [it_pred_m, It_pred_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def it_order_m {d} (α T : Term d) : Formula 1 d := set[d] ⟪
  Ord(⌜α⌝ₛ) ∧ ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜T⌝ₛ) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) → i ∈ ⌜α⌝ₛ ∧ j ∈ ⌜α⌝ₛ) ∧
  (∀ i ∈ ⌜α⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, ⌜T⌝ₛ)) ∧
  (∀ i j k, ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, k, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, k, ⌜T⌝ₛ)) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) → i = j ∨ i ∈ j) ∧
  (∀ i j k, ⌜rd_entry0_m⌝ₚ(i, k, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, k, ⌜T⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) ∨ ⌜rd_entry0_m⌝ₚ(j, i, ⌜T⌝ₛ)) ∧
  (∀ i j, j ∈ ⌜α⌝ₛ → ⌜KP.succ0_m⌝ₚ(j, i) → ∃ k, ⌜it_pred_m⌝ₚ(⌜T⌝ₛ, k, j)) ∧
  (∀ δ, δ ∈ ⌜α⌝ₛ → ⌜Formula.isLimitOrdinal⌝ₚ(δ) → ∀ i ∈ δ,
    ∃ j ∈ δ, ⌜rd_entry0_m⌝ₚ(j, δ, ⌜T⌝ₛ) ∧ (i = j ∨ i ∈ j))⟫
derive_free_closed it_order_m
theorem it_order_sat_l (hKP : M.Models KP) {d} (η : Env M d) (α T : Term d) :
    Formula.satisfies η (it_order_m α T) ↔ It_order_d (α.eval η) (T.eval η) := by
  simp only [it_order_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_isOrdinal_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_isRelation_iff (kp_pair_l hKP),
    rd_entry0_sat_l hKP.1, KP.succ0_sat_l hKP.1, it_pred_sat_l hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
    fun h => ⟨h.ordinal, h.relation, h.bound, h.refl, h.trans, h.forward, h.chain, h.predecessor, h.cofinal⟩⟩

def it_diagram_m {d} (ω α T Q G : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_order_m⌝ₚ(⌜α⌝ₛ, ⌜T⌝ₛ) ∧ ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜Q⌝ₛ) ∧
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜α⌝ₛ, ⌜Q⌝ₛ) ∧
  (∀ i c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ∃ X R, ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R)) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜G⌝ₛ) ∧ ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜T⌝ₛ, ⌜G⌝ₛ) ∧
  (∀ i j f c X R d Y S, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, d, ⌜Q⌝ₛ) →
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) → ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(d, Y, S) →
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c, d, X, Y, f)) ∧
  (∀ i f, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, i, f) → ∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, f) → x = y) ∧
  (∀ i j k f g h, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜it_map_m⌝ₚ(⌜G⌝ₛ, j, k, g) → ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, k, h) →
    ∀ x y z, ⌜rd_entry0_m⌝ₚ(x, y, f) → ⌜rd_entry0_m⌝ₚ(y, z, g) → ⌜rd_entry0_m⌝ₚ(x, z, h))⟫
derive_free_closed it_diagram_m
theorem it_diagram_sat_l (hZF : M.Models ZF) {d} (η : Env M d) (ω α T Q G : Term d) :
    Formula.satisfies η (it_diagram_m ω α T Q G) ↔
      It_diagram_d hZF (ω.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [it_diagram_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_isDomain_iff I,
    rd_entry0_sat_l hZF.1, it_map_sat_l hZF.1, smdl_sat_l I, smap_sat_l I hZF.1,
    it_order_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
    fun h => ⟨h.order, h.model_function, h.model_domain, h.models, h.map_function, h.map_domain, h.elementary, h.identity, h.comp⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
