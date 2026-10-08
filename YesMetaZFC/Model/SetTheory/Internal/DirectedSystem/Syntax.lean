import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Limit
import YesMetaZFC.SetTheory.Notation

/-! # 实际定向系统及其直接极限的一阶编码

公式逐项保留原图的函子律、投影核与极限关系，用于内部递归收集真实超幂。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def di_order_m {d} (J L : Term d) : Formula 1 d := set[d] ⟪
  (∀ i ∈ ⌜J⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, ⌜L⌝ₛ)) ∧
  (∀ i j k, ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, k, ⌜L⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, k, ⌜L⌝ₛ)) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ) → i ∈ ⌜J⌝ₛ ∧ j ∈ ⌜J⌝ₛ) ∧
  (∀ i ∈ ⌜J⌝ₛ, ∀ j ∈ ⌜J⌝ₛ, ∃ k ∈ ⌜J⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, k, ⌜L⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(j, k, ⌜L⌝ₛ))⟫
derive_free_closed di_order_m

theorem di_order_sat_l (hE : Extensional M) {d} (η : Env M d) (J L : Term d) :
    Formula.satisfies η (di_order_m J L) ↔ Di_order_d (J.eval η) (L.eval η) := by
  simp only [di_order_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨r, t, b, d⟩ => ⟨r, t, b, fun i j hi hj => d i hi j hj⟩,
    fun h => ⟨h.refl, h.trans, h.bound, fun i hi j hj => h.directed i j hi hj⟩⟩

def di_system_m {d} (J L A p T R : Term d) : Formula 1 d := set[d] ⟪
  ⌜di_order_m⌝ₚ(⌜J⌝ₛ, ⌜L⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜J⌝ₛ, ⌜p⌝ₛ) ∧
  (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → x ∈ ⌜A⌝ₛ ∧ y ∈ ⌜A⌝ₛ) ∧
  (∀ x y i j, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, j, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ)) ∧
  (∀ x ∈ ⌜A⌝ₛ, ⌜rd_entry0_m⌝ₚ(x, x, ⌜T⌝ₛ)) ∧
  (∀ x y z, ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, z, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x, z, ⌜T⌝ₛ)) ∧
  (∀ x i j, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ) →
    ∃ y, ⌜rd_entry0_m⌝ₚ(y, j, ⌜p⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ)) ∧
  (∀ x y z j, ⌜rd_entry0_m⌝ₚ(y, j, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(z, j, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x, z, ⌜T⌝ₛ) → y = z) ∧
  (∀ x y z i, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, i, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, z, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, z, ⌜T⌝ₛ) → x = y) ∧
  (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜R⌝ₛ) → ∃ i, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(y, i, ⌜p⌝ₛ)) ∧
  (∀ x y i u v j, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, i, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(u, j, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(v, j, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, u, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, v, ⌜T⌝ₛ) →
    (⌜rd_entry0_m⌝ₚ(x, y, ⌜R⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(u, v, ⌜R⌝ₛ)))⟫
derive_free_closed di_system_m

theorem di_system_sat_l (hE : Extensional M) {d} (η : Env M d) (J L A p T R : Term d) :
    Formula.satisfies η (di_system_m J L A p T R) ↔
      Di_system_d (J.eval η) (L.eval η) (A.eval η) (p.eval η) (T.eval η) (R.eval η) := by
  simp only [di_system_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    rd_entry0_sat_l hE, fn0_sat_l hE, di_order_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
    fun h => ⟨h.order, h.index, h.bound, h.forward, h.identity, h.comp, h.total, h.unique, h.injective, h.locality, h.relation⟩⟩

def di_limit_m {d} (A p T R q C S : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜C⌝ₛ, ⌜q⌝ₛ) ∧ (∀ B, B ∈ ⌜C⌝ₛ ↔ ∃ x, ⌜rd_entry0_m⌝ₚ(x, B, ⌜q⌝ₛ)) ∧
  (∀ x y B D, ⌜rd_entry0_m⌝ₚ(x, B, ⌜q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, D, ⌜q⌝ₛ) → (B = D ↔ ⌜di_eq_m⌝ₚ(⌜T⌝ₛ, x, y))) ∧
  (∀ x y B D, ⌜rd_entry0_m⌝ₚ(x, B, ⌜q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, D, ⌜q⌝ₛ) →
    (⌜rd_entry0_m⌝ₚ(B, D, ⌜S⌝ₛ) ↔ ⌜di_rel_m⌝ₚ(⌜p⌝ₛ, ⌜T⌝ₛ, ⌜R⌝ₛ, x, y))) ∧
  (∀ B D, ⌜rd_entry0_m⌝ₚ(B, D, ⌜S⌝ₛ) → B ∈ ⌜C⌝ₛ ∧ D ∈ ⌜C⌝ₛ) ∧
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜S⌝ₛ)⟫
derive_free_closed di_limit_m

theorem di_limit_sat_l (hKP : M.Models KP) {d} (η : Env M d) (A p T R q C S : Term d) :
    Formula.satisfies η (di_limit_m A p T R q C S) ↔
      Di_limit_d (A.eval η) (p.eval η) (T.eval η) (R.eval η) (q.eval η) (C.eval η) (S.eval η) := by
  simp only [di_limit_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_isRelation_iff (kp_pair_l hKP),
    rd_entry0_sat_l hKP.1, fn0_sat_l hKP.1, di_eq_sat_l hKP.1, di_rel_sat_l hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩,
    fun h => ⟨h.projection, h.range, h.kernel, h.relation, h.bounded, h.graph⟩⟩

end YesMetaZFC.SetTheory.Internal
