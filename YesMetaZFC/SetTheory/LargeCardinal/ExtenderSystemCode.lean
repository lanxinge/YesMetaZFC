import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystemSyntax
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Syntax

/-! # 原有限支撑超幂系统的一阶证书

分量公式、标签、过渡代表和直接系统均原样编码，量化的是实际集合图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def ep_graph_m {d} (ω κ L X R F J O Z A p T S : Term d) : Formula 1 d := set[d] ⟪
  ⌜di_order_m⌝ₚ(⌜J⌝ₛ, ⌜O⌝ₛ) ∧
  (∀ a b, ⌜rd_entry0_m⌝ₚ(a, b, ⌜O⌝ₛ) ↔ a ∈ ⌜J⌝ₛ ∧ b ∈ ⌜J⌝ₛ ∧ (∃ q, ⌜ei_map_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, a, b, q))) ∧
  ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜J⌝ₛ, ⌜p⌝ₛ) ∧ (∀ a, a ∈ ⌜J⌝ₛ ↔ ⌜ei_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, a)) ∧
  (∃ Q, ⌜fn0_m⌝ₚ(⌜J⌝ₛ, Q, ⌜Z⌝ₛ) ∧ (∀ a c, ⌜rd_entry0_m⌝ₚ(a, c, ⌜Z⌝ₛ) →
    ⌜ep_component_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜F⌝ₛ, a, c))) ∧
  (∀ u, u ∈ ⌜A⌝ₛ ↔ ∃ a B, ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜ep_at_m⌝ₚ(⌜Z⌝ₛ, a, B)) ∧
  (∀ u a B, ⌜kpair0_m⌝ₚ(u, a, B) → (⌜rd_entry0_m⌝ₚ(u, a, ⌜p⌝ₛ) ↔ u ∈ ⌜A⌝ₛ)) ∧
  (∀ u v, ⌜rd_entry0_m⌝ₚ(u, v, ⌜T⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧ (∃ a b B C,
    ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜kpair0_m⌝ₚ(v, b, C) ∧ ⌜ep_arrow_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, a, b, B, C))) ∧
  (∀ u v, ⌜rd_entry0_m⌝ₚ(u, v, ⌜S⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧ (∃ a B C,
    ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜kpair0_m⌝ₚ(v, a, C) ∧ ⌜ep_rel_m⌝ₚ(⌜Z⌝ₛ, a, B, C)))⟫
derive_free_closed ep_graph_m

theorem ep_graph_sat_l {d} (η : Env M d) (ω κ L X R F J O Z A p T S : Term d) :
    Formula.satisfies η (ep_graph_m ω κ L X R F J O Z A p T S) ↔
      Ep_graph_d hZF (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (R.eval η) (F.eval η)
        (J.eval η) (O.eval η) (Z.eval η) (A.eval η) (p.eval η) (T.eval η) (S.eval η) := by
  simp only [ep_graph_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, di_order_sat_l hZF.1,
    fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1, ei_map_sat_l hZF.1, ei_sat_l hZF.1,
    ep_component_sat_l I hZF.1, ep_at_sat_l hZF.1, ep_arrow_sat_l hZF.1, ep_rel_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
    fun h => ⟨h.order, h.order_spec, h.projection, h.indices, h.models, h.nodes, h.index, h.arrows, h.relations⟩⟩

def ep_lift_m {d} (ω κ L X a b B C : Term d) : Formula 1 d := set[d] ⟪
  ∀ f ∈ ⌜B⌝ₛ, ∃ m n q g, m ∈ ⌜ω⌝ₛ ∧ n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(m, n, q) ∧ ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, ⌜b⌝ₛ) ∧
    ⌜cp0_m⌝ₚ(m, n, ⌜L⌝ₛ, q, ⌜b⌝ₛ, ⌜a⌝ₛ) ∧ g ∈ ⌜C⌝ₛ ∧ ⌜ep_pull_m⌝ₚ(⌜κ⌝ₛ, ⌜X⌝ₛ, m, n, q, f, g)⟫
derive_free_closed ep_lift_m

theorem ep_lift_sat_l (hE : Extensional M) {d} (η : Env M d) (ω κ L X a b B C : Term d) :
    Formula.satisfies η (ep_lift_m ω κ L X a b B C) ↔ Ep_lift_d
      (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (a.eval η) (b.eval η) (B.eval η) (C.eval η) := by
  simp only [ep_lift_m, Ep_lift_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, fn0_sat_l hE, cp0_sat_l hE,
    ep_pull_sat_l hE, Definitional.Term.eval_weaken]; rfl

def ep_system_m {d} (ω κ L X R F J O Z A p T S : Term d) : Formula 1 d := set[d] ⟪
  ⌜ep_graph_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜F⌝ₛ, ⌜J⌝ₛ, ⌜O⌝ₛ, ⌜Z⌝ₛ, ⌜A⌝ₛ, ⌜p⌝ₛ, ⌜T⌝ₛ, ⌜S⌝ₛ) ∧
  ⌜di_system_m⌝ₚ(⌜J⌝ₛ, ⌜O⌝ₛ, ⌜A⌝ₛ, ⌜p⌝ₛ, ⌜T⌝ₛ, ⌜S⌝ₛ) ∧
  (∀ u v a b B C, ⌜kpair0_m⌝ₚ(u, a, B) → ⌜kpair0_m⌝ₚ(v, b, C) → ⌜rd_entry0_m⌝ₚ(u, v, ⌜T⌝ₛ) →
    ⌜ep_lift_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, a, b, B, C))⟫
derive_free_closed ep_system_m

theorem ep_system_sat_l {d} (η : Env M d) (ω κ L X R F J O Z A p T S : Term d) :
    Formula.satisfies η (ep_system_m ω κ L X R F J O Z A p T S) ↔
      Ep_system_d hZF (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (R.eval η) (F.eval η)
        (J.eval η) (O.eval η) (Z.eval η) (A.eval η) (p.eval η) (T.eval η) (S.eval η) := by
  simp only [ep_system_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1, ep_graph_sat_l hZF, di_system_sat_l hZF.1, ep_lift_sat_l hZF.1,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.toEp_graph_d, h.diagram, h.representatives⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
