import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakState
import YesMetaZFC.SetTheory.LargeCardinal.IterationStepSyntax

/-! # 原树枝、带标号系统与规范极限的纯公式

应答选择保留实际商图以及从同一商图读取的全部腿，不以良基性断言代替极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def it_branch_m {d} (α T B : Term d) : Formula 1 d := set[d] ⟪
  ⌜B⌝ₛ ⊆ ⌜α⌝ₛ ∧ (∀ i j, i ∈ ⌜B⌝ₛ → j ∈ ⌜B⌝ₛ → ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) ∨ ⌜rd_entry0_m⌝ₚ(j, i, ⌜T⌝ₛ)) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) → j ∈ ⌜B⌝ₛ → i ∈ ⌜B⌝ₛ) ∧
  (∀ i ∈ ⌜α⌝ₛ, ∃ j ∈ ⌜B⌝ₛ, i = j ∨ i ∈ j)⟫
derive_free_closed it_branch_m
theorem it_branch_sat_l (hE : Extensional M) {d} (η : Env M d) (α T B : Term d) :
    Formula.satisfies η (it_branch_m α T B) ↔ It_branch_d (α.eval η) (T.eval η) (B.eval η) := by
  simp only [it_branch_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.subset, h.chain, h.down, h.cofinal⟩⟩

def it_tag_m {d} (B Q A p R : Term d) : Formula 1 d := set[d] ⟪
  (∀ u, u ∈ ⌜A⌝ₛ ↔ ∃ i x, i ∈ ⌜B⌝ₛ ∧ ⌜kpair0_m⌝ₚ(u, i, x) ∧ ⌜ep_at_m⌝ₚ(⌜Q⌝ₛ, i, x)) ∧
  ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜B⌝ₛ, ⌜p⌝ₛ) ∧
  (∀ u i x, ⌜kpair0_m⌝ₚ(u, i, x) → (⌜rd_entry0_m⌝ₚ(u, i, ⌜p⌝ₛ) ↔ u ∈ ⌜A⌝ₛ)) ∧
  (∀ u v, ⌜rd_entry0_m⌝ₚ(u, v, ⌜R⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧
    (∃ i x y, ⌜kpair0_m⌝ₚ(u, i, x) ∧ ⌜kpair0_m⌝ₚ(v, i, y) ∧ ⌜ep_rel_m⌝ₚ(⌜Q⌝ₛ, i, x, y)))⟫
derive_free_closed it_tag_m
theorem it_tag_sat_l (hE : Extensional M) {d} (η : Env M d) (B Q A p R : Term d) :
    Formula.satisfies η (it_tag_m B Q A p R) ↔ It_tag_d (B.eval η) (Q.eval η) (A.eval η) (p.eval η) (R.eval η) := by
  simp only [it_tag_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, kpair0_sat_l hE,
    rd_entry0_sat_l hE, ep_at_sat_l hE, ep_rel_sat_l hE, fn0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.nodes, h.projection, h.index, h.relations⟩⟩

def it_system_m {d} (B L Q G A p H R : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_tag_m⌝ₚ(⌜B⌝ₛ, ⌜Q⌝ₛ, ⌜A⌝ₛ, ⌜p⌝ₛ, ⌜R⌝ₛ) ∧ ⌜di_system_m⌝ₚ(⌜B⌝ₛ, ⌜L⌝ₛ, ⌜A⌝ₛ, ⌜p⌝ₛ, ⌜H⌝ₛ, ⌜R⌝ₛ) ∧
  (∀ u v i j x y, ⌜kpair0_m⌝ₚ(u, i, x) → ⌜kpair0_m⌝ₚ(v, j, y) →
    (⌜rd_entry0_m⌝ₚ(u, v, ⌜H⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧ ⌜it_arrow_m⌝ₚ(⌜G⌝ₛ, i, j, x, y)))⟫
derive_free_closed it_system_m
theorem it_system_sat_l (hE : Extensional M) {d} (η : Env M d) (B L Q G A p H R : Term d) :
    Formula.satisfies η (it_system_m B L Q G A p H R) ↔
      It_system_d (B.eval η) (L.eval η) (Q.eval η) (G.eval η) (A.eval η) (p.eval η) (H.eval η) (R.eval η) := by
  simp only [it_system_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, kpair0_sat_l hE, rd_entry0_sat_l hE,
    it_tag_sat_l hE, di_system_sat_l hE, it_arrow_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.tags, h.system, h.arrows⟩⟩

def it_embedding_m {d} (ω B Q G a N W P : Term d) : Formula 1 d := set[d] ⟪
  ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, ⌜N⌝ₛ, ⌜W⌝ₛ) ∧ ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜P⌝ₛ) ∧
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜B⌝ₛ, ⌜P⌝ₛ) ∧
  (∀ i f c X R, ⌜rd_entry0_m⌝ₚ(i, f, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) →
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) → ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c, ⌜a⌝ₛ, X, ⌜N⌝ₛ, f)) ∧
  (∀ i j f u v, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜rd_entry0_m⌝ₚ(i, u, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, v, ⌜P⌝ₛ) →
    ∀ x y z, ⌜rd_entry0_m⌝ₚ(x, y, f) → ⌜rd_entry0_m⌝ₚ(y, z, v) → ⌜rd_entry0_m⌝ₚ(x, z, u))⟫
derive_free_closed it_embedding_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_embedding_sat_l {d} (η : Env M d) (ω B Q G a N W P : Term d) :
    Formula.satisfies η (it_embedding_m ω B Q G a N W P) ↔
      It_embedding_d hZF (ω.eval η) (B.eval η) (Q.eval η) (G.eval η) (a.eval η) (N.eval η) (W.eval η) (P.eval η) := by
  simp only [it_embedding_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_isDomain_iff I, smdl_sat_l I,
    smap_sat_l I hZF.1, it_map_sat_l hZF.1, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun h => ⟨h.model, h.function, h.domain, h.elementary, h.commute⟩⟩

def it_cone_m {d} (ω B Q G a N W P : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_embedding_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜a⌝ₛ, ⌜N⌝ₛ, ⌜W⌝ₛ, ⌜P⌝ₛ) ∧
  (∀ y ∈ ⌜N⌝ₛ, ∃ i f x, ⌜rd_entry0_m⌝ₚ(i, f, ⌜P⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, y, f))⟫
derive_free_closed it_cone_m
theorem it_cone_sat_l {d} (η : Env M d) (ω B Q G a N W P : Term d) :
    Formula.satisfies η (it_cone_m ω B Q G a N W P) ↔
      It_cone_d hZF (ω.eval η) (B.eval η) (Q.eval η) (G.eval η) (a.eval η) (N.eval η) (W.eval η) (P.eval η) := by
  simp only [it_cone_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    it_embedding_sat_l hZF, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun h => ⟨h.toIt_embedding_d, h.cover⟩⟩

def wi_limit_m {d} (ω B Q G c N W P : Term d) : Formula 1 d := set[d] ⟪
  ∃ L A p H R r, ⌜it_system_m⌝ₚ(⌜B⌝ₛ, L, ⌜Q⌝ₛ, ⌜G⌝ₛ, A, p, H, R) ∧
    ⌜di_limit_m⌝ₚ(A, p, H, R, r, ⌜N⌝ₛ, ⌜W⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜N⌝ₛ, ⌜W⌝ₛ) ∧
    ⌜it_cone_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜c⌝ₛ, ⌜N⌝ₛ, ⌜W⌝ₛ, ⌜P⌝ₛ) ∧
    (∀ i f, ⌜rd_entry0_m⌝ₚ(i, f, ⌜P⌝ₛ) ↔ i ∈ ⌜B⌝ₛ ∧ ⌜it_project_m⌝ₚ(r, i, f))⟫
derive_free_closed wi_limit_m
theorem wi_limit_sat_l {d} (η : Env M d) (ω B Q G c N W P : Term d) :
    Formula.satisfies η (wi_limit_m ω B Q G c N W P) ↔
      Wi_limit_d hZF (ω.eval η) (B.eval η) (Q.eval η) (G.eval η) (c.eval η) (N.eval η) (W.eval η) (P.eval η) := by
  simp only [wi_limit_m, Wi_limit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    it_system_sat_l hZF.1, di_limit_sat_l hZF.1, smem_sat_l I, it_cone_sat_l hZF,
    rd_entry0_sat_l hZF.1, it_project_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
