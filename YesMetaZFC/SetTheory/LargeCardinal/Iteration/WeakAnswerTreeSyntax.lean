import YesMetaZFC.SetTheory.LargeCardinal.Iteration.KeepTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswer
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakBranch

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
      It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval η) (B.eval η) (Q.eval η) (G.eval η) (a.eval η) (N.eval η) (W.eval η) (P.eval η) := by
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
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval η) (B.eval η) (Q.eval η) (G.eval η) (a.eval η) (N.eval η) (W.eval η) (P.eval η) := by
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

/-! ## 强返回极限证书的公式层

该层只编码 `Wi_limit_tree_d` 的直接字段。树枝的 `It_wf_branch_d`
仍由外部强接口消费，避免在公式层伪造其初等性见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

 def wi_limit_tree_m {d} (ω B T Q G c N W P : Term d) : Formula 1 d := set[d] ⟪
  ∃ L A p H R r, ⌜it_system_m⌝ₚ(⌜B⌝ₛ, L, ⌜Q⌝ₛ, ⌜G⌝ₛ, A, p, H, R) ∧
    (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, L) ↔ i ∈ ⌜B⌝ₛ ∧ j ∈ ⌜B⌝ₛ ∧
      ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ)) ∧
    ⌜di_limit_m⌝ₚ(A, p, H, R, r, ⌜N⌝ₛ, ⌜W⌝ₛ) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜N⌝ₛ, ⌜W⌝ₛ) ∧
    ⌜it_cone_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜c⌝ₛ, ⌜N⌝ₛ, ⌜W⌝ₛ, ⌜P⌝ₛ) ∧
    (∀ i f, ⌜rd_entry0_m⌝ₚ(i, f, ⌜P⌝ₛ) ↔ i ∈ ⌜B⌝ₛ ∧
      ⌜it_project_m⌝ₚ(r, i, f)) ∧
    ⌜wf_rel_m⌝ₚ(⌜N⌝ₛ, ⌜W⌝ₛ)⟫
derive_free_closed wi_limit_tree_m

theorem wi_limit_tree_sat_l {d} (η : Env M d) (ω B T Q G c N W P : Term d) :
    Formula.satisfies η (wi_limit_tree_m ω B T Q G c N W P) ↔
      Wi_limit_tree_d hZF (ω.eval η) (B.eval η) (T.eval η) (Q.eval η) (G.eval η)
        (c.eval η) (N.eval η) (W.eval η) (P.eval η) := by
  simp only [wi_limit_tree_m, Wi_limit_tree_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    it_system_sat_l hZF.1, di_limit_sat_l hZF.1, smem_sat_l I,
    it_cone_sat_l hZF, rd_entry0_sat_l hZF.1,
    it_project_sat_l (ZF.modelsKP hZF), wf_rel_sat_l hZF.1,
    Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 定向系统初等性的公式层

将 `Di_elementary_d` 的全分量量化直接编码为一阶公式，供强树枝证书复用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
variable (I : kpair_convention_l.Interpretation M)

 def di_elementary_m {d} (ω L A p T R : Term d) : Formula 1 d := set[d] ⟪
  ∀ i j c X S d Y V,
    ⌜di_stage_m⌝ₚ(⌜A⌝ₛ,⌜p⌝ₛ,⌜R⌝ₛ,i,c,X,S) →
    ⌜di_stage_m⌝ₚ(⌜A⌝ₛ,⌜p⌝ₛ,⌜R⌝ₛ,j,d,Y,V) →
    ⌜rd_entry0_m⌝ₚ(i,j,⌜L⌝ₛ) →
    ∃ e, ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,c,d,X,Y,e) ∧
      (∀ x y, ⌜rd_entry0_m⌝ₚ(x,y,e) ↔ x ∈ X ∧ y ∈ Y ∧
        ⌜rd_entry0_m⌝ₚ(x,y,⌜T⌝ₛ))⟫
derive_free_closed di_elementary_m

theorem di_elementary_sat_l {d} (hE : Extensional M) (η : Env M d)
    (ω L A p T R : Term d) :
    Formula.satisfies η (di_elementary_m ω L A p T R) ↔
      Di_elementary_d I (ω.eval η) (L.eval η) (A.eval η) (p.eval η)
        (T.eval η) (R.eval η) := by
  simp only [di_elementary_m, Di_elementary_d, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_iff_iff,
    di_stage_sat_l I hE, smap_sat_l I hE, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 线性状态、历史与全前驱保持的一阶编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def wi_state_m {d} (ω α T Q G a A S P : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_diagram_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ) ∧
  (∀ i j, j ∈ ⌜α⌝ₛ → i ∈ j → ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ)) ∧
  (∀ i c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ∃ X R K,
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) ∧ ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, K, X, R)) ∧
  (∀ i c X R, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ⌜kpair0_m⌝ₚ(c, X, R) →
    ⌜Formula.cardinalLessOrEqual kpair_convention_l⌝ₚ(X, ⌜ω⌝ₛ)) ∧
  ⌜it_embedding_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed wi_state_m
theorem wi_state_sat_l {d} (η : Env M d) (ω α T Q G a A S P : Term d) :
    Formula.satisfies η (wi_state_m ω α T Q G a A S P) ↔
      Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (a.eval η) (A.eval η) (S.eval η) (P.eval η) := by
  simp only [wi_state_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, it_diagram_sat_l hZF, rd_entry0_sat_l hZF.1, Formula.satisfies_exists_iff, smem_sat_l I, ep_source_sat_l (ZF.modelsKP hZF),
    kpair0_sat_l hZF.1, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1,
    it_embedding_sat_l hZF, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨⟨a, b, c, d⟩, e⟩, fun h => ⟨h.diagram, h.linear, h.sources, h.count, h.returns⟩⟩

def wi_keep_m {d} (Q G P Q' G' P' : Term d) : Formula 1 d := set[d] ⟪
  (∀ i c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q'⌝ₛ)) ∧
  (∀ i j f, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, j, f)) ∧
  (∀ i f, ⌜rd_entry0_m⌝ₚ(i, f, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, f, ⌜P'⌝ₛ))⟫
derive_free_closed wi_keep_m
theorem wi_keep_sat_l (hE : Extensional M) {d} (η : Env M d) (Q G P Q' G' P' : Term d) :
    Formula.satisfies η (wi_keep_m Q G P Q' G' P') ↔
      Wi_keep_d (Q.eval η) (G.eval η) (P.eval η) (Q'.eval η) (G'.eval η) (P'.eval η) := by
  simp only [wi_keep_m, Wi_keep_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hE, it_map_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_at_m {d} (H i T Q G P : Term d) : Formula 1 d := set[d] ⟪
  ∃ s, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, s, ⌜H⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(s, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed wi_at_m
theorem wi_at_sat_l (hE : Extensional M) {d} (η : Env M d) (H i T Q G P : Term d) :
    Formula.satisfies η (wi_at_m H i T Q G P) ↔ Wi_at_d (H.eval η) (i.eval η) (T.eval η) (Q.eval η) (G.eval η) (P.eval η) := by
  simp only [wi_at_m, Wi_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_past_m {d} (H Q G P : Term d) : Formula 1 d := set[d] ⟪
  ∀ i U Q' G' P', ⌜wi_at_m⌝ₚ(⌜H⌝ₛ, i, U, Q', G', P') → ⌜wi_keep_m⌝ₚ(Q', G', P', ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed wi_past_m
theorem wi_past_sat_l (hE : Extensional M) {d} (η : Env M d) (H Q G P : Term d) :
    Formula.satisfies η (wi_past_m H Q G P) ↔ Wi_past_d (H.eval η) (Q.eval η) (G.eval η) (P.eval η) := by
  simp only [wi_past_m, Wi_past_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    wi_at_sat_l hE, wi_keep_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_history_m {d} (ω a A S α D H : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜α⌝ₛ, ⌜D⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ i s, ⌜rd_entry0_m⌝ₚ(i, s, ⌜H⌝ₛ) → ∃ β T Q G P, ⌜KP.succ0_m⌝ₚ(β, i) ∧
    ⌜rd_quad_m⌝ₚ(s, T, Q, G, P) ∧ ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, β, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P)) ∧
  (∀ i j T Q G P U Q' G' P', i ∈ j → ⌜wi_at_m⌝ₚ(⌜H⌝ₛ, i, T, Q, G, P) →
    ⌜wi_at_m⌝ₚ(⌜H⌝ₛ, j, U, Q', G', P') → ⌜wi_keep_m⌝ₚ(Q, G, P, Q', G', P'))⟫
derive_free_closed wi_history_m
theorem wi_history_sat_l {d} (η : Env M d) (ω a A S α D H : Term d) :
    Formula.satisfies η (wi_history_m ω a A S α D H) ↔
      Wi_history_d hZF (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (α.eval η) (D.eval η) (H.eval η) := by
  simp only [wi_history_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    KP.succ0_sat_l hZF.1, rd_quad_sat_l hZF.1, wi_state_sat_l hZF,
    wi_at_sat_l hZF.1, wi_keep_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.function, h.rows, h.past⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相邻保持给出整列历史相容性

对实际一阶公式作内部自然数归纳。证明覆盖内部全部自然数，
不把外部标准有限链或外部任意谓词归纳代替内部 ω 运行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem wi_chain_past_l {ω D H : M.Domain} (hw : M.IsOmega ω) (fn : Fn0_d ω D H)
    (rows : ∀ i s, Rd_entry_d i s H → ∃ T Q G P, Rd_quad_d s T Q G P)
    (step : ∀ i j T Q G P U Q' G' P', M.SuccessorOf j i →
      Wi_at_d H i T Q G P → Wi_at_d H j U Q' G' P' → Wi_keep_d Q G P Q' G' P') :
    ∀ i j T Q G P U Q' G' P', M.mem i j →
      Wi_at_d H i T Q G P → Wi_at_d H j U Q' G' P' → Wi_keep_d Q G P Q' G' P' := by
  let φ : UnarySchema 1 := { body := set[2] ⟪∀ i T Q G P U Q' G' P', i ∈ ⌜(.bound 0 : Term 2)⌝ₛ →
    ⌜wi_at_m⌝ₚ(⌜(.bound 1 : Term 2)⌝ₛ,i,T,Q,G,P) →
    ⌜wi_at_m⌝ₚ(⌜(.bound 1 : Term 2)⌝ₛ,⌜(.bound 0 : Term 2)⌝ₛ,U,Q',G',P') →
    ⌜wi_keep_m⌝ₚ(Q,G,P,Q',G',P')⟫ }
  let ρ : Env M 1 := ⟨fun _ => H,fun _ => H⟩
  have read j : φ.denote ρ j ↔ ∀ i T Q G P U Q' G' P', M.mem i j →
      Wi_at_d H i T Q G P → Wi_at_d H j U Q' G' P' → Wi_keep_d Q G P Q' G' P' := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,wi_at_sat_l hZF.1,wi_keep_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all := hw.induction (fun j => φ.denote ρ j) (ZF.separation_exists_d hZF φ ρ ω)
    (fun z empty => (read z).mpr (fun i _ _ _ _ _ _ _ _ hi => (empty i hi).elim)) (by
      intro k hk ih j succ
      apply (read j).mpr
      intro i T Q G P U Q' G' P' hij first last
      obtain ⟨s,_,ks⟩ := (fn0_function_l (ZF.modelsKP hZF) fn).2.2 k hk
      obtain ⟨V,Q₀,G₀,P₀,quad⟩ := rows k s ks
      have mid : Wi_at_d H k V Q₀ G₀ P₀ := ⟨s,ks,quad⟩
      have tail := step k j V Q₀ G₀ P₀ U Q' G' P' succ mid last
      rcases (succ i).mp hij with lt | eq
      · exact ((read k).mp ih i T Q G P V Q₀ G₀ P₀ lt first mid).trans_l tail
      · have eq := hZF.1.eq_of_same_members i k eq
        subst i
        obtain ⟨s',ks',quad'⟩ := first
        have eq := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 k s' s ks' ks
        subst s'
        obtain ⟨rfl,rfl,rfl,rfl⟩ := quad'.unique_l quad
        exact tail)
  intro i j T Q G P U Q' G' P' hij first last
  obtain ⟨s,js,quad⟩ := last
  exact (read j).mp (all j (fn.bound_l js).1) i T Q G P U Q' G' P' hij first ⟨s,js,quad⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际良基树枝证书的公式层
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def it_wf_branch_m {d} (ω α T Q G B : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_branch_m⌝ₚ(⌜α⌝ₛ,⌜T⌝ₛ,⌜B⌝ₛ) ∧
  (∃ L A p H R q c C V,
    (∀ i j, ⌜rd_entry0_m⌝ₚ(i,j,L) ↔ i ∈ ⌜B⌝ₛ ∧ j ∈ ⌜B⌝ₛ ∧
      ⌜rd_entry0_m⌝ₚ(i,j,⌜T⌝ₛ)) ∧
    ⌜it_system_m⌝ₚ(⌜B⌝ₛ,L,⌜Q⌝ₛ,⌜G⌝ₛ,A,p,H,R) ∧
    ⌜di_elementary_m⌝ₚ(⌜ω⌝ₛ,L,A,p,H,R) ∧
    ⌜di_limit_m⌝ₚ(A,p,H,R,q,C,V) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c,C,V) ∧
    ⌜wf_rel_m⌝ₚ(C,V))⟫
derive_free_closed it_wf_branch_m

theorem it_wf_branch_sat_l {d} (η : Env M d) (ω α T Q G B : Term d) :
    Formula.satisfies η (it_wf_branch_m ω α T Q G B) ↔
      It_wf_branch_d hZF (ω.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (B.eval η) := by
  simp only [it_wf_branch_m, It_wf_branch_d, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    it_branch_sat_l hZF.1, it_system_sat_l hZF.1,
    di_elementary_sat_l I hZF.1, di_limit_sat_l hZF.1,
    smdl_sat_l I, wf_rel_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原弱迭代应答的精确公式

公式只陈述所选枝、实际极限及历史保持；不把应答存在性加入合法性定义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def wi_tree_m {d} (t T Q G E L : Term d) : Formula 1 d := set[d] ⟪
  ∃ p, ⌜kpair0_m⌝ₚ(p, ⌜E⌝ₛ, ⌜L⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(⌜t⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, p)⟫
derive_free_closed wi_tree_m
theorem wi_tree_sat_l (hE : Extensional M) {d} (η : Env M d) (t T Q G E L : Term d) :
    Formula.satisfies η (wi_tree_m t T Q G E L) ↔
      Wi_tree_d (t.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) := by
  simp only [wi_tree_m, Wi_tree_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_success_m {d} (ω α t B Q G : Term d) : Formula 1 d := set[d] ⟪
  ∃ ξ T₀ Q₀ G₀ E₀ L₀ c N W F j, ⌜KP.succ0_m⌝ₚ(⌜α⌝ₛ, ξ) ∧ ⌜wi_tree_m⌝ₚ(⌜t⌝ₛ, T₀, Q₀, G₀, E₀, L₀) ∧
    ⌜rd_entry0_m⌝ₚ(⌜α⌝ₛ, c, ⌜Q⌝ₛ) ∧ ⌜it_branch_m⌝ₚ(⌜ω⌝ₛ, T₀, ⌜B⌝ₛ) ∧
    ⌜wi_limit_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, Q₀, G₀, c, N, W, F) ∧ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ξ, ⌜α⌝ₛ, j) ∧
    (∀ o, ⌜Formula.isEmpty⌝ₚ(o) → ⌜rd_entry0_m⌝ₚ(o, j, F))⟫
derive_free_closed wi_success_m
theorem wi_success_sat_l {d} (η : Env M d) (ω α t B Q G : Term d) :
    Formula.satisfies η (wi_success_m ω α t B Q G) ↔
      Wi_success_d hZF (ω.eval η) (α.eval η) (t.eval η) (B.eval η) (Q.eval η) (G.eval η) := by
  simp only [wi_success_m, Wi_success_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isEmpty_iff,
    KP.succ0_sat_l hZF.1, wi_tree_sat_l hZF.1, rd_entry0_sat_l hZF.1, it_branch_sat_l hZF.1,
    wi_limit_sat_l hZF, it_map_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl

def wi_continuous_m {d} (ω a A S α H Q' G' : Term d) : Formula 1 d := set[d] ⟪
  ∃ T Q G P c N W F, ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P) ∧
    ⌜wi_past_m⌝ₚ(⌜H⌝ₛ, Q, G, P) ∧ ⌜rd_entry0_m⌝ₚ(⌜α⌝ₛ, c, ⌜Q'⌝ₛ) ∧
    ⌜wi_limit_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, Q, G, c, N, W, F) ∧
    (∀ i j, i ∈ ⌜α⌝ₛ → (⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, ⌜α⌝ₛ, j) ↔ ⌜rd_entry0_m⌝ₚ(i, j, F)))⟫
derive_free_closed wi_continuous_m
theorem wi_continuous_sat_l {d} (η : Env M d) (ω a A S α H Q' G' : Term d) :
    Formula.satisfies η (wi_continuous_m ω a A S α H Q' G') ↔
      Wi_continuous_d hZF (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (α.eval η) (H.eval η) (Q'.eval η) (G'.eval η) := by
  simp only [wi_continuous_m, Wi_continuous_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    wi_state_sat_l hZF, wi_past_sat_l hZF.1, rd_entry0_sat_l hZF.1, wi_limit_sat_l hZF,
    it_map_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl

/-! 强连续应答的公式层，保留返回树、规范极限及目标枝良基证书。 -/
def wi_continuous_tree_m {d} (ω a A S α H Q' G' : Term d) : Formula 1 d := set[d] ⟪
  ∃ T Q G P c N W F,
    ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P) ∧
    ⌜wi_past_m⌝ₚ(⌜H⌝ₛ, Q, G, P) ∧
    ⌜rd_entry0_m⌝ₚ(⌜α⌝ₛ, c, ⌜Q'⌝ₛ) ∧
    ⌜wi_limit_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, Q, G, c, N, W, F) ∧
    ⌜wi_limit_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, T, Q, G, c, N, W, F) ∧
    ⌜it_wf_branch_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, T, Q, G, ⌜α⌝ₛ) ∧
    (∀ i j, i ∈ ⌜α⌝ₛ →
      (⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, ⌜α⌝ₛ, j) ↔ ⌜rd_entry0_m⌝ₚ(i, j, F)))⟫
derive_free_closed wi_continuous_tree_m

theorem wi_continuous_tree_sat_l {d} (η : Env M d) (ω a A S α H Q' G' : Term d) :
    Formula.satisfies η (wi_continuous_tree_m ω a A S α H Q' G') ↔
      Wi_continuous_tree_d hZF (ω.eval η) (a.eval η) (A.eval η) (S.eval η)
        (α.eval η) (H.eval η) (Q'.eval η) (G'.eval η) := by
  simp only [wi_continuous_tree_m, Wi_continuous_tree_d,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    wi_state_sat_l hZF, wi_past_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    wi_limit_sat_l hZF, wi_limit_tree_sat_l hZF,
    it_wf_branch_sat_l hZF, it_map_sat_l hZF.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def wi_answer_m {d} (ω a A S o s₀ α H t B s : Term d) : Formula 1 d := set[d] ⟪
  ∃ β T Q G P, ⌜KP.succ0_m⌝ₚ(β, ⌜α⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(⌜s⌝ₛ, T, Q, G, P) ∧
    ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, β, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P) ∧ ⌜wi_past_m⌝ₚ(⌜H⌝ₛ, Q, G, P) ∧
    ((⌜α⌝ₛ = ⌜o⌝ₛ ∧ ⌜B⌝ₛ = ⌜o⌝ₛ ∧ ⌜s⌝ₛ = ⌜s₀⌝ₛ) ∨ ⌜wi_success_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜t⌝ₛ, ⌜B⌝ₛ, Q, G) ∨
      (⌜Formula.isLimitOrdinal⌝ₚ(⌜α⌝ₛ) ∧ ⌜B⌝ₛ = ⌜o⌝ₛ ∧ ⌜wi_continuous_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜α⌝ₛ, ⌜H⌝ₛ, Q, G)))⟫
derive_free_closed wi_answer_m
theorem wi_answer_sat_l {d} (η : Env M d) (ω a A S o s₀ α H t B s : Term d) :
    Formula.satisfies η (wi_answer_m ω a A S o s₀ α H t B s) ↔ Wi_answer_d hZF
      (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η) (α.eval η) (H.eval η) (t.eval η) (B.eval η) (s.eval η) := by
  simp only [wi_answer_m, Wi_answer_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_isLimitOrdinal_iff,
    KP.succ0_sat_l hZF.1, rd_quad_sat_l hZF.1, wi_state_sat_l hZF, wi_past_sat_l hZF.1,
    wi_success_sat_l hZF, wi_continuous_sat_l hZF, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 强成功回答的公式层
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
variable (hZF : M.Models ZF)

 def wi_success_tree_m {d} (ω α t B Q G : Term d) : Formula 1 d := set[d] ⟪
  ∃ ξ T₀ Q₀ G₀ E₀ L₀ c N W F j,
    ⌜KP.succ0_m⌝ₚ(⌜α⌝ₛ,ξ) ∧
    ⌜wi_tree_m⌝ₚ(⌜t⌝ₛ,T₀,Q₀,G₀,E₀,L₀) ∧
    ⌜rd_entry0_m⌝ₚ(⌜α⌝ₛ,c,⌜Q⌝ₛ) ∧
    ⌜it_branch_m⌝ₚ(⌜ω⌝ₛ,T₀,⌜B⌝ₛ) ∧
    ⌜it_wf_branch_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,T₀,Q₀,G₀,⌜B⌝ₛ) ∧
    ⌜wi_limit_m⌝ₚ(⌜ω⌝ₛ,⌜B⌝ₛ,Q₀,G₀,c,N,W,F) ∧
    ⌜wi_limit_tree_m⌝ₚ(⌜ω⌝ₛ,⌜B⌝ₛ,T₀,Q₀,G₀,c,N,W,F) ∧
    ⌜it_map_m⌝ₚ(⌜G⌝ₛ,ξ,⌜α⌝ₛ,j) ∧
    (∀ o, ⌜Formula.isEmpty⌝ₚ(o) → ⌜rd_entry0_m⌝ₚ(o,j,F))⟫
derive_free_closed wi_success_tree_m

theorem wi_success_tree_sat_l {d} (η : Env M d) (ω α t B Q G : Term d) :
    Formula.satisfies η (wi_success_tree_m ω α t B Q G) ↔
      Wi_success_tree_d hZF (ω.eval η) (α.eval η) (t.eval η) (B.eval η)
        (Q.eval η) (G.eval η) := by
  simp only [wi_success_tree_m, Wi_success_tree_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isEmpty_iff,
    KP.succ0_sat_l hZF.1, wi_tree_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    it_branch_sat_l hZF.1, it_wf_branch_sat_l hZF, wi_limit_sat_l hZF, wi_limit_tree_sat_l hZF,
    it_map_sat_l hZF.1, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 强迭代应答的总公式

把后继成功枝与连续极限枝统一到同一强证书关系中，供强请求及选择器直接调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
variable (hZF : M.Models ZF)

def wi_answer_tree_m {d} (ω a A S o s₀ α H t B s : Term d) : Formula 1 d := set[d] ⟪
  ∃ β T Q G P,
    ⌜KP.succ0_m⌝ₚ(β, ⌜α⌝ₛ) ∧
    ⌜rd_quad_m⌝ₚ(⌜s⌝ₛ, T, Q, G, P) ∧
    ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, β, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P) ∧
    ⌜wi_past_m⌝ₚ(⌜H⌝ₛ, Q, G, P) ∧
    ((⌜α⌝ₛ = ⌜o⌝ₛ ∧ ⌜B⌝ₛ = ⌜o⌝ₛ ∧ ⌜s⌝ₛ = ⌜s₀⌝ₛ) ∨
      ⌜wi_success_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜t⌝ₛ, ⌜B⌝ₛ, Q, G) ∨
      (⌜Formula.isLimitOrdinal⌝ₚ(⌜α⌝ₛ) ∧ ⌜B⌝ₛ = ⌜o⌝ₛ ∧
        ⌜wi_continuous_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜α⌝ₛ, ⌜H⌝ₛ, Q, G)))⟫
derive_free_closed wi_answer_tree_m

theorem wi_answer_tree_sat_l {d} (η : Env M d) (ω a A S o s₀ α H t B s : Term d) :
    Formula.satisfies η (wi_answer_tree_m ω a A S o s₀ α H t B s) ↔
      Wi_answer_tree_d hZF
        (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η)
        (α.eval η) (H.eval η) (t.eval η) (B.eval η) (s.eval η) := by
  simp only [wi_answer_tree_m, Wi_answer_tree_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isLimitOrdinal_iff,
    KP.succ0_sat_l hZF.1, rd_quad_sat_l hZF.1, wi_state_sat_l hZF,
    wi_past_sat_l hZF.1, wi_success_tree_sat_l hZF,
    wi_continuous_tree_sat_l hZF, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

end YesMetaZFC.SetTheory.LargeCardinal
