import YesMetaZFC.SetTheory.LargeCardinal.IterationTree
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystemCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSyntax

/-! # 原实际超幂边的一阶编码

编码保留全部源分量、直接极限、坍塌和常值方块；满足关系解码回原边证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def ea_agree_m {d} (ω κ X Y : Term d) : Formula 1 d := set[d] ⟪
  ∀ n D A, n ∈ ⌜ω⌝ₛ → ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) → A ⊆ D → (A ∈ ⌜X⌝ₛ ↔ A ∈ ⌜Y⌝ₛ)⟫
derive_free_closed ea_agree_m
theorem ea_agree_sat_l (hE : Extensional M) {d} (η : Env M d) (ω κ X Y : Term d) :
    Formula.satisfies η (ea_agree_m ω κ X Y) ↔ Ea_agree_d (ω.eval η) (κ.eval η) (X.eval η) (Y.eval η) := by
  simp only [ea_agree_m, Ea_agree_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    ep_space_sat_l hE, Definitional.Term.eval_weaken]; rfl

def ep_constants_m {d} (X q i : Term d) : Formula 1 d := set[d] ⟪
  ∀ x E, ⌜rd_entry0_m⌝ₚ(x, E, ⌜i⌝ₛ) → ∃ u a B f D, D ∈ ⌜X⌝ₛ ∧ ⌜sfun_m⌝ₚ(⌜X⌝ₛ, D, f) ∧
    ⌜rs_const_m⌝ₚ(D, x, f) ∧ f ∈ B ∧ ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜rd_entry0_m⌝ₚ(u, E, ⌜q⌝ₛ)⟫
derive_free_closed ep_constants_m

theorem ep_constants_sat_l (hE : Extensional M) {d} (η : Env M d) (X q i : Term d) :
    Formula.satisfies η (ep_constants_m X q i) ↔ Ep_constants_d (X.eval η) (q.eval η) (i.eval η) := by
  simp only [ep_constants_m, Ep_constants_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, sfun_sat_l hE, rs_const_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def it_ultra_m {d} (ω κ L F c d' j : Term d) : Formula 1 d := set[d] ⟪
  ∃ X R Y S J O Z A p T V q b C W i e,
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, X, R) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜d'⌝ₛ, Y, S) ∧
    ⌜ep_system_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, X, R, ⌜F⌝ₛ, J, O, Z, A, p, T, V) ∧
    ⌜di_limit_m⌝ₚ(A, p, T, V, q, C, W) ∧ ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(b, C, W) ∧
    ⌜wc_graph_m⌝ₚ(C, W, e) ∧ ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(e, C, Y) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, b, ⌜d'⌝ₛ, C, Y, e) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, b, X, C, i) ∧ ⌜ep_constants_m⌝ₚ(X, q, i) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜d'⌝ₛ, X, Y, ⌜j⌝ₛ) ∧ ⌜it_comp_m⌝ₚ(i, e, ⌜j⌝ₛ)⟫
derive_free_closed it_ultra_m

theorem it_ultra_sat_l {d} (η : Env M d) (ω κ L F c d' j : Term d) :
    Formula.satisfies η (it_ultra_m ω κ L F c d' j) ↔
      It_ultra_d hZF (ω.eval η) (κ.eval η) (L.eval η) (F.eval η) (c.eval η) (d'.eval η) (j.eval η) := by
  simp only [it_ultra_m, It_ultra_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smem_sat_l I, smdl_sat_l I, ep_system_sat_l hZF, di_limit_sat_l (ZF.modelsKP hZF), wc_graph_sat_l hZF.1,
    Formula.satisfies_isBijectionFromTo_iff I hZF.1, smap_sat_l I hZF.1, ep_constants_sat_l hZF.1,
    it_comp_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]; rfl

def it_source_m {d} (ω c : Term d) : Formula 1 d := set[d] ⟪
  ∃ X R K, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, X, R) ∧ ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, K, X, R)⟫
derive_free_closed it_source_m

theorem it_source_sat_l {d} (η : Env M d) (ω c : Term d) :
    Formula.satisfies η (it_source_m ω c) ↔ It_source_d hZF (ω.eval η) (c.eval η) := by
  simp only [it_source_m, It_source_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smem_sat_l I, ep_source_sat_l hZF, Definitional.Term.eval_weaken]; rfl

def it_payload_m {d} (p κ L F : Term d) : Formula 1 d := set[d] ⟪
  ∃ r, ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜κ⌝ₛ, r) ∧ ⌜kpair0_m⌝ₚ(r, ⌜L⌝ₛ, ⌜F⌝ₛ)⟫
derive_free_closed it_payload_m

theorem it_payload_sat_l (hE : Extensional M) {d} (η : Env M d) (p κ L F : Term d) :
    Formula.satisfies η (it_payload_m p κ L F) ↔ It_payload_d (p.eval η) (κ.eval η) (L.eval η) (F.eval η) := by
  simp only [it_payload_m, It_payload_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
