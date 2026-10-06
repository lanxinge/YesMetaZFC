import YesMetaZFC.SetTheory.LargeCardinal.IterationModel
import YesMetaZFC.SetTheory.LargeCardinal.IterationCoherence

/-! # 下降历史的实际模型行及全前驱公式

历史行只记录模型、嵌入图及可数编号；原树的模型码和支撑图作为固定参数。
所有前驱一致性都由同一个公式检查，不对宿主自然数作任何有限性假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def pn_rank_m {d} (X α V : Term d) : Formula 1 d := set[d] ⟪
  ∃ B ∈ ⌜X⌝ₛ, ∃ F ∈ ⌜X⌝ₛ, ∀ t ∈ ⌜X⌝ₛ, ⌜vc_matrix_m⌝ₚ(⌜α⌝ₛ, ⌜V⌝ₛ, B, F, t)⟫
derive_free_closed pn_rank_m

theorem pn_rank_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X α V : Term d) :
    Formula.satisfies ρ (pn_rank_m X α V) ↔ Vr_d (X.eval ρ) (α.eval ρ) (V.eval ρ) := by
  simp only [pn_rank_m, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    vc_matrix_sat_l hKP, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨B, hB, F, hF, h⟩ => ⟨B, F, hB, hF, h⟩,
    fun ⟨B, F, hB, hF, h⟩ => ⟨B, hB, F, hF, h⟩⟩

def pn_agree_m {d} (X Y π N Z σ ρ φ : Term d) : Formula 1 d := set[d] ⟪
  Trans(⌜X⌝ₛ) ∧ Trans(⌜Y⌝ₛ) ∧ Trans(⌜N⌝ₛ) ∧ Trans(⌜Z⌝ₛ) ∧
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜ρ⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜φ⌝ₛ) ∧
  (∃ W ∈ ⌜X⌝ₛ, W ∈ ⌜N⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜X⌝ₛ, ⌜ρ⌝ₛ, W) ∧ ⌜pn_rank_m⌝ₚ(⌜N⌝ₛ, ⌜ρ⌝ₛ, W) ∧
    (∀ x ∈ W, ∀ y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜π⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(x, y, ⌜σ⌝ₛ))) ∧
  (∃ V ∈ ⌜Y⌝ₛ, V ∈ ⌜Z⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜Y⌝ₛ, ⌜φ⌝ₛ, V) ∧ ⌜pn_rank_m⌝ₚ(⌜Z⌝ₛ, ⌜φ⌝ₛ, V)) ∧
  ⌜rd_entry0_m⌝ₚ(⌜ρ⌝ₛ, ⌜φ⌝ₛ, ⌜π⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜ρ⌝ₛ, ⌜φ⌝ₛ, ⌜σ⌝ₛ)⟫
derive_free_closed pn_agree_m

theorem pn_agree_sat_l (hKP : M.Models KP) {d} (η : Env M d) (X Y π N Z σ ρ φ : Term d) :
    Formula.satisfies η (pn_agree_m X Y π N Z σ ρ φ) ↔
      Pn_agree_d (X.eval η) (Y.eval η) (π.eval η) (N.eval η) (Z.eval η) (σ.eval η) (ρ.eval η) (φ.eval η) := by
  simp only [pn_agree_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    rd_entry0_sat_l hKP.1, pn_rank_sat_l hKP, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨a, b, c, d, l, m, ⟨W, wx, wn, w, w', p⟩, q, r, s⟩
    exact ⟨a, b, c, d, l, m, ⟨W, wx, wn, w, w', fun x y hx => p x hx y⟩, q, r, s⟩
  · intro h
    obtain ⟨W, wx, wn, w, w', p⟩ := h.source_rank
    exact ⟨h.source_left, h.target_left, h.source_right, h.target_right, h.source_limit, h.target_limit,
      ⟨W, wx, wn, w, w', fun x hx y => p x y hx⟩, h.target_rank, h.left_end, h.right_end⟩

def pn_strength_m {d} (X L Y : Term d) : Formula 1 d := set[d] ⟪
  (∀ α ∈ ⌜L⌝ₛ, ∀ x ∈ ⌜X⌝ₛ, x ⊆ α → x ∈ ⌜Y⌝ₛ) ∧
  (∃ x ∈ ⌜X⌝ₛ, x ⊆ ⌜L⌝ₛ ∧ x ∉ ⌜Y⌝ₛ)⟫
derive_free_closed pn_strength_m

theorem pn_strength_sat_l {d} (ρ : Env M d) (X L Y : Term d) :
    Formula.satisfies ρ (pn_strength_m X L Y) ↔ Es_strength_d (X.eval ρ) (L.eval ρ) (Y.eval ρ) := by
  simp only [pn_strength_m, Es_strength_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

def Pn_row_d (ω a X P π ι : M.Domain) : Prop := M.TransitiveSet X ∧ ∃ R S c μ K,
  Smem_d I a X R ∧ Smem_d I c P S ∧ Pn_model_d hZF ω μ K P S ∧ M.mem π P ∧ M.mem ι P ∧
    Smap_d I ω a c X P π ∧ M.IsSetInjectionFromTo I ι π ω

def pn_row_m {d} (ω a X P π ι : Term d) : Formula 1 d := set[d] ⟪
  Trans(⌜X⌝ₛ) ∧ (∃ R S c μ K, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, ⌜X⌝ₛ, R) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, ⌜P⌝ₛ, S) ∧ ⌜pn_model_m⌝ₚ(⌜ω⌝ₛ, μ, K, ⌜P⌝ₛ, S) ∧
    ⌜π⌝ₛ ∈ ⌜P⌝ₛ ∧ ⌜ι⌝ₛ ∈ ⌜P⌝ₛ ∧ ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, c, ⌜X⌝ₛ, ⌜P⌝ₛ, ⌜π⌝ₛ) ∧
    ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(⌜ι⌝ₛ, ⌜π⌝ₛ, ⌜ω⌝ₛ))⟫
derive_free_closed pn_row_m

theorem pn_row_sat_l {d} (ρ : Env M d) (ω a X P π ι : Term d) : Formula.satisfies ρ (pn_row_m ω a X P π ι) ↔
    Pn_row_d hZF (ω.eval ρ) (a.eval ρ) (X.eval ρ) (P.eval ρ) (π.eval ρ) (ι.eval ρ) := by
  simp only [pn_row_m, Pn_row_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff, smem_sat_l I, pn_model_sat_l hZF, Formula.satisfies_mem_iff, smap_sat_l I hZF.1,
    Formula.satisfies_isInjectionFromTo_iff I hZF.1, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
