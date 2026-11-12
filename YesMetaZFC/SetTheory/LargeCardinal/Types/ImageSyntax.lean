import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource

/-! # 类型像的同一扩展器证书

继续分支和回答分支共用秩段、扩展器、超幂及三个实际像。
此处只编码这些共同数据，具体子类型或游戏回答由调用处保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ti_image_m {s} (ω κ δ τ U D u X K R L F c d Y T j κ' U' D' u' : Term s) : Formula 1 s := set[s] ⟪
  ⌜v_sigma_m⌝ₚ(⌜δ⌝ₛ, ⌜X⌝ₛ) ∧ ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜K⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜L⌝ₛ ∈ ⌜δ⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜L⌝ₛ ∧ ⌜τ⌝ₛ ∈ ⌜L⌝ₛ ∧ ⌜ex_quality_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜d⌝ₛ, ⌜Y⌝ₛ, ⌜T⌝ₛ) ∧
  ⌜it_ultra_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜F⌝ₛ, ⌜c⌝ₛ, ⌜d⌝ₛ, ⌜j⌝ₛ) ∧
  ⌜wd_crit_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜j⌝ₛ, ⌜κ⌝ₛ, ⌜κ'⌝ₛ) ∧
  ⌜L⌝ₛ ⊆ ⌜κ'⌝ₛ ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜κ'⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜U⌝ₛ, ⌜U'⌝ₛ, ⌜j⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜D⌝ₛ, ⌜D'⌝ₛ, ⌜j⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜u⌝ₛ, ⌜u'⌝ₛ, ⌜j⌝ₛ)⟫
derive_free_closed ti_image_m

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem ti_image_sat_l {s} (ρ : Env M s) (ω κ δ τ U D u X K R L F c d Y T j κ' U' D' u' : Term s) :
    Formula.satisfies ρ (ti_image_m ω κ δ τ U D u X K R L F c d Y T j κ' U' D' u') ↔
    V_d I (δ.eval ρ) (X.eval ρ) ∧ Ep_source_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (K.eval ρ) (X.eval ρ) (R.eval ρ) ∧
    M.mem (L.eval ρ) (δ.eval ρ) ∧ M.mem (κ.eval ρ) (L.eval ρ) ∧ M.mem (τ.eval ρ) (L.eval ρ) ∧
    It_local_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) ∧
    Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ) ∧
    Ex_strength_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) ∧
    Smem_d I (c.eval ρ) (X.eval ρ) (R.eval ρ) ∧ Smem_d I (d.eval ρ) (Y.eval ρ) (T.eval ρ) ∧
    It_ultra_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (c.eval ρ) (d.eval ρ) (j.eval ρ) ∧
    Wd_crit_d I (X.eval ρ) (j.eval ρ) (κ.eval ρ) (κ'.eval ρ) ∧
    M.MemberSubset (L.eval ρ) (κ'.eval ρ) ∧ M.IsLimitOrdinal (κ'.eval ρ) ∧
    Rd_entry_d (U.eval ρ) (U'.eval ρ) (j.eval ρ) ∧ Rd_entry_d (D.eval ρ) (D'.eval ρ) (j.eval ρ) ∧
    Rd_entry_d (u.eval ρ) (u'.eval ρ) (j.eval ρ) := by
  simp only [ti_image_m, Formula.satisfies_conj_iff, v_sigma_sat_l hKP, ep_source_sat_l hKP,
    Formula.satisfies_mem_iff, smem_sat_l I, it_ultra_sat_l (kp_pair_l hKP) hKP.1, wd_crit_sat_l I hKP.1,
    Formula.satisfies_subset_iff, Formula.satisfies_isLimitOrdinal_iff, rd_entry0_sat_l hKP.1]
  constructor
  · rintro ⟨rank, source, hL, hk, ht, quality, rest⟩
    obtain ⟨loc, card, strong⟩ := (ex_quality_sat_l hKP _ _ _ _ _ _ source).mp quality
    exact ⟨rank, source, hL, hk, ht, loc, card, strong, rest⟩
  · rintro ⟨rank, source, hL, hk, ht, loc, card, strong, rest⟩
    exact ⟨rank, source, hL, hk, ht, (ex_quality_sat_l hKP _ _ _ _ _ _ source).mpr ⟨loc, card, strong⟩, rest⟩

end YesMetaZFC.SetTheory.LargeCardinal
