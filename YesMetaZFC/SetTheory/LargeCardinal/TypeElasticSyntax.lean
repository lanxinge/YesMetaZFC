import YesMetaZFC.SetTheory.LargeCardinal.TypeElastic
import YesMetaZFC.SetTheory.LargeCardinal.IterationStepSyntax
import YesMetaZFC.Model.SetTheory.Internal.TypeTruthSyntax

/-! # 编码表中的实际弹性关系

这里在背景模型内量化原超幂和完整类型。公式不把候选类型当作真值谕示，
只为已有的实际伸展关系提供可作分离与收集的原语言表示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def et_stretch_raw_m {d} (ω κ L F X R t D v : Term d) : Formula 1 d := set[d] ⟪∃ b c Y S j w,
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(b, ⌜X⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, S) ∧
  ⌜it_ultra_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜F⌝ₛ, b, c, j) ∧
  ⌜rd_entry0_m⌝ₚ(⌜t⌝ₛ, w, j) ∧ (∀ p, p ∈ ⌜v⌝ₛ ↔ p ∈ ⌜D⌝ₛ ∧ p ∈ w)⟫
derive_free_closed et_stretch_raw_m

theorem et_stretch_raw_sat_l {d} (ρ : Env M d) (ω κ L F X R t D v : Term d) :
    Formula.satisfies ρ (et_stretch_raw_m ω κ L F X R t D v) ↔
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) (R.eval ρ)
        (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  simp only [et_stretch_raw_m, Et_stretch_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    smem_sat_l I, it_ultra_sat_l hZF, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def ee_step0_m {d} (ω κ δ n s c X R t τ : Term d) : Formula 1 d := set[d] ⟪∃ L F B U D v,
  L ∈ ⌜δ⌝ₛ ∧ ⌜κ⌝ₛ ∈ L ∧ ⌜τ⌝ₛ ∈ L ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜τ⌝ₛ, B) ∧
  ⌜tt_constants0_m⌝ₚ(⌜τ⌝ₛ, B, U) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, U, D) ∧
  ⌜tt_truth_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜δ⌝ₛ, D, v) ∧
  ⌜ex_quality_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, L, ⌜X⌝ₛ, F) ∧
  ⌜et_stretch_raw_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, L, F, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜t⌝ₛ, D, v)⟫
derive_free_closed ee_step0_m

theorem ee_step0_sat_l {d K} (ρ : Env M d) (ω κ δ n s c X R t τ : Term d)
    (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (ee_step0_m ω κ δ n s c X R t τ) ↔
      Ee_step_d hZF (ω.eval ρ) (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (s.eval ρ) (c.eval ρ)
        (X.eval ρ) (R.eval ρ) (t.eval ρ) (τ.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken.weaken
  have quality L F B U D v := ex_quality_sat_l hZF ((((((ρ.push L).push F).push B).push U).push D).push v)
    (w ω) (w κ) Term.newest.weaken.weaken.weaken.weaken.weaken (w X) Term.newest.weaken.weaken.weaken.weaken
      (by simpa only [w, Definitional.Term.eval_weaken] using source)
  dsimp only [w] at quality
  simp only [ee_step0_m, Ee_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, v_sat_l I hZF.1, tt_constants0_sat_l hZF.1,
    tt_pool_sat_l I (ZF.modelsKP hZF), tt_truth_sat_l I (ZF.modelsKP hZF), quality,
    et_stretch_raw_sat_l hZF, Definitional.Term.eval_weaken, and_assoc]
  rfl

/-- 全高度实现的背景公式，供低自然数程序的统一正确性句子使用。 -/
def ee_realized0_m {d} (ω κ δ n s c X R : Term d) : Formula 1 d := set[d] ⟪∃ B U D t,
  ⌜v_m kpair_convention_l⌝ₚ(⌜κ⌝ₛ, B) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, B, U) ∧
  ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, U, D) ∧ ⌜tt_truth_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜δ⌝ₛ, D, t) ∧
  (∀ τ ∈ ⌜δ⌝ₛ, ⌜ee_step0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜n⌝ₛ, ⌜s⌝ₛ, ⌜c⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, t, τ))⟫
derive_free_closed ee_realized0_m

theorem ee_realized0_sat_l {d K} (ρ : Env M d) (ω κ δ n s c X R : Term d)
    (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (ee_realized0_m ω κ δ n s c X R) ↔
      Ee_realized_d hZF (ω.eval ρ) (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (s.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken.weaken.weaken.weaken
  have read B U D t τ := ee_step0_sat_l hZF (((((ρ.push B).push U).push D).push t).push τ)
    (w ω) (w κ) (w δ) (w n) (w s) (w c) (w X) (w R) Term.newest.weaken .newest
    (by simpa only [w, Definitional.Term.eval_weaken] using source)
  dsimp only [w] at read
  simp only [ee_realized0_m, Ee_realized_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hZF.1, tt_constants0_sat_l hZF.1, tt_pool_sat_l I (ZF.modelsKP hZF),
    tt_truth_sat_l I (ZF.modelsKP hZF), Formula.satisfies_forallMem_iff, read, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
