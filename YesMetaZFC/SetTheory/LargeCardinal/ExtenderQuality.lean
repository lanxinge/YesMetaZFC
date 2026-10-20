import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLocalFormula
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthPull
import YesMetaZFC.Model.SetTheory.Internal.FiniteSpaceBounded

/-! # 短扩展器、不可达支撑与最大强度的单一有界公式

所需有限列空间由公式量化并完整识别。最大强度仍由同一张扩展器的
原有界超幂和缺失子集判定；没有外部提供的强度值表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def ex_strength_m {d} (ω κ L X F : Term d) : Formula 1 d := set[d] ⟪
  ⌜L⌝ₛ ∈ ⌜X⌝ₛ ∧ (∃ K ∈ ⌜X⌝ₛ, ∃ H ∈ ⌜X⌝ₛ,
    ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜κ⌝ₛ, K) ∧ ⌜fs_space0_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜L⌝ₛ, H) ∧
    ⌜ex_strength0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ, K, H))⟫
derive_free_closed ex_strength_m

theorem ex_strength_delta_l {d} (ω κ L X F : Term d) : (ex_strength_m ω κ L X F).IsDelta0 :=
  .conj (.mem ..) (.existsMem _ (.existsMem _ (.conj (fs_space0_delta_l ..)
    (.conj (fs_space0_delta_l ..) (ex_strength0_delta_l ..)))))

def ex_quality_m {d} (ω κ L X F : Term d) : Formula 1 d :=
  .conj (ex_local_m ω κ L X F) (.conj (ex_inaccessible_m ω X L) (ex_strength_m ω κ L X F))
derive_free_closed ex_quality_m

theorem ex_quality_delta_l {d} (ω κ L X F : Term d) : (ex_quality_m ω κ L X F).IsDelta0 :=
  .conj (ex_local_delta_l ..) (.conj (ex_inaccessible_delta_l ..) (ex_strength_delta_l ..))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ex_strength_sat_l {d K₀ R} (ρ : Env M d) (ω κ L X F : Term d)
    (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K₀ (X.eval ρ) R) :
    Formula.satisfies ρ (ex_strength_m ω κ L X F) ↔
      Ex_strength_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
  let w (a : Term d) := a.weaken.weaken
  have sk K H : Formula.satisfies ((ρ.push K).push H)
      (fs_space0_m (w ω) (w X) (w κ) Term.newest.weaken) ↔ K = K₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := K₀) ((ρ.push K).push H) (w ω) (w X) (w κ) Term.newest.weaken
        (by simpa only [w, Definitional.Term.eval_weaken] using source.finite)
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive K₀ source.finite_mem)
  have sl K H H₀ (seq : Fseq_space_d I (ω.eval ρ) (L.eval ρ) H₀) (hH : M.mem H₀ (X.eval ρ)) :
      Formula.satisfies ((ρ.push K).push H) (fs_space0_m (w ω) (w X) (w L) .newest) ↔ H = H₀ := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      fs_space0_iff_l (ZF.modelsKP hZF) (K₀ := H₀) ((ρ.push K).push H) (w ω) (w X) (w L) .newest
        (by simpa only [w, Definitional.Term.eval_weaken] using seq)
        (by simpa only [w, Definitional.Term.eval_weaken, Structure.MemberSubset] using source.transitive H₀ hH)
  have core H (seq : Fseq_space_d I (ω.eval ρ) (L.eval ρ) H) :
      Formula.satisfies ((ρ.push K₀).push H) (ex_strength0_m (w ω) (w κ) (w L) (w X) (w F) Term.newest.weaken .newest) ↔
      Ex_strength_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
    simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      ex_strength0_sat_l hZF ((ρ.push K₀).push H) (w ω) (w κ) (w L) (w X) (w F) Term.newest.weaken .newest
        (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using source.finite)
        (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using seq)
  dsimp only [w] at sk sl core
  simp only [ex_strength_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, sk, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hL, K, _, H, _, eqK, space, matrix⟩
    subst K
    obtain ⟨H₀, hH₀, seq⟩ := source.sequences.space (L.eval ρ) hL
    have eqH := (sl K₀ H H₀ seq hH₀).mp space
    subst H
    exact (core H₀ seq).mp matrix
  · intro strength
    have hL := strength.2.2.1
    obtain ⟨H, hH, seq⟩ := source.sequences.space (L.eval ρ) hL
    exact ⟨hL, K₀, source.finite_mem, H, hH, rfl, (sl K₀ H H seq hH).mpr rfl, (core H seq).mpr strength⟩

theorem ex_quality_sat_l {d K R} (ρ : Env M d) (ω κ L X F : Term d)
    (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) R) :
    Formula.satisfies ρ (ex_quality_m ω κ L X F) ↔
      It_local_d (ω.eval ρ) (X.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) ∧
      Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ) ∧
      Ex_strength_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) :=
  (Formula.satisfies_conj_iff ..).trans (and_congr (ex_local_sat_l ρ ω κ L X F source.transitive)
    ((Formula.satisfies_conj_iff ..).trans (and_congr (ex_inaccessible_sat_l ρ ω X L source.transitive)
      (ex_strength_sat_l hZF ρ ω κ L X F source))))

end YesMetaZFC.SetTheory.LargeCardinal
