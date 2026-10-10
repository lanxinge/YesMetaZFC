import YesMetaZFC.Model.SetTheory.Internal.SupportBound
import YesMetaZFC.Model.SetTheory.Internal.Induction

/-! # 内部有限支撑上的真值一致性

两份完整赋值若在程序坐标界内相同，则每一行真值相同。量词步对两份赋值
更新同一变量、同一见证；归纳性质是实际满足公式，覆盖全部内部有限程序。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ssat_agree_l (hZF : M.Models ZF) {ω X R E F n b r f g}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hE : M.IsFunctionSpace I E ω X)
    (hr : M.mem r n) (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g) :
    Ssat_d I X R E F n r f ↔ Ssat_d I X R E F n r g := by
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  let ρ : Env M 6 := (((((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push E).push F).push n).push b
  let φ : UnarySchema 6 := {
    body := Formula.forallMem (.bound 4) (Formula.forallMem (.bound 5)
      (.imp (senv_agree_m (𝒞 := 𝒞) (.bound 3) (.bound 1) .newest)
        (.iff (ssat_m (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 1))
          (ssat_m (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)))) }
  have hφ k : φ.denote ρ k ↔ ∀ f, M.mem f E → ∀ g, M.mem g E → Senv_agree_d I b f g →
      (Ssat_d I X R E F n k f ↔ Ssat_d I X R E F n k g) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, senv_agree_sat_l I, ssat_sat_l I hZF.1]
    rfl
  suffices hh : φ.denote ρ r from (hφ r).mp hh f hf g hg ha
  apply sfm_induction_l I hZF hF φ ρ ?_ hr
  intro r hr ih
  apply (hφ r).mpr
  intro f hf g hg ha
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨hib, hjb⟩ := hb.operands_l I hc hs
    obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 i hi
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 j hj
    exact (ssat_rel_l I hZF hF hH hc hs hE hf hx hy).trans
      (ssat_rel_l I hZF hF hH hc hs hE hg ((ha i x hib).mp hx) ((ha j y hjb).mp hy)).symm
  · obtain ⟨hib, hjb⟩ := hb.operands_l I hc hs
    obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 i hi
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 j hj
    exact (ssat_eq_l I hZF hF hH hc hs hE hf hx hy).trans
      (ssat_eq_l I hZF hF hH hc hs hE hg ((ha i x hib).mp hx) ((ha j y hjb).mp hy)).symm
  · rw [ssat_nor_l I hZF hF hH hc hs hf, ssat_nor_l I hZF hF hH hc hs hg]
    exact not_congr (or_congr ((hφ i).mp (ih i hi) f hf g hg ha) ((hφ j).mp (ih j hj) f hf g hg ha))
  · have transfer {f g} (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g) :
        (∃ x h, M.mem x X ∧ Senv_update_d I f i x h ∧ Ssat_d I X R E F n j h) →
          ∃ x k, M.mem x X ∧ Senv_update_d I g i x k ∧ Ssat_d I X R E F n j k := by
      rintro ⟨x, h, hx, hh, ht⟩
      obtain ⟨k, hk, hK⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi hx
      have hhE := (hE h).mpr (hh.function_l I ((hE f).mp hf) hi hx)
      exact ⟨x, k, hx, hk, ((hφ j).mp (ih j hj) h hhE k ((hE k).mpr hK) (ha.update_l I hh hk)).mp ht⟩
    rw [ssat_exists_l I hZF hF hH hc hs hf, ssat_exists_l I hZF hF hH hc hs hg]
    exact ⟨transfer hf hg ha, transfer hg hf (ha.symm_l I)⟩

end YesMetaZFC.SetTheory.Internal
