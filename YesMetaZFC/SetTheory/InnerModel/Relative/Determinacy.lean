import YesMetaZFC.SetTheory.InnerModel.Relative.LReal
import YesMetaZFC.SetTheory.Descriptive.Determinacy

/-! # L(ℝ) 中 AD 的原句子与实际模型语义

未来的大基数定理以本句子为结论。本层只建立精确陈述及其语义对应，
不把尚未证明的武丁基数到决定性的推论加入任何构造或实例。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

private theorem la_ad_sat_l (S : M.Domain) (hS : M.TransitiveSet S) {d}
    (ρ : Env M d) (T : Term d) (hT : T.eval ρ = S) :
    Formula.satisfies ρ (la_rel_m (ad_m kpair_convention_l) T Fin.elim0) ↔
      (la_model_l S (ZF.models_kpi_l hZF)).SatisfiesSentence Axioms.ad_axiom := by
  let η : Env (la_model_l S (ZF.models_kpi_l hZF)) 0 :=
    ⟨Fin.elim0, fun _ => ⟨S, la_seed_l S (ZF.models_kpi_l hZF)⟩⟩
  have h := la_rel_sat_l (ZF.models_kpi_l hZF) S hS (ad_m kpair_convention_l) ad_closed_l η ρ T Fin.elim0 hT (fun i => Fin.elim0 i)
  exact h.trans ((ad_sat_l (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF hS)))
    (la_model_ext_l S (ZF.models_kpi_l hZF) hS) η).trans (ad_axiom_sat_l (ZF.modelsKP (la_model_zf_l S hZF hS))).symm)

def lr_ad_m : Formula 1 0 := .existsE (.existsE (.existsE
  (.conj (baire_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1))
    (.conj (tc_m (.bound 1) .newest)
      (la_rel_m (ad_m kpair_convention_l) .newest Fin.elim0)))))

theorem lr_ad_closed_l : lr_ad_m.FreeClosed := by
  simp only [lr_ad_m, Definitional.Formula.FreeClosed]
  exact ⟨baire_free_l _ _ rfl rfl, tc_m_freeClosed _ _ rfl rfl,
    la_rel_closed_l _ ad_closed_l _ _ rfl (fun i => Fin.elim0 i)⟩

theorem lr_ad_sat_l (ρ : Env M 0) : Formula.satisfies ρ lr_ad_m ↔
    (lr_model_l hZF).SatisfiesSentence Axioms.ad_axiom := by
  simp only [lr_ad_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    baire_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, tc_sat_l]
  constructor
  · rintro ⟨ω, B, S, hB, hS, ht⟩
    have h : Lr_seed_d hZF ω B S := ⟨hB, hS⟩
    rw [lr_model_eq_l hZF h]
    exact (la_ad_sat_l hZF S hS.1 _ .newest rfl).mp ht
  · intro ht
    obtain ⟨ω, B, S, h⟩ := lr_seed_exists_l hZF
    rw [lr_model_eq_l hZF h] at ht
    exact ⟨ω, B, S, h.1, h.2, (la_ad_sat_l hZF S h.2.1 _ .newest rfl).mpr ht⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel.Relative
universe u

def Axioms.lr_ad : Sentence := Sentence.ofFormula lr_ad_m lr_ad_closed_l

theorem lr_ad_axiom_sat_l {M : Structure.{u}} (hZF : M.Models ZF) :
    M.SatisfiesSentence Axioms.lr_ad ↔ (lr_model_l hZF).SatisfiesSentence Axioms.ad_axiom := by
  rw [Structure.satisfiesSentence_iff]
  constructor
  · intro h
    obtain ⟨x⟩ := M.nonempty
    exact (lr_ad_sat_l hZF ⟨Fin.elim0, fun _ => x⟩).mp (h (fun _ => x))
  · exact fun h f => (lr_ad_sat_l hZF ⟨Fin.elim0, f⟩).mpr h

end YesMetaZFC.SetTheory
