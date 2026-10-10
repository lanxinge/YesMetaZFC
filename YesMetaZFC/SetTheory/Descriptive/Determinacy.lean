import YesMetaZFC.SetTheory.Descriptive.Game
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # AD 的原一阶句子

收益集合遍历内部 Baire 空间的全部内部子集；策略和对局也由同一模型量化。
存在量化的 ω、Baire 空间和有限局面空间在 ZF 中自动构造且唯一。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def AD_d : Prop := ∃ ω B T, Baire_d I ω B ∧ Fseq_space_d I ω ω T ∧
  ∀ A, M.MemberSubset A B → Det_d I ω B T A

def ad_m (𝒞 : OrderedPairConvention) : Formula 1 0 :=
  .existsE (.existsE (.existsE (.conj (baire_m (𝒞 := 𝒞) (.bound 2) (.bound 1))
    (.conj (fseq_space_m (𝒞 := 𝒞) (.bound 2) (.bound 2) .newest)
      (.forallE (.imp (Formula.subset .newest (.bound 2))
        (det_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest)))))))

theorem ad_closed_l : (ad_m 𝒞).FreeClosed := by
  simp -implicitDefEqProofs [ad_m, Definitional.Formula.FreeClosed]

theorem ad_sat_l (hE : Extensional M) (ρ : Env M 0) :
    Formula.satisfies ρ (ad_m 𝒞) ↔ AD_d I := by
  simp only [ad_m, AD_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    baire_sat_l I hE, fseq_space_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, det_sat_l I hE]
  rfl

/-- 固定任何实际空间后，AD 恰好断言每个收益集合有一方的内部获胜策略。 -/
theorem ad_iff_l (hE : Extensional M) {ω B T} (hB : Baire_d I ω B) (hT : Fseq_space_d I ω ω T) :
    AD_d I ↔ ∀ A, M.MemberSubset A B → Det_d I ω B T A := by
  refine ⟨?_, fun h => ⟨ω, B, T, hB, hT, h⟩⟩
  rintro ⟨v, C, U, hC, hU, h⟩
  have ev : v = ω := hE.eq_of_same_members v ω (fun n =>
    ⟨hC.1.2 ω hB.1.1 n, hB.1.2 v hC.1.1 n⟩)
  subst v
  have eC := baire_unique_l I hE hC hB
  subst C
  have eU : U = T := hE.eq_of_same_members U T (fun s => (hU s).trans (hT s).symm)
  exact eU ▸ h

end YesMetaZFC.SetTheory.Descriptive

namespace YesMetaZFC.SetTheory
open Definitional.Project

def Axioms.ad_axiom : Sentence := Sentence.ofFormula
  (Descriptive.ad_m kpair_convention_l) Descriptive.ad_closed_l

namespace ZFAD
inductive Axiom : Theory where
  | zf {s : Sentence} : ZF s → Axiom s
  | ad : Axiom Axioms.ad_axiom
end ZFAD

abbrev ZFAD : Theory := ZFAD.Axiom

theorem ad_axiom_sat_l {M : Structure.{u}} (hKP : M.Models KP) :
    M.SatisfiesSentence Axioms.ad_axiom ↔ Descriptive.AD_d (InnerModel.kp_pair_l hKP) := by
  rw [Structure.satisfiesSentence_iff]
  constructor
  · intro h
    obtain ⟨x⟩ := M.nonempty
    exact (Descriptive.ad_sat_l (InnerModel.kp_pair_l hKP) hKP.1 ⟨Fin.elim0, fun _ => x⟩).mp (h (fun _ => x))
  · intro h f
    exact (Descriptive.ad_sat_l (InnerModel.kp_pair_l hKP) hKP.1 ⟨Fin.elim0, f⟩).mpr h

end YesMetaZFC.SetTheory
