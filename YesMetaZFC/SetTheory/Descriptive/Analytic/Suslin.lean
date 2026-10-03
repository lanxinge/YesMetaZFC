import YesMetaZFC.SetTheory.Descriptive.Analytic.Separation
import YesMetaZFC.SetTheory.Descriptive.Analytic.Diagonal

/-! # Suslin 定理：解析且余解析当且仅当 Borel -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem suslin_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    Borel_d I ω A A B K ↔ An_d I ω A B J K ∧ Coan_d I ω A B J K := by
  constructor
  · intro hk
    obtain ⟨L, hl, hb⟩ := borel_compl_l I hZF hB.1 hA hk
    have sub : M.MemberSubset K B := hk.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
    exact ⟨borel_an_l I hZF hB hA ha hJ hk,
      L, borel_an_l I hZF hB hA ha hJ hb, cm_symm_l sub hl⟩
  · rintro ⟨hk, L, hl, hc⟩
    obtain ⟨C, hb, sub, disj⟩ := an_separation_l I hZF hB hA ha hJ hk hl
      (fun x ⟨hx, hy⟩ => ((hc x).mp hx).2 hy)
    have cb : M.MemberSubset C B := hb.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
    have e := hZF.1.eq_of_same_members C K (fun x => ⟨fun hx => (hc x).mpr
      ⟨cb x hx, fun hy => disj x ⟨hx, hy⟩⟩, sub x⟩)
    exact e ▸ hb

end YesMetaZFC.SetTheory.Descriptive
