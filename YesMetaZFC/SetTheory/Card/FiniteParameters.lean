import YesMetaZFC.SetTheory.Card.Finite

/-! # 外部有限参数列的实际内部有限集合

这里只对原公式参数个数作宿主归纳。返回模型内的有限性见证和精确成员式，
不把模型的内部有限集合或 ω 当作宿主有限对象。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem finite_params_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) {n} (v : Fin n → M.Domain) :
    ∃ A, Finite_d I ω A ∧ ∀ x, M.mem x A ↔ ∃ i, v i = x := by
  induction n with
  | zero =>
    obtain ⟨A, hA⟩ := KP.exists_empty (ZF.modelsKP hZF)
    exact ⟨A, finite_empty_l I hZF hω hA, fun x =>
      ⟨fun hx => (hA x hx).elim, fun ⟨i, _⟩ => Fin.elim0 i⟩⟩
  | succ n ih =>
    obtain ⟨A, ha, hA⟩ := ih (fun i => v i.succ)
    obtain ⟨B, hB⟩ := KP.exists_insert (ZF.modelsKP hZF) A (v 0)
    refine ⟨B, finite_insert_l I hZF hω ha hB, fun x => (hB x).trans ⟨?_, ?_⟩⟩
    · rintro (hx | rfl)
      · obtain ⟨i, hi⟩ := (hA x).mp hx
        exact ⟨i.succ, hi⟩
      · exact ⟨0, rfl⟩
    · rintro ⟨i, rfl⟩
      exact Fin.cases (Or.inr rfl) (fun i => Or.inl ((hA _).mpr ⟨i, rfl⟩)) i

end YesMetaZFC.SetTheory.ZF
