import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion
import YesMetaZFC.SetTheory.Separation
/-!
# 序数的基数代表
本层证明每个序数都与唯一的初始序数等势。该结论是一般基数论基础设施，不依赖
Aleph 枚举或基数算术。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace ZF
/-- 从给定序数的后继中分离与该序数等势的序数。 -/
private def ordinalCardinalCandidate (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 1 where
  body := .conj (Definitional.Project.Formula.isOrdinal (.bound 0)) (Definitional.Project.Formula.equinumerous 𝒞 (.bound 0) (.bound 1))
/-- 序数基数候选模式的模型语义。 -/
private theorem satisfies_ordinalCardinalCandidate_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ) (env : Env ℳ 1) (candidate : ℳ.Domain) :
    Definitional.Project.Formula.satisfies (env.push candidate) (ordinalCardinalCandidate 𝒞).body ↔
      ℳ.IsOrdinal candidate ∧
        ℳ.Equinumerous 𝕀 candidate (env.bound 0) := by
  simp only [ordinalCardinalCandidate,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_isOrdinal_iff,
    Definitional.Project.Formula.satisfies_equinumerous_iff 𝕀 hExt,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push]
  rfl
/-- 每个序数都有唯一的基数代表。 -/
theorem ordinalCardinal_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {α : ℳ.Domain} (hα : ℳ.IsOrdinal α) :
    ∃ κ,
      ℳ.IsCardinalOf 𝕀 κ α ∧
        ∀ μ, ℳ.IsCardinalOf 𝕀 μ α → μ = κ := by
  rcases KP.exists_successor (ZF.modelsKP hZF) α with
    ⟨successor, hSuccessor⟩
  have hSuccessorOrdinal :
      ℳ.IsOrdinal successor :=
    KP.successor_isOrdinal (ZF.modelsKP hZF) hα hSuccessor
  let env : Env ℳ 1 := {
    bound := fun _ => α
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases separation_exists_d hZF (ordinalCardinalCandidate 𝒞) env successor with
    ⟨candidates, hCandidatesRaw⟩
  have hCandidates (candidate : ℳ.Domain) :
      ℳ.mem candidate candidates ↔
        ℳ.mem candidate successor ∧
          ℳ.IsOrdinal candidate ∧
            ℳ.Equinumerous 𝕀 candidate α := by
    rw [hCandidatesRaw candidate,
      satisfies_ordinalCardinalCandidate_iff 𝕀 hZF.1 env candidate]
  have hCandidatesSubset :
      ℳ.MemberSubset candidates successor := by
    intro candidate hCandidate
    exact (hCandidates candidate).mp hCandidate |>.1
  have hαSuccessor : ℳ.mem α successor := (hSuccessor α).mpr <| Or.inr fun _ => Iff.rfl
  have hαCandidate : ℳ.mem α candidates := (hCandidates α).mpr
      ⟨hαSuccessor, hα,
        Structure.Equinumerous.refl hZF 𝕀 α⟩
  rcases hSuccessorOrdinal.wellOrder.least candidates
      hCandidatesSubset ⟨α, hαCandidate⟩ with
    ⟨κ, hκCandidate, hκLeast⟩
  rcases (hCandidates κ).mp hκCandidate with
    ⟨hκSuccessor, hκOrdinal, hκEquinumerous⟩
  have hκCardinal : ℳ.IsCardinal 𝕀 κ := by
    refine ⟨hκOrdinal, ?_⟩
    intro β hβκ hβκEquinumerous
    have hβOrdinal : ℳ.IsOrdinal β :=
      hκOrdinal.mem hβκ
    have hβSuccessor : ℳ.mem β successor := by
      rcases (hSuccessor κ).mp hκSuccessor with
        hκα | hκSame
      · exact (hSuccessor β).mpr <| Or.inl <|
          hα.transitive κ hκα β hβκ
      · have hκEq := hZF.1.eq_of_same_members κ α hκSame
        subst κ
        exact (hSuccessor β).mpr <| Or.inl hβκ
    have hβEquinumerousα :
        ℳ.Equinumerous 𝕀 β α :=
      hβκEquinumerous.trans hZF 𝕀 hκEquinumerous
    have hβCandidate : ℳ.mem β candidates := (hCandidates β).mpr
        ⟨hβSuccessor, hβOrdinal, hβEquinumerousα⟩
    rcases hκLeast β hβCandidate with
      hSame | hκβ
    · have hEq := hZF.1.eq_of_same_members κ β hSame
      subst β
      exact hκOrdinal.wellOrder.linear.irrefl κ hβκ hβκ
    · have hSelf : ℳ.mem κ κ :=
        hκOrdinal.transitive β hβκ κ hκβ
      exact hκOrdinal.wellOrder.linear.irrefl κ hSelf hSelf
  have hκCardinalOf : ℳ.IsCardinalOf 𝕀 κ α :=
    ⟨hκCardinal, hκEquinumerous⟩
  exact ⟨κ, hκCardinalOf, fun μ hμ =>
    hμ.eq hZF 𝕀 hκCardinalOf⟩
end ZF
end SetTheory
end YesMetaZFC
