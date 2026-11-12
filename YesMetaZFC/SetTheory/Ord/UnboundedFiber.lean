import YesMetaZFC.SetTheory.CumulativeRank
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 集合值的可定义序数关系具有无界纤维

若每个足够大的序数都有一个集合中的颜色，而每种颜色的纤维都有界，
收集这些界再取共同秩界即矛盾。只用 ZF，不要求关系单值或对象选择。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

/-- 原公式定义的集合值关系覆盖序数尾段时，某个实际颜色出现于无界多个高度。 -/
theorem ordinal_unbounded_fiber_l {k} (φ : BinarySchema k) (ρ : Env M k)
    {γ P : M.Domain} (hγ : M.IsOrdinal γ)
    (total : ∀ ν, M.IsOrdinal ν → M.mem γ ν → ∃ t, M.mem t P ∧ φ.denote ρ ν t) :
    ∃ t, M.mem t P ∧ ∀ β, M.IsOrdinal β →
      ∃ ν, M.IsOrdinal ν ∧ M.mem γ ν ∧ M.mem β ν ∧ φ.denote ρ ν t := by
  apply Classical.byContradiction
  intro none
  let ψ : BinarySchema (k+1) := {
    body := .conj (Formula.isOrdinal .newest)
      (.forallE (.imp (Formula.isOrdinal .newest) (.imp (.mem (.bound 3) .newest)
        (.imp (.mem (.bound 1) .newest) (.neg (binary_pred_m φ
          (fun i => .bound ⟨i.val + 4, by omega⟩) .newest (.bound 2))))))) }
  have read t β : ψ.denote (ρ.push γ) t β ↔ M.IsOrdinal β ∧
      ∀ ν, M.IsOrdinal ν → M.mem γ ν → M.mem β ν → ¬ φ.denote ρ ν t := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_neg_iff, binary_pred_sat_l]
    rfl
  obtain ⟨C, bounds⟩ := collection_exists_d hZF ψ (ρ.push γ) P (by
    intro t ht
    apply Classical.byContradiction
    intro noBound
    apply none
    refine ⟨t, ht, fun β hβ => ?_⟩
    apply Classical.byContradiction
    intro noPoint
    exact noBound ⟨β, (read t β).mpr ⟨hβ, fun ν hν hγν hβν h => noPoint ⟨ν, hν, hγν, hβν, h⟩⟩⟩)
  -- 包含 C 与 γ 的秩层同时严格越过所有收集到的序数界。
  let I := kp_pair_l (modelsKP hZF)
  obtain ⟨B, pair⟩ := KP.exists_pair (modelsKP hZF) C γ
  obtain ⟨ν, V, hV, hBV⟩ := v_cover_l I hZF B
  have tr := v_transitive_l I hV
  have hγν := v_ordinal_height_l hZF hV hγ (tr B hBV γ ((pair γ).mpr (Or.inr rfl)))
  obtain ⟨t, ht, h⟩ := total ν (v_ordinal_l I hV) hγν
  obtain ⟨β, hβC, hb⟩ := bounds t ht
  obtain ⟨hβ, bound⟩ := (read t β).mp hb
  exact bound ν (v_ordinal_l I hV) hγν (v_ordinal_height_l hZF hV hβ
    (tr C (tr B hBV C ((pair C).mpr (Or.inl rfl))) β hβC)) h

end YesMetaZFC.SetTheory.ZF
