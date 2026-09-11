import YesMetaZFC.Automation.Guards

/-!
# 命题子句与守卫的公共语义

规范化、赋值传输和守卫学习不依赖对象语言；FO 与 HO 回放只提供各自的文字解释。
-/
namespace YesMetaZFC.Automation
namespace PropResolution

theorem Lit.holds_neg_iff {valuation : Valuation} {lit : Lit} :
    lit.neg.Holds valuation ↔ ¬ lit.Holds valuation := by
  classical
  cases lit with
  | mk var positive => cases positive <;> simp [Lit.Holds, Lit.neg]

namespace Clause

theorem satisfies_canonical_iff {valuation : Valuation} {clause : Clause} :
    Satisfies valuation (canonicalClause clause) ↔ Satisfies valuation clause := by
  constructor
  · rintro ⟨lit, hMem, hHolds⟩
    exact ⟨lit, mem_of_mem_canonicalClauseList hMem, hHolds⟩
  · rintro ⟨lit, hMem, hHolds⟩
    exact ⟨lit, mem_canonicalClause_of_mem hMem, hHolds⟩

theorem satisfies_append_iff {valuation : Valuation} {left right : Clause} :
    Satisfies valuation (left ++ right) ↔
      Satisfies valuation left ∨ Satisfies valuation right := by
  simp only [Satisfies, Array.toList_append, List.mem_append, or_and_right,
    exists_or]

theorem Satisfies.transfer {source target : Valuation} {clause : Clause}
    (hClause : Satisfies source clause)
    (hTransfer : ∀ lit, lit ∈ clause.toList → lit.Holds source → lit.Holds target) :
    Satisfies target clause := by
  rcases hClause with ⟨lit, hMem, hHolds⟩
  exact ⟨lit, hMem, hTransfer lit hMem hHolds⟩

end Clause
end PropResolution

namespace Guards
open PropResolution

theorem learnedClause_satisfies_iff {valuation : Valuation} {guards : Set} :
    Clause.Satisfies valuation (learnedClause guards) ↔
      ¬ ∀ lit, lit ∈ (canonical guards).toList → lit.Holds valuation := by
  classical
  rw [learnedClause, canonical, Clause.satisfies_canonical_iff]
  simp only [Clause.Satisfies, Array.toList_map, List.mem_map]
  constructor
  · rintro ⟨_, ⟨lit, hMem, rfl⟩, hHolds⟩ hGuards
    exact Lit.holds_neg_iff.mp hHolds
      (hGuards lit (mem_canonicalClause_of_mem hMem))
  · intro hGuards
    simp only [Classical.not_forall] at hGuards
    rcases hGuards with ⟨lit, hMem, hNot⟩
    exact ⟨lit.neg, ⟨lit, mem_of_mem_canonical hMem, rfl⟩,
      Lit.holds_neg_iff.mpr hNot⟩

/-- 激活子句表示守卫合取蕴含正文；两种赋值须在每个原守卫上保持真值。 -/
theorem activation_satisfies {base valuation : Valuation} {guards : Set}
    {clause : Clause}
    (hTransfer : ∀ lit, lit ∈ guards.toList →
      (lit.Holds valuation ↔ lit.Holds base))
    (hBody : (∀ lit, lit ∈ (canonical guards).toList → lit.Holds base) →
      Clause.Satisfies valuation clause) :
    Clause.Satisfies valuation (canonicalClause (guards.map Lit.neg ++ clause)) := by
  classical
  apply Clause.satisfies_canonical_iff.mpr
  apply Clause.satisfies_append_iff.mpr
  by_cases hGuards : ∀ lit, lit ∈ (canonical guards).toList → lit.Holds valuation
  · exact Or.inr (hBody fun lit hMem =>
      (hTransfer lit (mem_of_mem_canonical hMem)).mp (hGuards lit hMem))
  · exact Or.inl (Clause.satisfies_canonical_iff.mp
      (learnedClause_satisfies_iff.mpr hGuards))

end Guards
end YesMetaZFC.Automation
