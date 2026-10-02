import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-! # 由标准实例的正负表示得到最小见证的对象唯一性

相对标准正确输出切分码域。较小或相等的候选由有限负实例排除；较大候选
与正确输出已满足正文矛盾。因此不要求原关系在任意模型中预先具有函数性。
-/
namespace YesMetaZFC.Automation.ObjectLeastWitness
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 闭推导可在任意自由上下文及局部假设下使用。 -/
theorem closed {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    {formula : SetSentence} (h : Derives T [] formula) :
    Derives T Γ (formula.substituteFree (VariableSubstitution.empty : VariableSubstitution signature [] [] free)) := by
  apply FirstOrder.Derives.context_weaken (Γ := []) (by simp)
  exact FirstOrder.Derives.free_substitution VariableSubstitution.empty h

/-- 只消费有限个负实例，排除码域内的全部错误最小见证。 -/
theorem unique {T : SetTheory} (C : Core T) {free : SetContext} {Γ : Context signature free}
    (body : SetFormula [SetSort.set] free) (value : Nat) (point : SetOpenTerm free)
    (hDomain : Derives T Γ (C.code_domain.condition point))
    (hPoint : Derives T Γ (body.instantiateTop point))
    (hEarlier : Derives T Γ (set_levy_bound.boundedForall point (¬ₘ body)))
    (hValue : Derives T Γ (body.instantiateTop (numₘ(value))))
    (hWrong : ∀ index, index ≤ value → index ≠ value → Derives T Γ (¬ₘ body.instantiateTop (numₘ(index)))) :
    Derives T Γ (point ≐ₘ numₘ(value)) := by
  apply C.cut_elim value point _ hDomain
  · intro index hIndex
    have hEq : Derives T ((point ≐ₘ numₘ(index)) :: Γ) (point ≐ₘ numₘ(index)) :=
      FirstOrder.Derives.assumption List.mem_cons_self
    by_cases h : index = value
    · simpa only [h] using hEq
    · apply FirstOrder.Derives.falsum_elim
      exact FirstOrder.Derives.neg_elim
        (FirstOrder.Derives.eq_subst (body := body) hEq (FirstOrder.Derives.context_weaken_cons hPoint))
        (FirstOrder.Derives.context_weaken_cons (hWrong index hIndex h))
  · have hMember : Derives T ((numₘ(value) ∈ₘ point) :: Γ) (numₘ(value) ∈ₘ point) :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hNegative := bounded_forall_elim point (¬ₘ body) (numₘ(value))
      (FirstOrder.Derives.context_weaken_cons hEarlier) hMember
    rw [Formula.instantiateTop_neg] at hNegative
    exact FirstOrder.Derives.falsum_elim (FirstOrder.Derives.neg_elim
      (FirstOrder.Derives.context_weaken_cons hValue) hNegative)

end YesMetaZFC.Automation.ObjectLeastWitness
