import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectMinimumRelation

/-! # 对象关系的存在连接

固定模板通过 bound 量词连接，开闭变量只使用内核的类型安全变换。
-/
namespace YesMetaZFC.Automation.ObjectRelationBinder
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 对原始 bound 正文使用规范 fresh 存在消去。 -/
theorem eliminate {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (body : SetFormula [SetSort.set] free) {conclusion : SetOpenFormula free}
    (h : Derives T Γ (.existsE SetSort.set body))
    (hCase : Derives T (body.openBoundTop SetSort.set :: FreshVariable.extendContext SetSort.set Γ)
      (conclusion.weakenFree SetSort.set)) : Derives T Γ conclusion := by
  apply FirstOrder.Derives.exists_elim (body := body.openBoundTop SetSort.set) _ hCase
  simpa only [Formula.existsFreeTop_openBoundTop] using h

/-- 三元模板与 fresh 自由扩张交换。 -/
@[simp] theorem weaken_three (R : FormulaTemplate.Ternary) {bound free : SetContext}
    (first second third : SetTerm bound free) :
    (R first second third).weakenFree SetSort.set =
      R (first.weakenFree SetSort.set) (second.weakenFree SetSort.set) (third.weakenFree SetSort.set) := by
  rw [Formula.weakenFree_eq_renameMapped, ← Formula.substituteMapped_of_renaming,
    FormulaTemplate.apply_three_substituteMapped]
  congr 1
  · exact Term.substituteMapped_of_renaming (VariableRenaming.weaken SetSort.set) first
  · exact Term.substituteMapped_of_renaming (VariableRenaming.weaken SetSort.set) second
  · exact Term.substituteMapped_of_renaming (VariableRenaming.weaken SetSort.set) third

@[simp] theorem numeral_at {bound free : SetContext} (number : Nat) (point : SetTerm bound free) :
    (numₘ(number) : SetTerm (SetSort.set :: bound) free).instantiateTop point = numₘ(number) := by
  simp only [Term.instantiateTop, Term.substitute, Substitution.instantiateTop, finite_numeral_term_substituteMapped]

/-- 二元模板的第二槽由顶部 bound 变量填充。 -/
theorem second_at (R : FormulaTemplate.Binary) {free : SetContext}
    (left point : SetOpenTerm free) :
    (R (left.weakenBound SetSort.set) (.bvar .here)).instantiateTop point = R left point := by
  change (R.instantiate (VariableSubstitution.cons (left.weakenBound SetSort.set)
    (VariableSubstitution.cons (.bvar .here) VariableSubstitution.empty))).instantiateTop point =
      R.instantiate (VariableSubstitution.cons left (VariableSubstitution.cons point VariableSubstitution.empty))
  rw [FormulaTemplate.instantiate_top]
  congr
  funext sort entry
  cases entry with
  | here => simp [VariableSubstitution.cons]
  | there previous =>
    cases previous with
    | here => rfl
    | there impossible => exact nomatch impossible

/-- 标准参数处的闭三元事实可用于任意自由及局部上下文。 -/
theorem closed_three {T : SetTheory} (R : FormulaTemplate.Ternary) {free : SetContext}
    {Γ : Context signature free} (first second third : Nat)
    (h : Derives T [] (R (numₘ(first)) (numₘ(second)) (numₘ(third) : SetOpenTerm []))) :
    Derives T Γ (R (numₘ(first)) (numₘ(second)) (numₘ(third))) := by
  simpa only [Formula.substituteFree, Formula.substitute, Substitution.free_map,
    FormulaTemplate.apply_three_substituteMapped, finite_numeral_term_substituteMapped]
    using ObjectLeastWitness.closed (free := free) (Γ := Γ) h

theorem closed_three_negative {T : SetTheory} (R : FormulaTemplate.Ternary) {free : SetContext}
    {Γ : Context signature free} (first second third : Nat)
    (h : Derives T [] (¬ₘ R (numₘ(first)) (numₘ(second)) (numₘ(third) : SetOpenTerm []))) :
    Derives T Γ (¬ₘ R (numₘ(first)) (numₘ(second)) (numₘ(third))) := by
  simpa only [Formula.substituteFree, Formula.substitute, Substitution.free_map,
    Formula.substituteMapped, FormulaTemplate.apply_three_substituteMapped,
    finite_numeral_term_substituteMapped]
    using ObjectLeastWitness.closed (free := free) (Γ := Γ) h

end YesMetaZFC.Automation.ObjectRelationBinder
