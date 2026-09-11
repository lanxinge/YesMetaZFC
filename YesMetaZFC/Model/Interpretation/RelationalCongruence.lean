import YesMetaZFC.Model.Interpretation.RelationalDefinitions

/-! # 关系翻译对已覆盖符号的同余

按源语法归纳比较解释，不展开各符号的大型目标图。未出现在正文中的解释字段
可以不同；类型映射保持相同。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
variable {σ τ : Signature.{0,0,0}}
variable (I : Interpretation σ τ)
variable (functions : (symbol : σ.FuncSymbol) → Formula τ [] (I.sort (σ.funcCodomain symbol) :: (σ.funcDomain symbol).map I.sort))
variable (relations : (symbol : σ.RelSymbol) → Formula τ [] ((σ.relDomain symbol).map I.sort))
variable (fc : σ.FuncSymbol → Bool) (rc : σ.RelSymbol → Bool)
variable (hFunctions : ∀ symbol, fc symbol = true → functions symbol = I.function symbol)
variable (hRelations : ∀ symbol, rc symbol = true → relations symbol = I.relation symbol)

abbrev regraph : Interpretation σ τ := { I with function := functions, relation := relations }

mutual
theorem term_congr (hFunctions : ∀ symbol, fc symbol = true → functions symbol = I.function symbol) {sb sf : SortContext σ} {bound free : SortContext τ} {sort : σ.SortSymbol}
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (input : Term σ sb sf sort) (output : Term τ bound free (I.sort sort))
    (hCovered : termCovered fc input = true) :
    term (regraph I functions relations) bs fs input output = term I bs fs input output := by
  cases input with
  | bvar entry => rfl
  | fvar entry => rfl
  | app symbol args =>
    have h := Bool.and_eq_true_iff.mp hCovered
    simp only [term]
    rw [hFunctions symbol h.1,arguments_congr hFunctions _ _ args _ h.2]
    all_goals rfl


theorem arguments_congr (hFunctions : ∀ symbol, fc symbol = true → functions symbol = I.function symbol) {sb sf : SortContext σ} {bound free : SortContext τ} {sorts : SortContext σ}
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (input : Arguments σ sb sf sorts) (output : Arguments τ bound free (sorts.map I.sort))
    (hCovered : argumentsCovered fc input = true) :
    arguments (regraph I functions relations) bs fs input output = arguments I bs fs input output := by
  cases input with
  | nil => cases output; rfl
  | cons head tail =>
    cases output with
    | cons first rest =>
      have h := Bool.and_eq_true_iff.mp hCovered
      simp only [arguments]
      rw [term_congr hFunctions _ _ head _ h.1,
        arguments_congr hFunctions _ _ tail _ h.2]
      all_goals rfl
end

include hFunctions hRelations
theorem formula_congr {sb sf : SortContext σ} {bound free : SortContext τ}
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (input : Formula σ sb sf) (hCovered : formulaCovered fc rc input = true) :
    formula (regraph I functions relations) bs fs input = formula I bs fs input := by
  induction input generalizing bound with
  | falsum => rfl
  | truth => rfl
  | rel symbol args =>
    have h := Bool.and_eq_true_iff.mp hCovered
    simp only [formula]
    rw [hRelations symbol h.1,arguments_congr I functions relations fc hFunctions _ _ args _ h.2]
    all_goals rfl
  | equal left right =>
    have h := Bool.and_eq_true_iff.mp hCovered
    simp only [formula]
    rw [term_congr I functions relations fc hFunctions _ _ left _ h.1,
      term_congr I functions relations fc hFunctions _ _ right _ h.2]
    all_goals rfl
  | neg body ih => exact congrArg Formula.neg (ih _ _ hCovered)
  | conj left right ihLeft ihRight =>
    simp only [formula]
    rw [ihLeft _ _ (Bool.and_eq_true_iff.mp hCovered).1,ihRight _ _ (Bool.and_eq_true_iff.mp hCovered).2]
  | disj left right ihLeft ihRight =>
    simp only [formula]
    rw [ihLeft _ _ (Bool.and_eq_true_iff.mp hCovered).1,ihRight _ _ (Bool.and_eq_true_iff.mp hCovered).2]
  | imp left right ihLeft ihRight =>
    simp only [formula]
    rw [ihLeft _ _ (Bool.and_eq_true_iff.mp hCovered).1,ihRight _ _ (Bool.and_eq_true_iff.mp hCovered).2]
  | iff left right ihLeft ihRight =>
    simp only [formula]
    rw [ihLeft _ _ (Bool.and_eq_true_iff.mp hCovered).1,ihRight _ _ (Bool.and_eq_true_iff.mp hCovered).2]
  | forallE sort body ih => exact congrArg (Formula.forallE (I.sort sort)) (ih _ _ hCovered)
  | existsE sort body ih => exact congrArg (Formula.existsE (I.sort sort)) (ih _ _ hCovered)

omit hFunctions hRelations
theorem mapVariable_regraph {sorts : SortContext σ} {sort : σ.SortSymbol} (entry : Variable sorts sort) :
    mapVariable (regraph I functions relations) entry = mapVariable I entry := by
  induction entry with
  | here => rfl
  | there previous ih => exact congrArg Variable.there ih

include hFunctions hRelations
theorem openFormula_congr {free : SortContext σ} (input : Formula σ [] free)
    (hCovered : formulaCovered fc rc input = true) :
    openFormula (regraph I functions relations) input = openFormula I input := by
  unfold openFormula
  simp only [mapVariable_regraph]
  exact formula_congr I functions relations fc rc hFunctions hRelations _ _ input hCovered
end YesMetaZFC.Automation.RelationalTranslation
