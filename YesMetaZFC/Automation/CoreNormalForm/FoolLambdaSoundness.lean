import YesMetaZFC.Automation.CoreNormalForm.Semantics

/-!
# FOOL 与 lambda 的语义合同

`CoreNormalForm` 的语法层允许布尔项、公式 quote、条件项和局部无名 lambda。
这些构造不能在任意 `CoreNormalForm.Semantics.Model` 上自动视为一阶等价；
本模块把所需的模型合同显式化，并提供 normalizer replay 可以复用的局部语义定理。

这里不把高阶模型强行擦除成一阶 DAG。后续 FOOL 定义化先消费这些合同，
保留的 `apply/lam` 结构直接交给原生 HO 证书后端。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm
namespace Semantics

/-- FOOL 布尔运算、公式 quote、条件项和 lambda 应满足的模型合同。 -/
structure FoolLambdaContract (M : Model) where
  function_sort :
    ∀ symbol arguments, M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)
  apply_sort :
    ∀ domain codomain functionValue argumentValue,
      M.sortInterp (.arrow domain codomain) functionValue →
        M.sortInterp domain argumentValue →
          M.sortInterp codomain (M.applyInterp functionValue argumentValue)
  bool_sort : ∀ value, M.sortInterp .bool (M.boolValue value)
  not_sort :
    ∀ value, M.sortInterp .bool value → M.sortInterp .bool (M.notValue value)
  and_sort :
    ∀ left right, M.sortInterp .bool left → M.sortInterp .bool right →
      M.sortInterp .bool (M.andValue left right)
  or_sort :
    ∀ left right, M.sortInterp .bool left → M.sortInterp .bool right →
      M.sortInterp .bool (M.orValue left right)
  imp_sort :
    ∀ left right, M.sortInterp .bool left → M.sortInterp .bool right →
      M.sortInterp .bool (M.impValue left right)
  iff_sort :
    ∀ left right, M.sortInterp .bool left → M.sortInterp .bool right →
      M.sortInterp .bool (M.iffValue left right)
  quote_sort : ∀ proposition, M.sortInterp .bool (M.quoteValue proposition)
  lambda_sort :
    ∀ domain codomain functionValue,
      (∀ value, M.sortInterp domain value → M.sortInterp codomain (functionValue value)) →
        M.sortInterp (.arrow domain codomain) (M.lambdaValue domain codomain functionValue)
  lambda_congr :
    ∀ domain codomain left right,
      (∀ value, M.sortInterp domain value → left value = right value) →
        M.lambdaValue domain codomain left = M.lambdaValue domain codomain right
  ite_sort :
    ∀ sort condition thenValue elseValue,
      M.sortInterp sort thenValue →
        M.sortInterp sort elseValue →
          M.sortInterp sort (M.iteValue condition thenValue elseValue)
  bool_holds : ∀ value : Bool, M.boolHolds (M.boolValue value) ↔ value = true
  bool_extensionality :
    ∀ left right,
      M.sortInterp .bool left →
        M.sortInterp .bool right →
          (left = right ↔ (M.boolHolds left ↔ M.boolHolds right))
  quote_eq_iff :
    ∀ left right : Prop, M.quoteValue left = M.quoteValue right ↔ (left ↔ right)
  quote_holds : ∀ proposition : Prop, M.boolHolds (M.quoteValue proposition) ↔ proposition
  not_holds : ∀ value, M.boolHolds (M.notValue value) ↔ ¬ M.boolHolds value
  and_holds :
    ∀ left right, M.boolHolds (M.andValue left right) ↔
      (M.boolHolds left ∧ M.boolHolds right)
  or_holds :
    ∀ left right, M.boolHolds (M.orValue left right) ↔
      (M.boolHolds left ∨ M.boolHolds right)
  imp_holds :
    ∀ left right, M.boolHolds (M.impValue left right) ↔
      (M.boolHolds left → M.boolHolds right)
  iff_holds :
    ∀ left right, M.boolHolds (M.iffValue left right) ↔
      (M.boolHolds left ↔ M.boolHolds right)
  ite_value :
    ∀ (condition : Prop) thenValue elseValue,
      M.iteValue condition thenValue elseValue =
        @ite M.Carrier condition (Classical.propDecidable condition) thenValue elseValue
  beta :
    ∀ (domain codomain : CoreSort) (body : M.Carrier → M.Carrier)
      (argument : M.Carrier),
      (∀ value, M.sortInterp domain value →
        M.sortInterp codomain (body value)) →
      M.sortInterp domain argument →
      M.applyInterp
          (M.lambdaValue domain codomain body)
          argument =
        body argument
  eta :
    ∀ (domain codomain : CoreSort) (functionValue : M.Carrier),
      M.sortInterp (.arrow domain codomain) functionValue →
      M.lambdaValue domain codomain (fun value => M.applyInterp functionValue value) =
        functionValue
  function_extensionality :
    ∀ (domain codomain : CoreSort) (left right : M.Carrier),
      M.sortInterp (.arrow domain codomain) left →
        M.sortInterp (.arrow domain codomain) right →
          (left = right ↔
            ∀ value, M.sortInterp domain value →
              M.applyInterp left value = M.applyInterp right value)

namespace Formula

/-- `quote φ` 作为布尔项时与原公式语义等价。 -/
theorem satisfies_boolQuote_iff {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (formula : Formula) :
    Formula.Satisfies env (.boolTerm (.quote formula)) ↔
      Formula.Satisfies env formula := by
  simp only [Formula.Satisfies, Formula.eval, Term.eval]
  exact contract.quote_holds _

/-- FOOL 否定布尔项的公式语义。 -/
theorem satisfies_boolNot_iff {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (body : Term) :
    Formula.Satisfies env (.boolTerm (.notE body)) ↔
      ¬ M.boolHolds (Term.eval env body) := by
  simp only [Formula.Satisfies, Formula.eval, Term.eval]
  exact contract.not_holds _

/-- FOOL 合取布尔项的公式语义。 -/
theorem satisfies_boolAnd_iff {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (left right : Term) :
    Formula.Satisfies env (.boolTerm (.andE left right)) ↔
      (M.boolHolds (Term.eval env left) ∧ M.boolHolds (Term.eval env right)) := by
  simp only [Formula.Satisfies, Formula.eval, Term.eval]
  exact contract.and_holds _ _

/-- FOOL 析取布尔项的公式语义。 -/
theorem satisfies_boolOr_iff {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (left right : Term) :
    Formula.Satisfies env (.boolTerm (.orE left right)) ↔
      (M.boolHolds (Term.eval env left) ∨ M.boolHolds (Term.eval env right)) := by
  simp only [Formula.Satisfies, Formula.eval, Term.eval]
  exact contract.or_holds _ _

/-- FOOL 蕴涵布尔项的公式语义。 -/
theorem satisfies_boolImp_iff {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (left right : Term) :
    Formula.Satisfies env (.boolTerm (.impE left right)) ↔
      (M.boolHolds (Term.eval env left) → M.boolHolds (Term.eval env right)) := by
  simp only [Formula.Satisfies, Formula.eval, Term.eval]
  exact contract.imp_holds _ _

/-- FOOL 等价布尔项的公式语义。 -/
theorem satisfies_boolIff_iff {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (left right : Term) :
    Formula.Satisfies env (.boolTerm (.iffE left right)) ↔
      (M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) := by
  simp only [Formula.Satisfies, Formula.eval, Term.eval]
  exact contract.iff_holds _ _

end Formula

namespace Term

/-- 条件项在合同模型中按条件选择对应分支。 -/
theorem eval_ite {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (sort : CoreSort) (condition : Formula)
    (thenTerm elseTerm : Term) :
    Term.eval env (.ite sort condition thenTerm elseTerm) =
      @ite M.Carrier (Formula.Satisfies env condition)
        (Classical.propDecidable (Formula.Satisfies env condition))
        (Term.eval env thenTerm) (Term.eval env elseTerm) := by
  simp only [Term.eval]
  exact contract.ite_value _ _ _

/-- lambda beta 在合同模型中的局部语义回放。 -/
theorem eval_beta {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (domain codomain : CoreSort) (body argument : Term)
    (hBody :
      ∀ value, M.sortInterp domain value →
        M.sortInterp codomain (Term.eval (env.push value) body))
    (hArgument : M.sortInterp domain (Term.eval env argument)) :
    Term.eval env (.apply (.lam domain codomain body) argument) =
      Term.eval (env.push (Term.eval env argument)) body := by
  simpa only [Term.eval] using
    contract.beta domain codomain
      (fun value => Term.eval (env.push value) body) (Term.eval env argument)
      hBody hArgument

/-- lambda eta 形状在合同模型中的局部语义回放。 -/
theorem eval_eta {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (domain codomain : CoreSort) (functionTerm : Term)
    (hFunction :
      M.sortInterp (.arrow domain codomain) (Term.eval env functionTerm)) :
    Term.eval env
        (.lam domain codomain
          (.apply
            (_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Term.shiftAbove
              1 0 functionTerm)
            (.bvar domain 0))) =
      Term.eval env functionTerm := by
  simp only [Term.eval]
  have hPointwise :
      (fun value =>
          M.applyInterp
            (Term.eval (env.push value)
              (_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Term.shiftAbove
                1 0 functionTerm))
            ((env.push value).boundVal 0)) =
        (fun value => M.applyInterp (Term.eval env functionTerm) value) := by
    funext value
    simp only [Env.push_bound_zero]
    rw [Term.eval_shiftAbove]
    have hEval :
        Term.eval ((env.push value).skip 1 0) functionTerm =
          Term.eval env functionTerm := by
      apply Term.eval_eq_of_env_eq
      · intro index
        have hSkip :
            ((env.push value).skip 1 0).boundVal index =
              ((env.push value).drop 1).boundVal index :=
          Env.skip_zero_bound 1 (env.push value) index
        rw [hSkip]
        simp [Env.drop, Env.push]
      · intro sort id
        rfl
    rw [hEval]
  rw [hPointwise, contract.eta domain codomain _ hFunction]

end Term

end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
