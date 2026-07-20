import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness

/-!
# 局部作用域环境语义

本模块提供 locally nameless 语法在局部 bound 支持上的环境一致性定理。公式只读取
checker 确认可见的 bound 位置；因此两个环境不必在作用域之外的 fallback 栈上相同。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm
namespace Semantics

mutual

  private theorem termWellScopedWithOfInferSortWith :
      ∀ (bound : List CoreSort) (term : Term) (sort : CoreSort),
        Term.inferSortWith bound term = some sort →
          Term.wellScopedWith bound term = true
    | bound, Term.bvar sort index, _, hSort => by
        cases hLookup : TypeCheck.lookupBound? bound index with
        | none =>
            simp [Term.inferSortWith, hLookup] at hSort
        | some expected =>
            by_cases hEqual : expected == sort
            · simp [Term.inferSortWith, hLookup] at hSort
              simp [Term.wellScopedWith, hLookup, hEqual]
            · simp [Term.inferSortWith, hLookup] at hSort
              exact (hEqual (by simp [hSort.1])).elim
    | _, Term.fvar _ _, _, _ => rfl
    | bound, Term.app symbol args, _, hSort => by
        by_cases hArity : (!symbol.arityOk || args.length != symbol.arity) = true
        · simp [Term.inferSortWith, hArity] at hSort
        · cases hArgs : Term.inferSortListWith bound args with
          | none =>
              simp [Term.inferSortWith, hArity, hArgs] at hSort
          | some sorts =>
              have hScoped :=
                termListWellScopedWithOfInferSortListWith bound args sorts hArgs
              have hConditions :
                  symbol.arityOk = true ∧ args.length = symbol.arity := by
                have hFalse :
                    (!symbol.arityOk || args.length != symbol.arity) = false := by
                  cases hValue :
                      (!symbol.arityOk || args.length != symbol.arity) <;>
                    simp_all
                simpa using hFalse
              rcases hConditions with ⟨hArityOk, hLength⟩
              simp [Term.wellScopedWith, hArityOk, hLength, hScoped]
    | bound, Term.apply fn arg, _, hSort => by
        rcases Term.inferSortWith_apply_parts hSort with ⟨domain, hFn, hArg⟩
        simp [Term.wellScopedWith,
          termWellScopedWithOfInferSortWith bound fn (.arrow domain _) hFn,
          termWellScopedWithOfInferSortWith bound arg domain hArg]
    | _, Term.bool _, _, _ => rfl
    | bound, Term.notE body, _, hSort => by
        rcases Term.inferSortWith_notE_parts hSort with ⟨_, hBody⟩
        simpa [Term.wellScopedWith] using
          termWellScopedWithOfInferSortWith bound body .bool hBody
    | bound, Term.andE left right, _, hSort => by
        rcases Term.inferSortWith_andE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith,
          termWellScopedWithOfInferSortWith bound left .bool hLeft,
          termWellScopedWithOfInferSortWith bound right .bool hRight]
    | bound, Term.orE left right, _, hSort => by
        rcases Term.inferSortWith_orE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith,
          termWellScopedWithOfInferSortWith bound left .bool hLeft,
          termWellScopedWithOfInferSortWith bound right .bool hRight]
    | bound, Term.impE left right, _, hSort => by
        rcases Term.inferSortWith_impE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith,
          termWellScopedWithOfInferSortWith bound left .bool hLeft,
          termWellScopedWithOfInferSortWith bound right .bool hRight]
    | bound, Term.iffE left right, _, hSort => by
        rcases Term.inferSortWith_iffE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith,
          termWellScopedWithOfInferSortWith bound left .bool hLeft,
          termWellScopedWithOfInferSortWith bound right .bool hRight]
    | bound, Term.quote formula, _, hSort => by
        rcases Term.inferSortWith_quote_parts hSort with ⟨_, hFormula⟩
        simpa [Term.wellScopedWith] using
          formulaWellScopedWithOfCheckWith bound formula hFormula
    | bound, Term.lam domain _ body, _, hSort => by
        rcases Term.inferSortWith_lam_parts hSort with ⟨_, hBody⟩
        simpa [Term.wellScopedWith] using
          termWellScopedWithOfInferSortWith (domain :: bound) body _ hBody
    | bound, Term.ite _ condition thenTerm elseTerm, _, hSort => by
        rcases Term.inferSortWith_ite_parts hSort with
          ⟨_, hCondition, hThen, hElse⟩
        simp [Term.wellScopedWith,
          formulaWellScopedWithOfCheckWith bound condition hCondition,
          termWellScopedWithOfInferSortWith bound thenTerm _ hThen,
          termWellScopedWithOfInferSortWith bound elseTerm _ hElse]

  private theorem formulaWellScopedWithOfCheckWith :
      ∀ (bound : List CoreSort) (formula : Formula),
        Formula.checkWith bound formula = true →
          Formula.wellScopedWith bound formula = true
    | _, Formula.trueE, _ => rfl
    | _, Formula.falseE, _ => rfl
    | bound, Formula.atom predicate args, hCheck => by
        rcases Formula.inferSortListWith_of_check_atom hCheck with ⟨sorts, hArgs⟩
        have hScoped :=
          termListWellScopedWithOfInferSortListWith bound args sorts hArgs
        by_cases hArity :
            (!predicate.arityOk || args.length != predicate.arity) = true
        · simp [Formula.checkWith, hArity] at hCheck
        · have hConditions :
              predicate.arityOk = true ∧ args.length = predicate.arity := by
            have hFalse :
                (!predicate.arityOk || args.length != predicate.arity) = false := by
              cases hValue :
                  (!predicate.arityOk || args.length != predicate.arity) <;>
                simp_all
            simpa using hFalse
          rcases hConditions with ⟨hArityOk, hLength⟩
          simp [Formula.wellScopedWith, hArityOk, hLength, hScoped]
    | bound, Formula.equal _ left right, hCheck => by
        rcases Formula.inferSortWith_of_check_equal hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith,
          termWellScopedWithOfInferSortWith bound left _ hLeft,
          termWellScopedWithOfInferSortWith bound right _ hRight]
    | bound, Formula.boolTerm term, hCheck => by
        have hTerm := Formula.inferSortWith_of_check_boolTerm hCheck
        simpa [Formula.wellScopedWith] using
          termWellScopedWithOfInferSortWith bound term .bool hTerm
    | bound, Formula.neg body, hCheck => by
        simpa [Formula.wellScopedWith] using
          formulaWellScopedWithOfCheckWith bound body
            (Formula.checkWith_of_check_neg hCheck)
    | bound, Formula.imp left right, hCheck => by
        rcases Formula.checkWith_of_check_imp hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith,
          formulaWellScopedWithOfCheckWith bound left hLeft,
          formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.conj left right, hCheck => by
        rcases Formula.checkWith_of_check_conj hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith,
          formulaWellScopedWithOfCheckWith bound left hLeft,
          formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.disj left right, hCheck => by
        rcases Formula.checkWith_of_check_disj hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith,
          formulaWellScopedWithOfCheckWith bound left hLeft,
          formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.iffE left right, hCheck => by
        rcases Formula.checkWith_of_check_iffE hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith,
          formulaWellScopedWithOfCheckWith bound left hLeft,
          formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.forallE sort body, hCheck => by
        simpa [Formula.wellScopedWith] using
          formulaWellScopedWithOfCheckWith (sort :: bound) body
            (Formula.checkWith_of_check_forallE hCheck)
    | bound, Formula.existsE sort body, hCheck => by
        simpa [Formula.wellScopedWith] using
          formulaWellScopedWithOfCheckWith (sort :: bound) body
            (Formula.checkWith_of_check_existsE hCheck)

  private theorem termListWellScopedWithOfInferSortListWith :
      ∀ (bound : List CoreSort) (terms : List Term) (sorts : List CoreSort),
        Term.inferSortListWith bound terms = some sorts →
          Term.wellScopedListWith bound terms = true
    | _, [], _, hSorts => by
        simp [Term.inferSortListWith] at hSorts
        rfl
    | bound, term :: rest, sorts, hSorts => by
        rcases Term.inferSortListWith_cons_parts hSorts with
          ⟨sort, restSorts, _, hTerm, hRest⟩
        simp [Term.wellScopedListWith,
          termWellScopedWithOfInferSortWith bound term sort hTerm,
          termListWellScopedWithOfInferSortListWith bound rest restSorts hRest]

end

namespace Formula

/-- checker 接受的公式只读取当前 locally nameless 上下文中的 bound 位置。 -/
theorem wellScopedWith_of_checkWith_support
    (bound : List CoreSort) (formula : Formula)
    (hCheck : Formula.checkWith bound formula = true) :
    Formula.wellScopedWith bound formula = true :=
  formulaWellScopedWithOfCheckWith bound formula hCheck

end Formula

namespace Env

/-- 两个环境在局部 bound 支持上相同，并且拥有相同的完整 free 赋值。 -/
def ScopedSupportAgreement {M : Model}
    (bound : List CoreSort) (left right : Env M) : Prop :=
  (∀ sort index, TypeCheck.lookupBound? bound index = some sort →
      left.boundVal index = right.boundVal index) ∧
    ∀ sort id, left.freeVal sort id = right.freeVal sort id

theorem scopedSupportAgreement_push {M : Model}
    {bound : List CoreSort} {left right : Env M}
    (hAgreement : ScopedSupportAgreement bound left right)
    (sort : CoreSort) (value : M.Carrier) :
    ScopedSupportAgreement (sort :: bound) (left.push value) (right.push value) := by
  constructor
  · intro target index hLookup
    cases index with
    | zero =>
        rfl
    | succ previous =>
        simp only [TypeCheck.lookupBound?] at hLookup
        simpa only [push_bound_succ] using hAgreement.1 target previous hLookup
  · intro target id
    exact hAgreement.2 target id

end Env

mutual

theorem Term.eval_eq_of_scopedSupportAgreement
    {M : Model} (bound : List CoreSort) (left right : Env M)
    (hAgreement : Env.ScopedSupportAgreement bound left right)
    (term : Term) (hScoped : Term.wellScopedWith bound term = true) :
    Term.eval left term = Term.eval right term := by
  cases term with
  | bvar sort index =>
      cases hLookup : TypeCheck.lookupBound? bound index with
      | none =>
          simp [Term.wellScopedWith, hLookup] at hScoped
      | some expected =>
          have hSort : expected = sort := by
            simpa [Term.wellScopedWith, hLookup, beq_iff_eq] using hScoped
          subst expected
          simpa only [Term.eval] using hAgreement.1 sort index hLookup
  | fvar sort id =>
      simpa only [Term.eval] using hAgreement.2 sort id
  | app symbol args =>
      unfold Term.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      unfold Term.eval
      congr 1
      exact Term.evalList_eq_of_scopedSupportAgreement
        bound left right hAgreement args hScoped.2
  | apply fn arg =>
      unfold Term.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      unfold Term.eval
      rw [Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement fn hScoped.1,
        Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement arg hScoped.2]
  | bool value =>
      unfold Term.eval
      rfl
  | notE body =>
      unfold Term.wellScopedWith at hScoped
      unfold Term.eval
      rw [Term.eval_eq_of_scopedSupportAgreement
        bound left right hAgreement body hScoped]
  | andE leftTerm rightTerm
  | orE leftTerm rightTerm
  | impE leftTerm rightTerm
  | iffE leftTerm rightTerm =>
      unfold Term.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      unfold Term.eval
      rw [Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement leftTerm hScoped.1,
        Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement rightTerm hScoped.2]
  | quote formula =>
      unfold Term.wellScopedWith at hScoped
      unfold Term.eval
      congr 1
      apply propext
      exact Formula.satisfies_iff_of_scopedSupportAgreement
        bound left right hAgreement formula hScoped
  | lam domain codomain body =>
      unfold Term.wellScopedWith at hScoped
      unfold Term.eval
      congr 1
      funext value
      exact Term.eval_eq_of_scopedSupportAgreement
        (domain :: bound) (left.push value) (right.push value)
        (Env.scopedSupportAgreement_push hAgreement domain value) body hScoped
  | ite sort condition thenTerm elseTerm =>
      unfold Term.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      unfold Term.eval
      congr 1
      · apply propext
        exact Formula.satisfies_iff_of_scopedSupportAgreement
          bound left right hAgreement condition hScoped.1.1
      · exact Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement thenTerm hScoped.1.2
      · exact Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement elseTerm hScoped.2

theorem Formula.satisfies_iff_of_scopedSupportAgreement
    {M : Model} (bound : List CoreSort) (left right : Env M)
    (hAgreement : Env.ScopedSupportAgreement bound left right)
    (formula : Formula) (hScoped : Formula.wellScopedWith bound formula = true) :
    Formula.Satisfies left formula ↔ Formula.Satisfies right formula := by
  cases formula with
  | trueE
  | falseE =>
      simp [Formula.Satisfies, Formula.eval]
  | atom predicate args =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.evalList_eq_of_scopedSupportAgreement
        bound left right hAgreement args hScoped.2]
  | equal sort leftTerm rightTerm =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement leftTerm hScoped.1,
        Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement rightTerm hScoped.2]
  | boolTerm term =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_eq_of_scopedSupportAgreement
        bound left right hAgreement term hScoped]
  | neg body =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      exact not_congr
        (Formula.satisfies_iff_of_scopedSupportAgreement
          bound left right hAgreement body hScoped)
  | imp leftFormula rightFormula
  | conj leftFormula rightFormula
  | disj leftFormula rightFormula
  | iffE leftFormula rightFormula =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      first
      | exact imp_congr
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement rightFormula hScoped.2)
      | exact and_congr
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement rightFormula hScoped.2)
      | exact or_congr
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement rightFormula hScoped.2)
      | exact iff_congr
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedSupportAgreement
            bound left right hAgreement rightFormula hScoped.2)
  | forallE sort body =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      constructor <;> intro h value hSort
      · exact (Formula.satisfies_iff_of_scopedSupportAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedSupportAgreement_push hAgreement sort value)
            body hScoped).mp (h value hSort)
      · exact (Formula.satisfies_iff_of_scopedSupportAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedSupportAgreement_push hAgreement sort value)
            body hScoped).mpr (h value hSort)
  | existsE sort body =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      constructor
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_iff_of_scopedSupportAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedSupportAgreement_push hAgreement sort value)
            body hScoped).mp hBody
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_iff_of_scopedSupportAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedSupportAgreement_push hAgreement sort value)
            body hScoped).mpr hBody

theorem Term.evalList_eq_of_scopedSupportAgreement
    {M : Model} (bound : List CoreSort) (left right : Env M)
    (hAgreement : Env.ScopedSupportAgreement bound left right)
    (terms : List Term)
    (hScoped : Term.wellScopedListWith bound terms = true) :
    terms.map (Term.eval left) = terms.map (Term.eval right) := by
  cases terms with
  | nil =>
      rfl
  | cons head tail =>
      unfold Term.wellScopedListWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      simp only [List.map_cons]
      congr 1
      · exact Term.eval_eq_of_scopedSupportAgreement
          bound left right hAgreement head hScoped.1
      · exact Term.evalList_eq_of_scopedSupportAgreement
          bound left right hAgreement tail hScoped.2

end

end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
