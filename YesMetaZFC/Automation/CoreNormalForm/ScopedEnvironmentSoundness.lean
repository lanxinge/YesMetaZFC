import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness
/-!
# 局部作用域环境语义
本模块提供 locally nameless 语法在局部 bound 支持上的环境一致性定理。公式只读取
checker 确认可见的 bound 位置；因此两个环境不必在作用域之外的 fallback 栈上相同。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
mutual
  private theorem termWellScopedWithOfInferSortWith : ∀ (bound : List CoreSort) (term : Term) (sort : CoreSort), Term.inferSortWith bound term = some sort → Term.wellScopedWith bound term = true
    | bound, Term.bvar sort index, _, hSort => by
        cases hLookup : TypeCheck.lookupBound? bound index with
        | none => simp [Term.inferSortWith, hLookup] at hSort
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
          | none => simp [Term.inferSortWith, hArity, hArgs] at hSort
          | some sorts =>
              have hScoped :=
                termListWellScopedWithOfInferSortListWith bound args sorts hArgs
              have hConditions :
                  symbol.arityOk = true ∧ args.length = symbol.arity := by
                have hFalse : (!symbol.arityOk || args.length != symbol.arity) = false := by
                  cases hValue : (!symbol.arityOk || args.length != symbol.arity) <;>
                    simp_all
                simpa using hFalse
              rcases hConditions with ⟨hArityOk, hLength⟩
              simp [Term.wellScopedWith, hArityOk, hLength, hScoped]
    | bound, Term.apply fn arg, _, hSort => by
        rcases Term.inferSortWith_apply_parts hSort with ⟨domain, hFn, hArg⟩
        simp [Term.wellScopedWith, termWellScopedWithOfInferSortWith bound fn (.arrow domain _) hFn, termWellScopedWithOfInferSortWith bound arg domain hArg]
    | _, Term.bool _, _, _ => rfl
    | bound, Term.notE body, _, hSort => by
        rcases Term.inferSortWith_notE_parts hSort with ⟨_, hBody⟩
        simpa [Term.wellScopedWith] using
          termWellScopedWithOfInferSortWith bound body .bool hBody
    | bound, Term.andE left right, _, hSort => by
        rcases Term.inferSortWith_andE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith, termWellScopedWithOfInferSortWith bound left .bool hLeft, termWellScopedWithOfInferSortWith bound right .bool hRight]
    | bound, Term.orE left right, _, hSort => by
        rcases Term.inferSortWith_orE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith, termWellScopedWithOfInferSortWith bound left .bool hLeft, termWellScopedWithOfInferSortWith bound right .bool hRight]
    | bound, Term.impE left right, _, hSort => by
        rcases Term.inferSortWith_impE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith, termWellScopedWithOfInferSortWith bound left .bool hLeft, termWellScopedWithOfInferSortWith bound right .bool hRight]
    | bound, Term.iffE left right, _, hSort => by
        rcases Term.inferSortWith_iffE_parts hSort with ⟨_, hLeft, hRight⟩
        simp [Term.wellScopedWith, termWellScopedWithOfInferSortWith bound left .bool hLeft, termWellScopedWithOfInferSortWith bound right .bool hRight]
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
        simp [Term.wellScopedWith, formulaWellScopedWithOfCheckWith bound condition hCondition, termWellScopedWithOfInferSortWith bound thenTerm _ hThen,
          termWellScopedWithOfInferSortWith bound elseTerm _ hElse]
  private theorem formulaWellScopedWithOfCheckWith : ∀ (bound : List CoreSort) (formula : Formula), Formula.checkWith bound formula = true → Formula.wellScopedWith bound formula = true
    | _, Formula.trueE, _ => rfl
    | _, Formula.falseE, _ => rfl
    | bound, Formula.atom predicate args, hCheck => by
        rcases Formula.inferSortListWith_of_check_atom hCheck with ⟨sorts, hArgs⟩
        have hScoped :=
          termListWellScopedWithOfInferSortListWith bound args sorts hArgs
        by_cases hArity : (!predicate.arityOk || args.length != predicate.arity) = true
        · simp [Formula.checkWith, hArity] at hCheck
        · have hConditions :
              predicate.arityOk = true ∧ args.length = predicate.arity := by
            have hFalse : (!predicate.arityOk || args.length != predicate.arity) = false := by
              cases hValue : (!predicate.arityOk || args.length != predicate.arity) <;>
                simp_all
            simpa using hFalse
          rcases hConditions with ⟨hArityOk, hLength⟩
          simp [Formula.wellScopedWith, hArityOk, hLength, hScoped]
    | bound, Formula.equal _ left right, hCheck => by
        rcases Formula.inferSortWith_of_check_equal hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith, termWellScopedWithOfInferSortWith bound left _ hLeft, termWellScopedWithOfInferSortWith bound right _ hRight]
    | bound, Formula.boolTerm term, hCheck => by
        have hTerm := Formula.inferSortWith_of_check_boolTerm hCheck
        simpa [Formula.wellScopedWith] using
          termWellScopedWithOfInferSortWith bound term .bool hTerm
    | bound, Formula.neg body, hCheck => by
        simpa [Formula.wellScopedWith] using
          formulaWellScopedWithOfCheckWith bound body (Formula.checkWith_of_check_neg hCheck)
    | bound, Formula.imp left right, hCheck => by
        rcases Formula.checkWith_of_check_imp hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith, formulaWellScopedWithOfCheckWith bound left hLeft, formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.conj left right, hCheck => by
        rcases Formula.checkWith_of_check_conj hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith, formulaWellScopedWithOfCheckWith bound left hLeft, formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.disj left right, hCheck => by
        rcases Formula.checkWith_of_check_disj hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith, formulaWellScopedWithOfCheckWith bound left hLeft, formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.iffE left right, hCheck => by
        rcases Formula.checkWith_of_check_iffE hCheck with ⟨hLeft, hRight⟩
        simp [Formula.wellScopedWith, formulaWellScopedWithOfCheckWith bound left hLeft, formulaWellScopedWithOfCheckWith bound right hRight]
    | bound, Formula.forallE sort body, hCheck => by
        simpa [Formula.wellScopedWith] using
          formulaWellScopedWithOfCheckWith (sort :: bound) body (Formula.checkWith_of_check_forallE hCheck)
    | bound, Formula.existsE sort body, hCheck => by
        simpa [Formula.wellScopedWith] using
          formulaWellScopedWithOfCheckWith (sort :: bound) body (Formula.checkWith_of_check_existsE hCheck)
  private theorem termListWellScopedWithOfInferSortListWith : ∀ (bound : List CoreSort) (terms : List Term) (sorts : List CoreSort), Term.inferSortListWith bound terms = some sorts → Term.wellScopedListWith bound terms = true
    | _, [], _, hSorts => by
        simp [Term.inferSortListWith] at hSorts
        rfl
    | bound, term :: rest, sorts, hSorts => by
        rcases Term.inferSortListWith_cons_parts hSorts with
          ⟨sort, restSorts, _, hTerm, hRest⟩
        simp [Term.wellScopedListWith, termWellScopedWithOfInferSortWith bound term sort hTerm, termListWellScopedWithOfInferSortListWith bound rest restSorts hRest]
end
namespace Formula
theorem wellScopedWith_of_checkWith_support (bound : List CoreSort) (formula : Formula) (hCheck : Formula.checkWith bound formula = true) : Formula.wellScopedWith bound formula = true :=
  formulaWellScopedWithOfCheckWith bound formula hCheck
end Formula
namespace Env
def ScopedSupportAgreement {M : Model} (bound : List CoreSort) (left right : Env M) : Prop :=
  (∀ sort index, TypeCheck.lookupBound? bound index = some sort → left.boundVal index = right.boundVal index) ∧
    ∀ sort id, left.freeVal sort id = right.freeVal sort id
theorem scopedSupportAgreement_push {M : Model} {bound : List CoreSort} {left right : Env M} (hAgreement : ScopedSupportAgreement bound left right) (sort : CoreSort) (value : M.Carrier) : ScopedSupportAgreement (sort :: bound) (left.push value) (right.push value) := by
  constructor
  · intro target index hLookup
    cases index with
    | zero => rfl
    | succ previous =>
        simp only [TypeCheck.lookupBound?] at hLookup
        simpa only [push_bound_succ] using hAgreement.1 target previous hLookup
  · intro target id
    exact hAgreement.2 target id
end Env
mutual
theorem Term.eval_eq_of_scopedSupportAgreement {M : Model} (bound : List CoreSort) (left right : Env M) (hAgreement : Env.ScopedSupportAgreement bound left right) (term : Term) (hScoped : Term.wellScopedWith bound term = true) : Term.eval left term = Term.eval right term := by
  cases term
  case bvar sort index =>
    cases hLookup : TypeCheck.lookupBound? bound index with
    | none => simp [Term.wellScopedWith, hLookup] at hScoped
    | some expected =>
        have hSort : expected = sort := by
          simpa [Term.wellScopedWith, hLookup, beq_iff_eq] using hScoped
        subst expected
        simpa only [Term.eval] using hAgreement.1 sort index hLookup
  case lam domain codomain body =>
    simp only [Term.eval]
    congr 1
    funext value
    exact Term.eval_eq_of_scopedSupportAgreement (domain :: bound) (left.push value)
      (right.push value) (Env.scopedSupportAgreement_push hAgreement domain value) body hScoped
  all_goals simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
  all_goals simp only [Term.eval]
  all_goals simp_all only [← Formula.Satisfies.eq_def, hAgreement.2,
      Term.eval_eq_of_scopedSupportAgreement bound left right hAgreement,
      Formula.satisfies_iff_of_scopedSupportAgreement bound left right hAgreement,
      Term.evalList_eq_of_scopedSupportAgreement bound left right hAgreement]

theorem Formula.satisfies_iff_of_scopedSupportAgreement {M : Model} (bound : List CoreSort) (left right : Env M) (hAgreement : Env.ScopedSupportAgreement bound left right) (formula : Formula) (hScoped : Formula.wellScopedWith bound formula = true) : Formula.Satisfies left formula ↔ Formula.Satisfies right formula := by
  cases formula <;> simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
  case forallE sort body | existsE sort body =>
    simp only [Formula.Satisfies, Formula.eval]
    simp only [← Formula.Satisfies.eq_def,
      Formula.satisfies_iff_of_scopedSupportAgreement (sort :: bound) (left.push _)
        (right.push _) (Env.scopedSupportAgreement_push hAgreement sort _) body hScoped]
  all_goals simp only [Formula.Satisfies, Formula.eval]
  all_goals simp_all only [← Formula.Satisfies.eq_def,
      Term.eval_eq_of_scopedSupportAgreement bound left right hAgreement,
      Formula.satisfies_iff_of_scopedSupportAgreement bound left right hAgreement,
      Term.evalList_eq_of_scopedSupportAgreement bound left right hAgreement]

theorem Term.evalList_eq_of_scopedSupportAgreement {M : Model} (bound : List CoreSort) (left right : Env M) (hAgreement : Env.ScopedSupportAgreement bound left right) (terms : List Term) (hScoped : Term.wellScopedListWith bound terms = true) : terms.map (Term.eval left) = terms.map (Term.eval right) := by
  cases terms <;> simp only [Term.wellScopedListWith, Bool.and_eq_true] at hScoped
  all_goals simp_all only [List.map_nil, List.map_cons,
      Term.eval_eq_of_scopedSupportAgreement bound left right hAgreement,
      Term.evalList_eq_of_scopedSupportAgreement bound left right hAgreement]


end
end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
