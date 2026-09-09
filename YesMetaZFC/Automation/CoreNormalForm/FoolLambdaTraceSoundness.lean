import YesMetaZFC.Automation.CoreNormalForm.ContextualRewriteSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaSoundness
/-!
# FOOL / lambda normalization trace soundness
本模块证明 `CoreNormalForm` 可计算 trace 的逐步语义保持。项级 FOOL 化简需要先
知道被化简项确实位于布尔 sort，因此这里同时建立 locally nameless 环境与
`inferSortWith` 的类型语义不变量。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
universe x
namespace Term
theorem eval_mem_of_inferSortWith {M : Model} (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) : ∀ (term : Term) (sort : CoreSort), Term.inferSortWith bound term = some sort → M.sortInterp sort (Term.eval env term) := by
  intro term sort hSort
  exact eval_mem_of_inferSortWith_fragment contract.toFoolContract contract.higherOrderTyping
    bound env hBound hFree term sort (Or.inl True.intro) hSort
end Term
namespace Term
theorem eval_eq_of_bool_holds_iff {M : Model} (contract : FoolLambdaContract M) (env : Env M) (left right : Term) (hLeft : M.sortInterp .bool (Term.eval env left)) (hRight : M.sortInterp .bool (Term.eval env right)) (hHolds : M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) : SemanticallyEqual env left right :=
  (contract.bool_extensionality _ _ hLeft hRight).mpr hHolds
theorem eval_eq_of_inferred_bool_holds_iff {M : Model} (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (left right : Term) (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) (hHolds : M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) : SemanticallyEqual env left right :=
  eval_eq_of_bool_holds_iff contract env left right (eval_mem_of_inferSortWith contract bound env hBound hFree left .bool hLeft)
    (eval_mem_of_inferSortWith contract bound env hBound hFree right .bool hRight)
    hHolds
theorem eval_beta_instantiate {M : Model} (contract : FoolLambdaContract M) (env : Env M) (domain codomain : CoreSort) (body argument : Term) (hBody : ∀ value, M.sortInterp domain value → M.sortInterp codomain (Term.eval (env.push value) body)) (hArgument : M.sortInterp domain (Term.eval env argument)) : Term.eval env (.apply (.lam domain codomain body) argument) = Term.eval env (Term.instantiate argument body) := by
  rw [Term.eval_beta contract env domain codomain body argument hBody hArgument]
  simp only [Term.instantiate, Term.eval_instantiateAt]
  rw [Env.drop_zero_eq]
  rw [Env.insertAt_zero_eq_push]
mutual
  theorem etaTerm_occursBVarAt_eq (depth : Nat) (term : Term) : Eta.Term.occursBVarAt depth term = Term.occursBVarAt depth term := by
    cases term <;>
      simp [Eta.Term.occursBVarAt, Term.occursBVarAt, etaTerm_occursBVarAt_eq, etaFormula_occursBVarAt_eq, etaTerm_occursBVarListAt_eq]
  theorem etaFormula_occursBVarAt_eq (depth : Nat) (formula : Formula) : Eta.Formula.occursBVarAt depth formula = Formula.occursBVarAt depth formula := by
    cases formula <;>
      simp [Eta.Formula.occursBVarAt, Formula.occursBVarAt, etaTerm_occursBVarAt_eq, etaFormula_occursBVarAt_eq, etaTerm_occursBVarListAt_eq]
  theorem etaTerm_occursBVarListAt_eq (depth : Nat) (terms : List Term) : Eta.Term.occursBVarListAt depth terms = Term.occursBVarListAt depth terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp [Eta.Term.occursBVarListAt, Term.occursBVarListAt, etaTerm_occursBVarAt_eq, etaTerm_occursBVarListAt_eq]
end
mutual
  theorem etaTerm_lowerAbove_eq (cutoff : Nat) (term : Term) : Eta.Term.lowerAbove cutoff term = Term.lowerAbove cutoff term := by
    cases term <;>
      simp [Eta.Term.lowerAbove, Term.lowerAbove, etaTerm_lowerAbove_eq, etaFormula_lowerAbove_eq, etaTerm_lowerListAbove_eq]
  theorem etaFormula_lowerAbove_eq (cutoff : Nat) (formula : Formula) : Eta.Formula.lowerAbove cutoff formula = Formula.lowerAbove cutoff formula := by
    cases formula <;>
      simp [Eta.Formula.lowerAbove, Formula.lowerAbove, etaTerm_lowerAbove_eq, etaFormula_lowerAbove_eq, etaTerm_lowerListAbove_eq]
  theorem etaTerm_lowerListAbove_eq (cutoff : Nat) (terms : List Term) : Eta.Term.lowerListAbove cutoff terms = Term.lowerListAbove cutoff terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
        simp [Eta.Term.lowerListAbove, Term.lowerListAbove, etaTerm_lowerAbove_eq, etaTerm_lowerListAbove_eq]
end
theorem eval_eta_contract? {M : Model} (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (domain codomain : CoreSort) (body contracted : Term) (hBodySort : Term.inferSortWith (domain :: bound) body = some codomain) (hContract : Eta.contract? domain body = some contracted) : Term.eval env (.lam domain codomain body) = Term.eval env contracted := by
  cases body with
  | apply fn argument =>
      cases argument with
      | bvar argumentSort index =>
          cases index with
          | zero =>
              simp only [Eta.contract?] at hContract
              split at hContract
              next hGuard =>
                simp only [Option.some.injEq] at hContract
                subst contracted
                simp only [Bool.and_eq_true] at hGuard
                have hArgumentSort : argumentSort = domain :=
                  coreSort_eq_of_beq_eq_true hGuard.1
                subst argumentSort
                have hEtaOccurs : Eta.Term.occursBVarAt 0 fn = false := (Bool.not_eq_true' _).mp hGuard.2
                have hOccurs : Term.occursBVarAt 0 fn = false := by
                  rw [← etaTerm_occursBVarAt_eq]
                  exact hEtaOccurs
                obtain ⟨functionDomain, hFnSort, hArgumentSort⟩ :=
                  inferSortWith_apply_parts hBodySort
                simp [Term.inferSortWith, TypeCheck.lookupBound?] at hArgumentSort
                have hFunctionDomain : functionDomain = domain := by exact hArgumentSort.symm
                subst functionDomain
                let witness := Classical.choose (M.sortNonempty domain)
                have hWitness : M.sortInterp domain witness :=
                  Classical.choose_spec (M.sortNonempty domain)
                have hFnSemantic :
                    M.sortInterp (.arrow domain codomain) (Term.eval (env.push witness) fn) :=
                  eval_mem_of_inferSortWith contract (domain :: bound) (env.push witness) (Env.respectsBound_push hBound hWitness)
                    (Env.respectsFree_push hFree witness)
                    fn (.arrow domain codomain) hFnSort
                have hFnEval :
                    Term.eval (env.push witness) fn =
                      Term.eval env (Term.lowerAbove 0 fn) := by
                  rw [← Env.insertAt_zero_eq_push env witness]
                  rw [← Term.eval_lowerAbove_of_not_occurs env 0 witness fn hOccurs]
                have hContractedSort :
                    M.sortInterp (.arrow domain codomain) (Term.eval env (Term.lowerAbove 0 fn)) := by
                  rw [← hFnEval]
                  exact hFnSemantic
                simp only [Term.eval]
                have hFunction : (fun value => M.applyInterp (Term.eval (env.push value) fn) value) =
                      (fun value => M.applyInterp (Term.eval env (Term.lowerAbove 0 fn)) value) := by
                  funext value
                  rw [← Env.insertAt_zero_eq_push env value]
                  rw [← Term.eval_lowerAbove_of_not_occurs env 0 value fn hOccurs]
                simp only [Env.push_bound_zero]
                rw [hFunction, contract.eta domain codomain _ hContractedSort, etaTerm_lowerAbove_eq]
              next =>
                simp at hContract
          | succ index => simp [Eta.contract?] at hContract
      | _ => simp [Eta.contract?] at hContract
  | _ => simp [Eta.contract?] at hContract
theorem inferSortWith_andE_eq_bool {bound : List CoreSort} {left right : Term} {sort : CoreSort} (hSort : Term.inferSortWith bound (.andE left right) = some sort) : sort = .bool := by
  cases hLeft : Term.inferSortWith bound left with
  | none => simp [Term.inferSortWith, hLeft] at hSort
  | some leftSort =>
      cases hRight : Term.inferSortWith bound right with
      | none => simp [Term.inferSortWith, hLeft, hRight] at hSort
      | some rightSort =>
          simp [Term.inferSortWith, hLeft, hRight] at hSort
          exact hSort.2.symm
theorem inferSortWith_orE_eq_bool {bound : List CoreSort} {left right : Term} {sort : CoreSort} (hSort : Term.inferSortWith bound (.orE left right) = some sort) : sort = .bool :=
  inferSortWith_andE_eq_bool (by
    simpa only [Term.inferSortWith] using hSort)
theorem inferSortWith_impE_eq_bool {bound : List CoreSort} {left right : Term} {sort : CoreSort} (hSort : Term.inferSortWith bound (.impE left right) = some sort) : sort = .bool :=
  inferSortWith_andE_eq_bool (by
    simpa only [Term.inferSortWith] using hSort)
theorem inferSortWith_iffE_eq_bool {bound : List CoreSort} {left right : Term} {sort : CoreSort} (hSort : Term.inferSortWith bound (.iffE left right) = some sort) : sort = .bool :=
  inferSortWith_andE_eq_bool (by
    simpa only [Term.inferSortWith] using hSort)
theorem inferSortWith_quote_eq_bool {bound : List CoreSort} {formula : Formula} {sort : CoreSort} (hSort : Term.inferSortWith bound (.quote formula) = some sort) : sort = .bool := by
  cases hCheck : Formula.checkWith bound formula <;>
    simp [Term.inferSortWith, hCheck] at hSort
  exact hSort.symm
theorem inferSortWith_ite_eq_declared {bound : List CoreSort} {declared result : CoreSort} {condition : Formula} {thenTerm elseTerm : Term} (hSort : Term.inferSortWith bound (.ite declared condition thenTerm elseTerm) = some result) : result = declared := by
  cases hCheck : Formula.checkWith bound condition <;>
    simp [Term.inferSortWith, hCheck] at hSort
  cases hThen : Term.inferSortWith bound thenTerm with
  | none => simp [hThen] at hSort
  | some thenSort =>
      cases hElse : Term.inferSortWith bound elseTerm with
      | none => simp [hThen, hElse] at hSort
      | some elseSort =>
          simp [hThen, hElse] at hSort
          exact hSort.2.symm
theorem eval_beta_instantiate_of_inferSortWith {M : Model} (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (domain codomain : CoreSort) (body argument : Term) {resultSort : CoreSort} (hSource : Term.inferSortWith bound (.apply (.lam domain codomain body) argument) = some resultSort) : Term.eval env (.apply (.lam domain codomain body) argument) = Term.eval env (Term.instantiate argument body) := by
  obtain ⟨actualDomain, hLambda, hArgument⟩ :=
    inferSortWith_apply_parts hSource
  obtain ⟨hArrow, hBody⟩ := inferSortWith_lam_parts hLambda
  cases hArrow
  exact eval_beta_instantiate contract env domain codomain body argument (by
      intro value hValue
      exact eval_mem_of_inferSortWith contract (domain :: bound) (env.push value) (Env.respectsBound_push hBound hValue)
        (Env.respectsFree_push hFree value) body codomain hBody) (eval_mem_of_inferSortWith contract bound env hBound hFree argument domain hArgument)
theorem inferSortWith_unique {bound : List CoreSort} {term : Term} {left right : CoreSort} (hLeft : Term.inferSortWith bound term = some left) (hRight : Term.inferSortWith bound term = some right) : left = right := by
  rw [hLeft] at hRight
  exact Option.some.inj hRight
@[simp]
theorem inferSortWith_bool_eq_bool {bound : List CoreSort} {value : Bool} : Term.inferSortWith bound (.bool value) = some .bool := rfl
@[simp]
theorem inferSortWith_notE_eq_bool_iff {bound : List CoreSort} {body : Term} : Term.inferSortWith bound (.notE body) = some .bool ↔ Term.inferSortWith bound body = some .bool := by
  cases hBody : Term.inferSortWith bound body <;>
    simp [Term.inferSortWith, hBody]
@[simp]
theorem inferSortWith_andE_eq_bool_iff {bound : List CoreSort} {left right : Term} : Term.inferSortWith bound (.andE left right) = some .bool ↔ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool := by
  cases hLeft : Term.inferSortWith bound left <;>
    cases hRight : Term.inferSortWith bound right <;>
    simp [Term.inferSortWith, hLeft, hRight]
@[simp]
theorem inferSortWith_orE_eq_bool_iff {bound : List CoreSort} {left right : Term} : Term.inferSortWith bound (.orE left right) = some .bool ↔ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool := by
  simpa only [Term.inferSortWith] using (inferSortWith_andE_eq_bool_iff (bound := bound) (left := left) (right := right))
@[simp]
theorem inferSortWith_impE_eq_bool_iff {bound : List CoreSort} {left right : Term} : Term.inferSortWith bound (.impE left right) = some .bool ↔ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool := by
  simpa only [Term.inferSortWith] using (inferSortWith_andE_eq_bool_iff (bound := bound) (left := left) (right := right))
@[simp]
theorem inferSortWith_iffE_eq_bool_iff {bound : List CoreSort} {left right : Term} : Term.inferSortWith bound (.iffE left right) = some .bool ↔ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool := by
  simpa only [Term.inferSortWith] using (inferSortWith_andE_eq_bool_iff (bound := bound) (left := left) (right := right))
@[simp]
theorem inferSortWith_quote_eq_bool_iff {bound : List CoreSort} {formula : Formula} : Term.inferSortWith bound (.quote formula) = some .bool ↔ Formula.checkWith bound formula = true := by
  cases hCheck : Formula.checkWith bound formula <;>
    simp [Term.inferSortWith, hCheck]
theorem rewriteRootTerm?_sound {M : Model} (contract : FoolLambdaContract M) (config : Config) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Term} {rule : StepRule} {resultSort : CoreSort} (hSource : Term.inferSortWith bound source = some resultSort) (hTarget : Term.inferSortWith bound target = some resultSort) (hStep : rewriteRootTerm? config source = some (rule, target)) : SemanticallyEqual env source target := by
  cases source with
  | apply fn argument =>
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases fn <;> simp at hStep
        next domain codomain body =>
          rcases hStep with ⟨rfl, rfl⟩
          exact eval_beta_instantiate_of_inferSortWith contract bound env
            hBound hFree domain codomain body argument hSource
      next =>
        simp at hStep
  | notE body =>
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases body <;> simp at hStep
        next value =>
          rcases hStep with ⟨rfl, rfl⟩
          have hResult : resultSort = .bool := (inferSortWith_notE_parts hSource).1
          subst resultSort
          apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree
          · exact hSource
          · exact hTarget
          · simp only [Term.eval, contract.not_holds, contract.bool_holds]
            cases value <;> simp
        next formula =>
          rcases hStep with ⟨rfl, rfl⟩
          cases hFormula : Formula.checkWith bound formula <;>
            simp [Term.inferSortWith, hFormula] at hSource
          subst resultSort
          apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree
          · simp [Term.inferSortWith, hFormula]
          · exact hTarget
          · simp only [Term.eval, contract.not_holds, contract.quote_holds, Formula.eval]
      next =>
        simp at hStep
  | andE left right =>
      have hSort : resultSort = .bool := inferSortWith_andE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree (.andE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.and_holds, contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;> simp_all)
        all_goals
          try (rcases hStep with ⟨_, hTargetEq⟩ <;> simp_all)
        all_goals
          grind [Term.eval, Formula.eval, contract.and_holds, contract.bool_holds, contract.quote_holds]
      next =>
        simp at hStep
  | orE left right =>
      have hSort : resultSort = .bool := inferSortWith_orE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree (.orE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.or_holds, contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;> simp_all)
        all_goals
          grind [Term.eval, Formula.eval, contract.or_holds, contract.bool_holds, contract.quote_holds]
      next =>
        simp at hStep
  | impE left right =>
      have hSort : resultSort = .bool := inferSortWith_impE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree (.impE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.imp_holds, contract.not_holds, contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;> simp_all)
        all_goals
          grind [Term.eval, Formula.eval, contract.imp_holds, contract.not_holds, contract.bool_holds, contract.quote_holds]
      next =>
        simp at hStep
  | iffE left right =>
      have hSort : resultSort = .bool := inferSortWith_iffE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree (.iffE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.iff_holds, contract.not_holds, contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;> simp_all [Term.eval, contract.iff_holds, contract.not_holds, contract.bool_holds, contract.quote_holds])
        case bool.bool leftValue rightValue =>
          cases leftValue <;> cases rightValue
          all_goals
            rcases hStep with ⟨_, rfl⟩ <;>
              simp [Term.eval, contract.not_holds, contract.bool_holds]
        all_goals
          try simp_all [Term.eval, Formula.eval, contract.iff_holds, contract.not_holds, contract.bool_holds, contract.quote_holds]
        all_goals
          try
            rcases hStep with ⟨_, hTargetEq⟩
            rw [← hTargetEq]
            simp [Term.eval, Formula.eval, contract.iff_holds, contract.not_holds, contract.quote_holds]
        all_goals
          try
            rcases hStep with ⟨hStructure, _, hTargetEq⟩
            rw [← hTargetEq]
            simp [Term.eval, contract.bool_holds]
      next =>
        simp at hStep
  | quote formula =>
      have hSort : resultSort = .bool := inferSortWith_quote_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree (.quote formula) target hSource hTarget
      cases formula <;>
        simp [rewriteRootTerm?] at hStep <;>
        grind [Term.eval, Formula.eval, contract.quote_holds, contract.bool_holds]
  | lam domain codomain body =>
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases hContract : Eta.contract? domain body with
        | none => simp [hContract] at hStep
        | some contracted =>
            simp [hContract] at hStep
            rcases hStep with ⟨_, hTargetEq⟩
            subst target
            exact eval_eta_contract? contract bound env hBound hFree
              domain codomain body contracted (inferSortWith_lam_parts hSource).2 hContract
      next =>
        simp at hStep
  | ite sort condition thenTerm elseTerm =>
      simp only [rewriteRootTerm?] at hStep
      by_cases hTrue : condition = .trueE
      · subst condition
        simp at hStep
        rcases hStep with ⟨_, hTargetEq⟩
        subst target
        change Term.eval env (.ite sort .trueE thenTerm elseTerm) =
          Term.eval env thenTerm
        rw [Term.eval_ite contract.toFoolContract]
        simp [Formula.Satisfies, Formula.eval]
      · by_cases hFalse : condition = .falseE
        · subst condition
          simp at hStep
          rcases hStep with ⟨_, hTargetEq⟩
          subst target
          change Term.eval env (.ite sort .falseE thenTerm elseTerm) =
            Term.eval env elseTerm
          rw [Term.eval_ite contract.toFoolContract]
          simp [Formula.Satisfies, Formula.eval]
        · by_cases hEqual : SyntaxEq.termEq thenTerm elseTerm = true
          · have hTerms : thenTerm = elseTerm :=
              SyntaxEq.termEq_eq_true.mp hEqual
            subst elseTerm
            simp [hEqual] at hStep
            rcases hStep with ⟨_, hTargetEq⟩
            subst target
            change Term.eval env (.ite sort condition thenTerm thenTerm) =
              Term.eval env thenTerm
            rw [Term.eval_ite contract.toFoolContract]
            by_cases hCondition : Formula.Satisfies env condition <;>
              simp [hCondition]
          · by_cases hFool : config.fool = true
            · cases sort with
              | object | prop | named | arrow => simp [hEqual, hFool] at hStep
              | bool =>
                  have hResult : resultSort = .bool :=
                    inferSortWith_ite_eq_declared hSource
                  subst resultSort
                  apply eval_eq_of_inferred_bool_holds_iff contract bound env
                    hBound hFree (.ite .bool condition thenTerm elseTerm) target
                    hSource hTarget
                  by_cases hThenTrue : thenTerm = .bool true
                  · by_cases hElseFalse : elseTerm = .bool false
                    · subst thenTerm
                      subst elseTerm
                      simp [hEqual, hFool] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract.toFoolContract, Term.eval, Formula.Satisfies, hCondition, contract.quote_holds, contract.bool_holds]
                    · subst thenTerm
                      simp [hEqual, hFool] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract.toFoolContract, Term.eval, Formula.Satisfies, hCondition, contract.or_holds, contract.quote_holds, contract.bool_holds]
                  · by_cases hThenFalse : thenTerm = .bool false
                    · by_cases hElseTrue : elseTerm = .bool true
                      · subst thenTerm
                        subst elseTerm
                        simp [hEqual, hFool] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract.toFoolContract, Term.eval, Formula.eval, Formula.Satisfies, hCondition, contract.quote_holds, contract.bool_holds]
                      · subst thenTerm
                        simp [hEqual, hFool] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract.toFoolContract, Term.eval, Formula.eval, Formula.Satisfies, hCondition, contract.and_holds, contract.quote_holds, contract.bool_holds]
                    · by_cases hElseTrue : elseTerm = .bool true
                      · subst elseTerm
                        simp [hEqual, hFool] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract.toFoolContract, Term.eval, Formula.Satisfies, hCondition, contract.imp_holds, contract.quote_holds, contract.bool_holds]
                      · by_cases hElseFalse : elseTerm = .bool false
                        · subst elseTerm
                          simp [hEqual, hFool] at hStep
                          rcases hStep with ⟨_, hTargetEq⟩
                          subst target
                          by_cases hCondition : Formula.Satisfies env condition <;>
                            simp only [Formula.Satisfies] at hCondition <;>
                            simp [Term.eval_ite contract.toFoolContract, Term.eval, Formula.Satisfies, hCondition, contract.and_holds, contract.quote_holds, contract.bool_holds]
                        · simp [hEqual, hFool, hThenTrue, hThenFalse, hElseTrue, hElseFalse] at hStep
            · simp [hEqual, hFool] at hStep
  | bvar => simp [rewriteRootTerm?] at hStep
  | fvar => simp [rewriteRootTerm?] at hStep
  | app => simp [rewriteRootTerm?] at hStep
  | bool => simp [rewriteRootTerm?] at hStep
theorem rewriteRootAnd_target_bool {config : Config} {bound : List CoreSort} {left right target : Term} {rule : StepRule} (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) (hStep : rewriteRootTerm? config (.andE left right) = some (rule, target)) : Term.inferSortWith bound target = some .bool := by
  simp only [rewriteRootTerm?] at hStep
  split at hStep
  next =>
    split at hStep <;> simp_all
    all_goals
      rcases hStep with ⟨hFirst, hRest⟩
      first
      | rcases hRest with ⟨_, hTargetEq⟩
        subst target
        simp_all
      | subst target
        simp_all [Formula.checkWith]
  next =>
    simp at hStep
theorem rewriteRootOr_target_bool {config : Config} {bound : List CoreSort} {left right target : Term} {rule : StepRule} (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) (hStep : rewriteRootTerm? config (.orE left right) = some (rule, target)) : Term.inferSortWith bound target = some .bool := by
  simp only [rewriteRootTerm?] at hStep
  split at hStep
  next =>
    split at hStep <;> simp_all
    all_goals
      rcases hStep with ⟨hFirst, hRest⟩
      first
      | rcases hRest with ⟨_, hTargetEq⟩
        subst target
        simp_all
      | subst target
        simp_all [Formula.checkWith]
  next =>
    simp at hStep
theorem rewriteRootImp_target_bool {config : Config} {bound : List CoreSort} {left right target : Term} {rule : StepRule} (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) (hStep : rewriteRootTerm? config (.impE left right) = some (rule, target)) : Term.inferSortWith bound target = some .bool := by
  simp only [rewriteRootTerm?] at hStep
  split at hStep
  next =>
    split at hStep <;> simp_all
    all_goals
      rcases hStep with ⟨hFirst, hRest⟩
      first
      | rcases hRest with ⟨_, hTargetEq⟩
        subst target
        simp_all
      | subst target
        simp_all [Formula.checkWith]
  next =>
    simp at hStep
theorem rewriteRootIff_target_bool {config : Config} {bound : List CoreSort} {left right target : Term} {rule : StepRule} (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) (hStep : rewriteRootTerm? config (.iffE left right) = some (rule, target)) : Term.inferSortWith bound target = some .bool := by
  simp only [rewriteRootTerm?] at hStep
  split at hStep
  next =>
    split at hStep <;> simp_all
    all_goals
      rcases hStep with ⟨hFirst, hRest⟩
      first
      | rcases hRest with ⟨_, hTargetEq⟩
        subst target
        simp_all
      | subst target
        simp_all [Formula.checkWith]
  next =>
    simp at hStep
theorem rewriteRootNot_target_bool {config : Config} {bound : List CoreSort} {body target : Term} {rule : StepRule} (hBody : Term.inferSortWith bound body = some .bool) (hStep : rewriteRootTerm? config (.notE body) = some (rule, target)) : Term.inferSortWith bound target = some .bool := by
  simp only [rewriteRootTerm?] at hStep
  split at hStep
  next =>
    split at hStep <;> simp_all
    all_goals
      rcases hStep with ⟨_, hTargetEq⟩
      subst target
      simp_all [Formula.checkWith]
  next =>
    simp at hStep
theorem rewriteRootQuote_target_bool {config : Config} {bound : List CoreSort} {formula : Formula} {target : Term} {rule : StepRule} (hFormula : Formula.checkWith bound formula = true) (hStep : rewriteRootTerm? config (.quote formula) = some (rule, target)) : Term.inferSortWith bound target = some .bool := by
  simp only [rewriteRootTerm?] at hStep
  split at hStep
  next =>
    split at hStep <;> simp_all
    all_goals
      rcases hStep with ⟨_, hTargetEq⟩
      subst target
      simp
  next =>
    simp at hStep
theorem rewriteRootIte_target_sort {config : Config} {bound : List CoreSort} {declared : CoreSort} {condition : Formula} {thenTerm elseTerm target : Term} {rule : StepRule} (hCondition : Formula.checkWith bound condition
    = true) (hThen : Term.inferSortWith bound thenTerm = some declared) (hElse : Term.inferSortWith bound elseTerm = some declared) (hStep : rewriteRootTerm? config (.ite declared condition thenTerm elseTerm) = some
    (rule, target)) : Term.inferSortWith bound target = some declared := by
  simp only [rewriteRootTerm?] at hStep
  split at hStep <;> simp_all
  all_goals
    repeat' first | split at hStep
    all_goals simp_all
  all_goals
    rcases hStep with ⟨hFirst, hRest⟩
    first
    | rcases hRest with ⟨_, hTargetEq⟩
      subst target
      simp_all [Formula.checkWith]
    | subst target
      simp_all [Formula.checkWith]
theorem rewriteRootTerm?_sound_of_typed {M : Model} (contract : FoolLambdaContract M) (config : Config) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source
    target : Term} {rule : StepRule} {sourceSort targetSort : CoreSort} (hSource : Term.inferSortWith bound source = some sourceSort) (hTarget : Term.inferSortWith bound target = some targetSort) (hStep :
    rewriteRootTerm? config source = some (rule, target)) : SemanticallyEqual env source target := by
  cases source with
  | apply fn argument =>
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases fn <;> simp at hStep
        next domain codomain body =>
          rcases hStep with ⟨rfl, rfl⟩
          exact eval_beta_instantiate_of_inferSortWith contract bound env
            hBound hFree domain codomain body argument hSource
      next =>
        simp at hStep
  | lam domain codomain body =>
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases hContract : Eta.contract? domain body with
        | none => simp [hContract] at hStep
        | some contracted =>
            simp [hContract] at hStep
            rcases hStep with ⟨_, rfl⟩
            exact eval_eta_contract? contract bound env hBound hFree
              domain codomain body contracted (inferSortWith_lam_parts hSource).2 hContract
      next =>
        simp at hStep
  | notE body =>
      rcases inferSortWith_notE_parts hSource with ⟨rfl, hBody⟩
      have hTargetBool := rewriteRootNot_target_bool hBody hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_sound contract config bound env hBound hFree
        hSource hTarget hStep
  | andE left right =>
      rcases inferSortWith_andE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootAnd_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_sound contract config bound env hBound hFree
        hSource hTarget hStep
  | orE left right =>
      rcases inferSortWith_orE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootOr_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_sound contract config bound env hBound hFree
        hSource hTarget hStep
  | impE left right =>
      rcases inferSortWith_impE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootImp_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_sound contract config bound env hBound hFree
        hSource hTarget hStep
  | iffE left right =>
      rcases inferSortWith_iffE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootIff_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_sound contract config bound env hBound hFree
        hSource hTarget hStep
  | quote formula =>
      rcases inferSortWith_quote_parts hSource with ⟨rfl, hFormula⟩
      have hTargetBool := rewriteRootQuote_target_bool hFormula hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_sound contract config bound env hBound hFree
        hSource hTarget hStep
  | ite declared condition thenTerm elseTerm =>
      rcases inferSortWith_ite_parts hSource with
        ⟨rfl, hCondition, hThen, hElse⟩
      have hTargetDeclared :=
        rewriteRootIte_target_sort hCondition hThen hElse hStep
      have hTargetSort : targetSort = sourceSort :=
        inferSortWith_unique hTarget hTargetDeclared
      subst targetSort
      exact rewriteRootTerm?_sound contract config bound env hBound hFree
        hSource hTarget hStep
  | bvar => simp [rewriteRootTerm?] at hStep
  | fvar => simp [rewriteRootTerm?] at hStep
  | app => simp [rewriteRootTerm?] at hStep
  | bool => simp [rewriteRootTerm?] at hStep
theorem eval_shift_under_push {M : Model} (env : Env M) (value : M.Carrier) (term : Term) : Term.eval (env.push value) (Term.shift 1 term) = Term.eval env term := by
  simp only [Term.shift]
  rw [Term.eval_shiftAbove]
  apply Term.eval_eq_of_env_eq
  · intro index
    rw [Env.skip_zero_bound]
    simp [Env.drop, Env.push]
  · intro sort id
    rfl
end Term
namespace Formula
def FoolLambdaSatisfiable (formula : Formula) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Nonempty (FoolLambdaContract M) ∧
    Env.RespectsFree env ∧ Formula.Satisfies env formula
theorem satisfies_functionExtensionality_iff {M : Model} (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (domain codomain :
    CoreSort) (left right : Term) (hLeft : Term.inferSortWith bound left = some (.arrow domain codomain)) (hRight : Term.inferSortWith bound right = some (.arrow domain codomain)) : Formula.Satisfies env (.equal (.arrow
    domain codomain) left right) ↔ Formula.Satisfies env (.forallE domain (.equal codomain (.apply (Term.shift 1 left) (.bvar domain 0)) (.apply (Term.shift 1 right) (.bvar domain 0)))) := by
  have hLeftMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    left (.arrow domain codomain) hLeft
  have hRightMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    right (.arrow domain codomain) hRight
  simp only [Formula.Satisfies, Formula.eval, Term.eval, Term.eval_shift_under_push]
  exact contract.function_extensionality domain codomain _ _ hLeftMem hRightMem
theorem satisfies_boolEquality_iff {M : Model} (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (left right : Term) (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) : Formula.Satisfies env (.equal .bool left right) ↔ (M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) := by
  have hLeftMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    left .bool hLeft
  have hRightMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    right .bool hRight
  simpa only [Formula.Satisfies, Formula.eval] using
    contract.bool_extensionality _ _ hLeftMem hRightMem
theorem rewriteRootFormula?_sound {M : Model} (contract : FoolLambdaContract M) (config : Config) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Formula} {rule : StepRule} (hSource : Formula.checkWith bound source = true) (_hTarget : Formula.checkWith bound target = true) (hStep : rewriteRootFormula? config source = some (rule, target)) : SemanticallyEquivalent env source target := by
  cases source with
  | trueE => simp [rewriteRootFormula?] at hStep
  | falseE => simp [rewriteRootFormula?] at hStep
  | atom => simp [rewriteRootFormula?] at hStep
  | equal sort left right =>
      have hSorts := inferSortWith_of_check_equal hSource
      simp only [rewriteRootFormula?] at hStep
      by_cases hRefl : (config.connectiveSimp && SyntaxEq.termEq left right) = true
      · have hEqual : SyntaxEq.termEq left right = true := (Bool.and_eq_true_iff.mp hRefl).2
        have hTerms : left = right := SyntaxEq.termEq_eq_true.mp hEqual
        subst right
        simp only [hRefl] at hStep
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · have hReflFalse : (config.connectiveSimp && SyntaxEq.termEq left right) = false :=
          Bool.eq_false_iff.mpr hRefl
        simp only [hReflFalse, Bool.false_eq] at hStep
        cases sort with
        | arrow domain codomain =>
            by_cases hExt : config.extensionality = true
            · simp [hExt] at hStep
              rcases hStep with ⟨_, rfl⟩
              exact satisfies_functionExtensionality_iff contract bound env
                hBound hFree domain codomain left right hSorts.1 hSorts.2
            · simp [hExt] at hStep
        | bool =>
            have hBool :=
              satisfies_boolEquality_iff contract bound env hBound hFree
                left right hSorts.1 hSorts.2
            by_cases hFool : config.fool = true
            · simp [hFool] at hStep
              cases left <;> cases right <;>
                try cases ‹Bool› <;> try cases ‹Bool›
              all_goals
                rcases hStep with ⟨_, rfl⟩
                simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.bool_holds, contract.quote_holds] at hBool ⊢
              all_goals exact hBool
            · simp [hFool] at hStep
        | object => simp at hStep
        | prop => simp at hStep
        | named => simp at hStep
  | boolTerm term =>
      simp only [rewriteRootFormula?] at hStep
      by_cases hFool : config.fool = true
      · simp [hFool] at hStep
        cases term with
        | bool value =>
            cases value <;>
              simp at hStep <;>
              rcases hStep with ⟨_, rfl⟩ <;>
              simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.bool_holds]
        | notE body =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.not_holds]
        | andE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.and_holds]
        | orE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.or_holds]
        | impE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.imp_holds]
        | iffE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.iff_holds]
        | quote formula =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.quote_holds]
        | ite sort condition thenTerm elseTerm =>
            cases sort <;> simp at hStep
            next =>
              rcases hStep with ⟨_, rfl⟩
              by_cases hCondition : Formula.Satisfies env condition <;>
                simp only [Formula.Satisfies] at hCondition <;>
                simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval_ite contract.toFoolContract, hCondition]
        | bvar => simp at hStep
        | fvar => simp at hStep
        | app => simp at hStep
        | apply => simp at hStep
        | lam => simp at hStep
      · simp [hFool] at hStep
  | neg body =>
      simp only [rewriteRootFormula?] at hStep
      by_cases hConfig : config.connectiveSimp = true
      · simp [hConfig] at hStep
        cases body <;> simp at hStep
        all_goals
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · simp [hConfig] at hStep
  | imp left right
  | conj left right
  | disj left right
  | iffE left right =>
      simp only [rewriteRootFormula?] at hStep
      by_cases hConfig : config.connectiveSimp = true
      · simp [hConfig] at hStep
        by_cases hEqual : SyntaxEq.formulaEq left right = true
        · have hFormulas : left = right := SyntaxEq.formulaEq_eq_true.mp hEqual
          subst right
          cases left <;> simp at hStep <;> rcases hStep with ⟨_, rfl⟩ <;>
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
        · cases left <;> cases right <;> simp [hEqual] at hStep
          all_goals
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · simp [hConfig] at hStep
  | forallE sort body =>
      simp only [rewriteRootFormula?] at hStep
      by_cases hConfig : config.quantifierSimp = true
      · simp [hConfig] at hStep
        cases body <;> simp at hStep
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · simp [hConfig] at hStep
  | existsE sort body =>
      simp only [rewriteRootFormula?] at hStep
      by_cases hConfig : config.quantifierSimp = true
      · simp [hConfig] at hStep
        cases body <;> simp at hStep
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · simp [hConfig] at hStep
end Formula
open _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Formula _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Term
namespace FoolLambdaContract
/-- 高阶实例使用实际根规则及原模型的 λ 同余。 -/
theorem rootRewriteSemantics {M : Model} (contract : FoolLambdaContract M) (config : Config) :
    RootRewriteSemantics M config True where
  term bound env hBound hFree _ _ _ _ _ _ _ hSource hTarget hStep :=
    Term.rewriteRootTerm?_sound_of_typed contract config bound env hBound hFree hSource hTarget hStep
  formula bound env hBound hFree _ _ _ _ _ hSource hTarget hStep :=
    Formula.rewriteRootFormula?_sound contract config bound env hBound hFree hSource hTarget hStep
  lambda_congr _ := contract.lambda_congr
end FoolLambdaContract

theorem Formula.rewriteOnceFormula?_sound {M : Model} (contract : FoolLambdaContract M) (config : Config) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Formula} {rule : StepRule} (hSource : Formula.checkWith bound source = true) (hTarget : Formula.checkWith bound target = true) (hStep : rewriteOnceFormula? config source = some (rule, target)) : SemanticallyEquivalent env source target := by
  exact Formula.rewriteOnceFormula?_of_root (contract.rootRewriteSemantics config) bound env hBound hFree
    (Or.inl True.intro) (Or.inl True.intro) hSource hTarget hStep

theorem Term.rewriteOnceTerm?_sound {M : Model} (contract : FoolLambdaContract M) (config : Config) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source
    target : Term} {rule : StepRule} {sourceSort targetSort : CoreSort} (hSource : Term.inferSortWith bound source = some sourceSort) (hTarget : Term.inferSortWith bound target = some targetSort) (hStep :
    rewriteOnceTerm? config source = some (rule, target)) : SemanticallyEqual env source target := by
  exact Term.rewriteOnceTerm?_of_root (contract.rootRewriteSemantics config) bound env hBound hFree
    (Or.inl True.intro) (Or.inl True.intro) hSource hTarget hStep

theorem Term.rewriteOnceTermList?_sound {M : Model} (contract : FoolLambdaContract M) (config : Config) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    {source target : List Term} {rule : StepRule} {sourceSorts targetSorts : List CoreSort} (hSource : Term.inferSortListWith bound source = some sourceSorts) (hTarget : Term.inferSortListWith bound target = some
    targetSorts) (hStep : rewriteOnceTermList? config source = some (rule, target)) : ListSemanticallyEqual env source target := by
  exact Term.rewriteOnceTermList?_of_root (contract.rootRewriteSemantics config) bound env hBound hFree
    (Or.inl True.intro) (Or.inl True.intro) hSource hTarget hStep

namespace TraceExpr
def SemanticallyEquivalent {M : Model} (env : Env M) : TraceExpr → TraceExpr → Prop
  | .term left, .term right => Term.SemanticallyEqual env left right
  | .formula left, .formula right => Formula.SemanticallyEquivalent env left right
  | _, _ => False
theorem eq_eq_true {left right : TraceExpr} : TraceExpr.eq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [TraceExpr.eq, SyntaxEq.termEq_eq_true, SyntaxEq.formulaEq_eq_true]
theorem semanticallyEquivalent_refl {M : Model} (env : Env M) (expr : TraceExpr) : SemanticallyEquivalent env expr expr := by
  cases expr <;>
    simp [SemanticallyEquivalent, Term.SemanticallyEqual, Formula.SemanticallyEquivalent]
theorem semanticallyEquivalent_trans {M : Model} {env : Env M} {left middle right : TraceExpr} (hLeft : SemanticallyEquivalent env left middle) (hRight : SemanticallyEquivalent env middle right) : SemanticallyEquivalent env left right := by
  cases left <;> cases middle <;> cases right <;>
    simp [SemanticallyEquivalent, Term.SemanticallyEqual, Formula.SemanticallyEquivalent] at hLeft hRight ⊢
  · exact hLeft.trans hRight
  · exact hLeft.trans hRight
end TraceExpr
namespace Env
theorem respectsBound_nil {M : Model} (env : Env M) : RespectsBound [] env := by
  intro index sort hLookup
  cases index <;> simp [TypeCheck.lookupBound?] at hLookup
end Env
namespace Step
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M) (config : Config) (env : Env M) (hFree : Env.RespectsFree env) (step : Step) (hCheck : step.check config = true) : TraceExpr.SemanticallyEquivalent env step.before step.after := by
  have hBound : Env.RespectsBound [] env := Env.respectsBound_nil env
  rcases step with ⟨stepRule, before, after⟩
  unfold Step.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hChecks, hRewrite⟩
  rcases Bool.and_eq_true_iff.mp hChecks with ⟨hBefore, hAfter⟩
  cases before with
  | term source =>
      cases after with
      | term target =>
          cases hSourceSort : Term.inferSortWith [] source with
          | none => simp [TraceExpr.check?, Term.inferSort?, hSourceSort] at hBefore
          | some sourceSort =>
              cases hTargetSort : Term.inferSortWith [] target with
              | none => simp [TraceExpr.check?, Term.inferSort?, hTargetSort] at hAfter
              | some targetSort =>
                  cases hStep : rewriteOnceTerm? config source with
                  | none => simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
                  | some value =>
                      rcases value with ⟨rule, rewritten⟩
                      simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq, SyntaxEq.termEq_eq_true] at hRewrite
                      rcases hRewrite with ⟨_, hTarget⟩
                      subst target
                      simpa [TraceExpr.SemanticallyEquivalent] using
                        Term.rewriteOnceTerm?_sound contract config [] env
                          hBound hFree hSourceSort hTargetSort hStep
      | formula target =>
          cases hStep : rewriteOnceTerm? config source <;>
            simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq] at hRewrite
  | formula source =>
      cases after with
      | term target =>
          cases hStep : rewriteOnceFormula? config source <;>
            simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq] at hRewrite
      | formula target =>
          cases hStep : rewriteOnceFormula? config source with
          | none => simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
          | some value =>
              rcases value with ⟨rule, rewritten⟩
              simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq, SyntaxEq.formulaEq_eq_true] at hRewrite
              rcases hRewrite with ⟨_, hTarget⟩
              subst target
              exact
                Formula.rewriteOnceFormula?_sound contract config [] env
                  hBound hFree (by simpa [TraceExpr.check?, Formula.check?] using hBefore) (by simpa [TraceExpr.check?, Formula.check?] using hAfter)
                    hStep
end Step
namespace Trace
theorem replay?_sound {M : Model} (contract : FoolLambdaContract M) (config : Config) (env : Env M) (hFree : Env.RespectsFree env) (steps : List Step) (source target : TraceExpr) (hReplay : _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay? config source steps = some target) : TraceExpr.SemanticallyEquivalent env source target := by
  induction steps generalizing source with
  | nil =>
      simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      subst target
      exact TraceExpr.semanticallyEquivalent_refl env source
  | cons step rest ih =>
      simp only
        [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      by_cases hLink : (TraceExpr.eq source step.before && step.check config) = true
      · simp [hLink] at hReplay
        have hLinkParts := Bool.and_eq_true_iff.mp hLink
        have hSource : source = step.before :=
          TraceExpr.eq_eq_true.mp hLinkParts.1
        have hStep :
            TraceExpr.SemanticallyEquivalent env step.before step.after :=
          Step.sound_of_check contract config env hFree step hLinkParts.2
        have hRest :
            TraceExpr.SemanticallyEquivalent env step.after target :=
          ih step.after hReplay
        subst source
        exact TraceExpr.semanticallyEquivalent_trans hStep hRest
      · simp [hLink] at hReplay
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M) (config : Config) (env : Env M) (hFree : Env.RespectsFree env) (trace : Trace) (hCheck : trace.check config = true) : TraceExpr.SemanticallyEquivalent env trace.source trace.target := by
  unfold _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_, hReplayCheck⟩
  cases hReplay :
      _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?
        config trace.source trace.steps.toList with
  | none => simp [hReplay] at hReplayCheck
  | some replayTarget =>
      have hEndpoints := Bool.and_eq_true_iff.mp (by
        simpa [hReplay] using hReplayCheck)
      have hTarget : replayTarget = trace.target :=
        TraceExpr.eq_eq_true.mp hEndpoints.1
      subst replayTarget
      exact replay?_sound contract config env hFree trace.steps.toList
        trace.source trace.target hReplay
namespace SoundnessPayload
theorem sound {M : Model} (contract : FoolLambdaContract M) (env : Env M) (hFree : Env.RespectsFree env) (checked : Certificate.Checked _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.SoundnessPayload _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.SoundnessPayload.check) : TraceExpr.SemanticallyEquivalent env checked.payload.trace.source checked.payload.trace.target := by
  exact Trace.sound_of_check contract checked.payload.config env hFree
    checked.payload.trace checked.checked
end SoundnessPayload
end Trace
namespace TermPayload
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M) (env : Env M) (hFree : Env.RespectsFree env) (payload : TermPayload) (hCheck : payload.check = true) : Term.SemanticallyEqual env payload.source payload.normal := by
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.TermPayload.check, Bool.and_eq_true_iff] at hCheck
  have hTrace := hCheck.1.1.1.1.1.2
  have hSource := hCheck.1.1.1.1.2
  have hTarget := hCheck.1.1.1.2
  have hTraceSem :=
    Trace.sound_of_check contract payload.config env hFree payload.trace hTrace
  have hSourceEq :
      payload.trace.source = TraceExpr.term payload.source :=
    TraceExpr.eq_eq_true.mp hSource
  have hTargetEq :
      payload.trace.target = TraceExpr.term payload.normal :=
    TraceExpr.eq_eq_true.mp hTarget
  simpa [hSourceEq, hTargetEq, TraceExpr.SemanticallyEquivalent] using hTraceSem
end TermPayload
namespace FormulaPayload
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M) (env : Env M) (hFree : Env.RespectsFree env) (payload : FormulaPayload) (hCheck : payload.check = true) : Formula.SemanticallyEquivalent env payload.source payload.normal := by
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.FormulaPayload.check, Bool.and_eq_true_iff] at hCheck
  have hTrace := hCheck.1.1.1.1.1.2
  have hSource := hCheck.1.1.1.1.2
  have hTarget := hCheck.1.1.1.2
  have hTraceSem :=
    Trace.sound_of_check contract payload.config env hFree payload.trace hTrace
  have hSourceEq :
      payload.trace.source = TraceExpr.formula payload.source :=
    TraceExpr.eq_eq_true.mp hSource
  have hTargetEq :
      payload.trace.target = TraceExpr.formula payload.normal :=
    TraceExpr.eq_eq_true.mp hTarget
  simpa [hSourceEq, hTargetEq, TraceExpr.SemanticallyEquivalent] using hTraceSem
end FormulaPayload
namespace FoolLambdaContract
@[simp]
theorem bool_true_holds {M : Model} (contract : FoolLambdaContract M) : M.boolHolds (M.boolValue true) := by exact (contract.bool_holds true).mpr rfl
@[simp]
theorem bool_false_not_holds {M : Model} (contract : FoolLambdaContract M) : ¬ M.boolHolds (M.boolValue false) := by
  intro hFalse
  have : false = true := (contract.bool_holds false).mp hFalse
  contradiction
theorem quoteValue_eq_iff {M : Model} (contract : FoolLambdaContract M) (left right : Prop) : M.quoteValue left = M.quoteValue right ↔ (left ↔ right) :=
  contract.quote_eq_iff left right
end FoolLambdaContract
end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
