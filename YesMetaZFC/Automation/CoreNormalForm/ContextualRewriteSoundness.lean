import YesMetaZFC.Automation.CoreNormalForm.RewriteTyping

/-!
# 局部改写沿语法上下文的统一可靠性

根部规则提供可靠性，外层递归只传输类型、语法片段和环境。
`higherOrder` 为假时保留原 FOOL 片段，为真时允许全部项并显式要求 λ 同余。
该参数只组织证明，不改变可计算改写器及其配置。
-/

namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics

/-- 真正依赖模型与规则选择的三个义务；外层结构归纳只证明一次。 -/
structure RootRewriteSemantics (M : Model) (config : Config) (higherOrder : Prop) : Prop where
  term : ∀ (bound : List CoreSort) (env : Env M),
    Env.RespectsBound bound env → Env.RespectsFree env →
    ∀ {source target : Term} {rule : StepRule} {sourceSort targetSort : CoreSort},
    Term.RewriteFragment higherOrder source → Term.RewriteFragment higherOrder target →
    Term.inferSortWith bound source = some sourceSort →
    Term.inferSortWith bound target = some targetSort →
    rewriteRootTerm? config source = some (rule, target) → Term.SemanticallyEqual env source target
  formula : ∀ (bound : List CoreSort) (env : Env M),
    Env.RespectsBound bound env → Env.RespectsFree env →
    ∀ {source target : Formula} {rule : StepRule},
    Formula.RewriteFragment higherOrder source → Formula.RewriteFragment higherOrder target →
    Formula.checkWith bound source = true → Formula.checkWith bound target = true →
    rewriteRootFormula? config source = some (rule, target) → Formula.SemanticallyEquivalent env source target
  lambda_congr : higherOrder → ∀ (domain codomain : CoreSort) (left right : M.Carrier → M.Carrier),
    (∀ value, M.sortInterp domain value → left value = right value) →
    M.lambdaValue domain codomain left = M.lambdaValue domain codomain right

open _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Formula
open _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Term
mutual
  theorem Formula.rewriteOnceFormula?_of_root
      {M : Model} {config : Config} {higherOrder : Prop}
      (semantics : RootRewriteSemantics M config higherOrder)
      (bound : List CoreSort) (env : Env M)
      (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
      {source target : Formula} {rule : StepRule}
      (hSourceFragment : Formula.RewriteFragment higherOrder source)
      (hTargetFragment : Formula.RewriteFragment higherOrder target)
      (hSource : Formula.checkWith bound source = true)
      (hTarget : Formula.checkWith bound target = true)
      (hStep : rewriteOnceFormula? config source = some (rule, target)) :
      SemanticallyEquivalent env source target := by
    cases source with
    | trueE => simp [rewriteOnceFormula?] at hStep
    | falseE => simp [rewriteOnceFormula?] at hStep
    | atom predicate args =>
        simp only [Formula.RewriteFragment, Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceTermList? config args with
        | none => simp [hRewrite, rewriteRootFormula?] at hStep
        | some value =>
            rcases value with ⟨childRule, args'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.RewriteFragment, Formula.foolFragment] at hTargetFragment
            obtain ⟨sourceSorts, hSourceArgs⟩ :=
              inferSortListWith_of_check_atom hSource
            obtain ⟨targetSorts, hTargetArgs⟩ :=
              inferSortListWith_of_check_atom hTarget
            have hArgs :=
              Term.rewriteOnceTermList?_of_root semantics bound env hBound hFree
                hSourceFragment hTargetFragment hSourceArgs hTargetArgs hRewrite
            change
              SemanticallyEquivalent env (Formula.atom predicate args) (Formula.atom predicate args')
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change (M.predicateInterp predicate (args.map (Term.eval env)) ↔ M.predicateInterp predicate (args'.map (Term.eval env)))
            rw [hArgs]
    | equal sort left right =>
        simp only [Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceSorts := inferSortWith_of_check_equal hSource
            have hTargetSorts := inferSortWith_of_check_equal hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceSorts.1 hTargetSorts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change (Term.eval env left = Term.eval env right ↔ Term.eval env left' = Term.eval env right)
            change Term.eval env left = Term.eval env left' at hLeftSem
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceSorts := inferSortWith_of_check_equal hSource
                have hTargetSorts := inferSortWith_of_check_equal hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceSorts.2 hTargetSorts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                change (Term.eval env left = Term.eval env right ↔ Term.eval env left = Term.eval env right')
                change Term.eval env right = Term.eval env right' at hRightSem
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact semantics.formula bound env
                  hBound hFree (by
                    simpa [Term.RewriteFragment, Term.RewriteFragmentList, Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | boolTerm term =>
        simp only [Formula.RewriteFragment, Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceTerm? config term with
        | some value =>
            rcases value with ⟨childRule, term'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.RewriteFragment, Formula.foolFragment] at hTargetFragment
            have hSourceSort := inferSortWith_of_check_boolTerm hSource
            have hTargetSort := inferSortWith_of_check_boolTerm hTarget
            have hTermSem :=
              Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceSort hTargetSort hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change (M.boolHolds (Term.eval env term) ↔ M.boolHolds (Term.eval env term'))
            change Term.eval env term = Term.eval env term' at hTermSem
            rw [hTermSem]
        | none =>
            simp [hRewrite] at hStep
            exact semantics.formula bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | neg body =>
        simp only [Formula.RewriteFragment, Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.RewriteFragment, Formula.foolFragment] at hTargetFragment
            have hSourceBody := checkWith_of_check_neg hSource
            have hTargetBody := checkWith_of_check_neg hTarget
            have hBodySem :=
              Formula.rewriteOnceFormula?_of_root semantics bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceBody hTargetBody hRewrite
            simpa only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval] using
              not_congr hBodySem
        | none =>
            simp [hRewrite] at hStep
            exact semantics.formula bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | imp left right
    | conj left right
    | disj left right
    | iffE left right =>
        simp only [Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := checkWith_of_check_imp (left := left) (right := right) hSource
            have hTargetParts := checkWith_of_check_imp (left := left') (right := right) hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_of_root semantics bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change Formula.Satisfies env left ↔ Formula.Satisfies env left' at hLeftSem
            simp only [Formula.Satisfies] at hLeftSem
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := checkWith_of_check_imp (left := left) (right := right) hSource
                have hTargetParts := checkWith_of_check_imp (left := left) (right := right') hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_of_root semantics bound env
                    hBound hFree hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                change Formula.Satisfies env right ↔ Formula.Satisfies env right' at hRightSem
                simp only [Formula.Satisfies] at hRightSem
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact semantics.formula bound env
                  hBound hFree (by
                    simpa [Term.RewriteFragment, Term.RewriteFragmentList, Formula.RewriteFragment, or_and_left, Formula.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | forallE sort body
    | existsE sort body =>
        simp only [Formula.RewriteFragment, Formula.foolFragment] at hSourceFragment
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Formula.RewriteFragment, Formula.foolFragment] at hTargetFragment
            have hSourceBody := checkWith_of_check_forallE hSource
            have hTargetBody := checkWith_of_check_forallE hTarget
            have hBodySem (value : M.Carrier) (hValue : M.sortInterp sort value) :=
              Formula.rewriteOnceFormula?_of_root semantics (sort :: bound) (env.push value) (Env.respectsBound_push hBound hValue)
                (Env.respectsFree_push hFree value)
                hSourceFragment hTargetFragment
                hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            simp only [← Formula.Satisfies.eq_def]
            first
            | exact forall_congr' (fun value => imp_congr_right (hBodySem value))
            | exact exists_congr (fun value => and_congr_right (hBodySem value))
        | none =>
            simp [hRewrite] at hStep
            exact semantics.formula bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
  theorem Term.rewriteOnceTerm?_of_root
      {M : Model} {config : Config} {higherOrder : Prop}
      (semantics : RootRewriteSemantics M config higherOrder)
      (bound : List CoreSort) (env : Env M)
      (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
      {source target : Term} {rule : StepRule} {sourceSort targetSort : CoreSort}
      (hSourceFragment : Term.RewriteFragment higherOrder source)
      (hTargetFragment : Term.RewriteFragment higherOrder target)
      (hSource : Term.inferSortWith bound source = some sourceSort)
      (hTarget : Term.inferSortWith bound target = some targetSort)
      (hStep : rewriteOnceTerm? config source = some (rule, target)) :
      SemanticallyEqual env source target := by
    cases source with
    | bvar => simp [rewriteOnceTerm?] at hStep
    | fvar => simp [rewriteOnceTerm?] at hStep
    | bool => simp [rewriteOnceTerm?] at hStep
    | app symbol args =>
        simp only [Term.RewriteFragment, Term.foolFragment] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceTermList? config args with
        | none => simp [hRewrite, rewriteRootTerm?] at hStep
        | some value =>
            rcases value with ⟨childRule, args'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.RewriteFragment, Term.foolFragment] at hTargetFragment
            obtain ⟨_, sourceSorts, hSourceArgs⟩ :=
              inferSortWith_app_parts hSource
            obtain ⟨_, targetSorts, hTargetArgs⟩ :=
              inferSortWith_app_parts hTarget
            have hArgsSem :=
              Term.rewriteOnceTermList?_of_root semantics bound env hBound hFree
                hSourceFragment hTargetFragment hSourceArgs hTargetArgs hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.functionInterp symbol (args.map (Term.eval env)) =
                M.functionInterp symbol (args'.map (Term.eval env))
            rw [hArgsSem]
    | apply fn arg =>
        have hHigher : higherOrder := by
          simpa only [Term.RewriteFragment, Term.foolFragment, Bool.false_eq_true, or_false] using hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hFnRewrite : rewriteOnceTerm? config fn with
        | some value =>
            rcases value with ⟨childRule, fn'⟩
            simp [hFnRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            obtain ⟨sourceDomain, hSourceFn, hSourceArg⟩ :=
              inferSortWith_apply_parts hSource
            obtain ⟨targetDomain, hTargetFn, hTargetArg⟩ :=
              inferSortWith_apply_parts hTarget
            have hFnSem :=
              Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree (Or.inl hHigher) (Or.inl hHigher)
                hSourceFn hTargetFn hFnRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.applyInterp (Term.eval env fn) (Term.eval env arg) =
                M.applyInterp (Term.eval env fn') (Term.eval env arg)
            rw [hFnSem]
        | none =>
            simp [hFnRewrite] at hStep
            cases hArgRewrite : rewriteOnceTerm? config arg with
            | some value =>
                rcases value with ⟨childRule, arg'⟩
                simp [hArgRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                obtain ⟨sourceDomain, hSourceFn, hSourceArg⟩ :=
                  inferSortWith_apply_parts hSource
                obtain ⟨targetDomain, hTargetFn, hTargetArg⟩ :=
                  inferSortWith_apply_parts hTarget
                have hArgSem :=
                  Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree (Or.inl hHigher) (Or.inl hHigher)
                    hSourceArg hTargetArg hArgRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.applyInterp (Term.eval env fn) (Term.eval env arg) =
                    M.applyInterp (Term.eval env fn) (Term.eval env arg')
                rw [hArgSem]
            | none =>
                simp [hArgRewrite] at hStep
                exact semantics.term bound env
                  hBound hFree hSourceFragment hTargetFragment hSource hTarget hStep
    | notE body =>
        simp only [Term.RewriteFragment, Term.foolFragment] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceTerm? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.RewriteFragment, Term.foolFragment] at hTargetFragment
            have hSourceBody := (inferSortWith_notE_parts hSource).2
            have hTargetBody := (inferSortWith_notE_parts hTarget).2
            have hBodySem :=
              Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change M.notValue (Term.eval env body) = M.notValue (Term.eval env body')
            rw [hBodySem]
        | none =>
            simp [hRewrite] at hStep
            exact semantics.term bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | andE left right
    | orE left right
    | impE left right
    | iffE left right =>
        simp only [Term.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := inferSortWith_andE_parts (left := left) (right := right) hSource
            have hTargetParts := inferSortWith_andE_parts (left := left') (right := right) hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := inferSortWith_andE_parts (left := left) (right := right) hSource
                have hTargetParts := inferSortWith_andE_parts (left := left) (right := right') hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact semantics.term bound env
                  hBound hFree (by
                    simpa [Term.RewriteFragment, Term.RewriteFragmentList, Formula.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] using
                      hSourceFragment)
                  hTargetFragment
                  hSource hTarget hStep
    | quote formula =>
        simp only [Term.RewriteFragment, Term.foolFragment] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceFormula? config formula with
        | some value =>
            rcases value with ⟨childRule, formula'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.RewriteFragment, Term.foolFragment] at hTargetFragment
            have hSourceFormula := (inferSortWith_quote_parts hSource).2
            have hTargetFormula := (inferSortWith_quote_parts hTarget).2
            have hFormulaSem :=
              Formula.rewriteOnceFormula?_of_root semantics bound env hBound hFree
                hSourceFragment hTargetFragment
                hSourceFormula hTargetFormula hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.quoteValue (Formula.eval env formula).holds =
                M.quoteValue (Formula.eval env formula').holds
            exact congrArg M.quoteValue (propext hFormulaSem)
        | none =>
            simp [hRewrite] at hStep
            exact semantics.term bound env
              hBound hFree hSourceFragment hTargetFragment
              hSource hTarget hStep
    | lam domain codomain body =>
        have hHigher : higherOrder := by
          simpa only [Term.RewriteFragment, Term.foolFragment, Bool.false_eq_true, or_false] using hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceTerm? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceBody := (inferSortWith_lam_parts hSource).2
            have hTargetBody := (inferSortWith_lam_parts hTarget).2
            simp only [SemanticallyEqual, Term.eval]
            change
              M.lambdaValue domain codomain (fun value => Term.eval (env.push value) body) =
                M.lambdaValue domain codomain (fun value => Term.eval (env.push value) body')
            apply semantics.lambda_congr hHigher
            intro value hValue
            exact
              Term.rewriteOnceTerm?_of_root semantics (domain :: bound) (env.push value) (Env.respectsBound_push hBound hValue)
                (Env.respectsFree_push hFree value) (Or.inl hHigher) (Or.inl hHigher) hSourceBody hTargetBody hRewrite
        | none =>
            simp [hRewrite] at hStep
            exact semantics.term bound env
              hBound hFree hSourceFragment hTargetFragment hSource hTarget hStep
    | ite declared condition thenTerm elseTerm =>
        simp only [Term.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] at hSourceFragment
        simp only [rewriteOnceTerm?] at hStep
        cases hConditionRewrite :
            rewriteOnceFormula? config condition with
        | some value =>
            rcases value with ⟨childRule, condition'⟩
            simp [hConditionRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] at hTargetFragment
            have hSourceParts := inferSortWith_ite_parts hSource
            have hTargetParts := inferSortWith_ite_parts hTarget
            have hConditionSem :=
              Formula.rewriteOnceFormula?_of_root semantics bound env hBound hFree
                hSourceFragment.1.1 hTargetFragment.1.1
                hSourceParts.2.1 hTargetParts.2.1 hConditionRewrite
            have hConditionEq : (Formula.eval env condition).holds = (Formula.eval env condition').holds :=
              propext hConditionSem
            simp only [SemanticallyEqual, Term.eval]
            change
              M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm) =
                M.iteValue (Formula.eval env condition').holds (Term.eval env thenTerm) (Term.eval env elseTerm)
            rw [hConditionEq]
        | none =>
            simp [hConditionRewrite] at hStep
            cases hThenRewrite : rewriteOnceTerm? config thenTerm with
            | some value =>
                rcases value with ⟨childRule, thenTerm'⟩
                simp [hThenRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                have hSourceParts := inferSortWith_ite_parts hSource
                have hTargetParts := inferSortWith_ite_parts hTarget
                have hThenSem :=
                  Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                    hSourceFragment.1.2 hTargetFragment.1.2
                    hSourceParts.2.2.1 hTargetParts.2.2.1 hThenRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm) =
                    M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm') (Term.eval env elseTerm)
                rw [hThenSem]
            | none =>
                simp [hThenRewrite] at hStep
                cases hElseRewrite : rewriteOnceTerm? config elseTerm with
                | some value =>
                    rcases value with ⟨childRule, elseTerm'⟩
                    simp [hElseRewrite] at hStep
                    rcases hStep with ⟨rfl, rfl⟩
                    simp only [Term.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] at hTargetFragment
                    have hSourceParts := inferSortWith_ite_parts hSource
                    have hTargetParts := inferSortWith_ite_parts hTarget
                    have hElseSem :=
                      Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                        hSourceFragment.2 hTargetFragment.2
                        hSourceParts.2.2.2 hTargetParts.2.2.2 hElseRewrite
                    simp only [SemanticallyEqual, Term.eval]
                    change
                      M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm) =
                        M.iteValue (Formula.eval env condition).holds (Term.eval env thenTerm) (Term.eval env elseTerm')
                    rw [hElseSem]
                | none =>
                    simp [hElseRewrite] at hStep
                    exact semantics.term bound env
                      hBound hFree (by
                        simpa [Term.RewriteFragment, Term.RewriteFragmentList, Formula.RewriteFragment, or_and_left, Term.foolFragment, Bool.and_eq_true] using
                          hSourceFragment)
                      hTargetFragment
                      hSource hTarget hStep
  theorem Term.rewriteOnceTermList?_of_root
      {M : Model} {config : Config} {higherOrder : Prop}
      (semantics : RootRewriteSemantics M config higherOrder)
      (bound : List CoreSort) (env : Env M)
      (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
      {source target : List Term} {rule : StepRule} {sourceSorts targetSorts : List CoreSort}
      (hSourceFragment : Term.RewriteFragmentList higherOrder source)
      (hTargetFragment : Term.RewriteFragmentList higherOrder target)
      (hSource : Term.inferSortListWith bound source = some sourceSorts)
      (hTarget : Term.inferSortListWith bound target = some targetSorts)
      (hStep : rewriteOnceTermList? config source = some (rule, target)) :
      ListSemanticallyEqual env source target := by
    cases source with
    | nil => simp [rewriteOnceTermList?] at hStep
    | cons term rest =>
        simp only [Term.RewriteFragmentList, or_and_left, Term.foolFragmentList, Bool.and_eq_true] at hSourceFragment
        obtain ⟨sourceSort, sourceRestSorts, rfl, hSourceTerm, hSourceRest⟩ :=
          inferSortListWith_cons_parts hSource
        simp only [rewriteOnceTermList?] at hStep
        cases hTermRewrite : rewriteOnceTerm? config term with
        | some value =>
            rcases value with ⟨childRule, term'⟩
            simp [hTermRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            simp only [Term.RewriteFragmentList, or_and_left, Term.foolFragmentList, Bool.and_eq_true] at hTargetFragment
            obtain ⟨targetSort, targetRestSorts, rfl, hTargetTerm, hTargetRest⟩ :=
              inferSortListWith_cons_parts hTarget
            have hTermSem :=
              Term.rewriteOnceTerm?_of_root semantics bound env hBound hFree
                hSourceFragment.1 hTargetFragment.1
                hSourceTerm hTargetTerm hTermRewrite
            change
              Term.eval env term :: rest.map (Term.eval env) =
                Term.eval env term' :: rest.map (Term.eval env)
            rw [hTermSem]
        | none =>
            simp [hTermRewrite] at hStep
            cases hRestRewrite : rewriteOnceTermList? config rest with
            | none => simp [hRestRewrite] at hStep
            | some value =>
                rcases value with ⟨childRule, rest'⟩
                simp [hRestRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                simp only [Term.RewriteFragmentList, or_and_left, Term.foolFragmentList, Bool.and_eq_true] at hTargetFragment
                obtain ⟨targetSort, targetRestSorts, rfl, hTargetTerm, hTargetRest⟩ :=
                  inferSortListWith_cons_parts hTarget
                have hRestSem :=
                  Term.rewriteOnceTermList?_of_root semantics bound env hBound hFree
                    hSourceFragment.2 hTargetFragment.2
                    hSourceRest hTargetRest hRestRewrite
                change
                  Term.eval env term :: rest.map (Term.eval env) =
                    Term.eval env term :: rest'.map (Term.eval env)
                rw [hRestSem]
end

end YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
