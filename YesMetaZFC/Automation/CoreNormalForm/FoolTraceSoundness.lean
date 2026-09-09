import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness
/-!
# FOOL-only normalization trace soundness
本模块在公共 normalization trace/checker 之上建立纯 FOOL 语义回放。与完整的
`FoolLambdaTraceSoundness` 不同，这里的可信边界显式拒绝原生 `apply/lam`，并固定
使用 `Config.foolOnly`，因此模型只需提供 `FoolContract`。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
universe x
namespace Term
theorem eval_mem_of_inferSortWith_fool {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) : ∀ (term : Term) (sort : CoreSort), Term.foolFragment term = true → Term.inferSortWith bound term = some sort → M.sortInterp sort (Term.eval env term) := by
  intro term sort hFragment hSort
  exact eval_mem_of_inferSortWith_fragment contract (HigherOrderTyping.fool M)
    bound env hBound hFree term sort (Or.inr hFragment) hSort

theorem eval_eq_of_inferred_bool_holds_iff_fool {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (left right : Term)
    (hLeftFragment : Term.foolFragment left = true) (hRightFragment : Term.foolFragment right = true) (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) (hHolds :
    M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) : SemanticallyEqual env left right :=
  (contract.bool_extensionality _ _ (eval_mem_of_inferSortWith_fool contract bound env hBound hFree left .bool hLeftFragment hLeft)
    (eval_mem_of_inferSortWith_fool contract bound env hBound hFree right .bool hRightFragment hRight)).mpr hHolds
theorem rewriteRootTerm?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Term} {rule :
    StepRule} {resultSort : CoreSort} (hSourceFragment : Term.foolFragment source = true) (hTargetFragment : Term.foolFragment target = true) (hSource : Term.inferSortWith bound source = some resultSort) (hTarget :
    Term.inferSortWith bound target = some resultSort) (hStep : rewriteRootTerm? Config.foolOnly source = some (rule, target)) : SemanticallyEqual env source target := by
  cases source with
  | apply fn argument => simp [rewriteRootTerm?, Config.foolOnly] at hStep
  | notE body =>
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases body <;> simp at hStep
      next value =>
        rcases hStep with ⟨rfl, rfl⟩
        have hResult : resultSort = .bool := (inferSortWith_notE_parts hSource).1
        subst resultSort
        apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
          hBound hFree
        · exact hSourceFragment
        · exact hTargetFragment
        · exact hSource
        · exact hTarget
        · simp only [Term.eval, contract.not_holds, contract.bool_holds]
          cases value <;> simp
      next formula =>
        rcases hStep with ⟨rfl, rfl⟩
        cases hFormula : Formula.checkWith bound formula <;>
          simp [Term.inferSortWith, hFormula] at hSource
        subst resultSort
        apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
          hBound hFree
        · exact hSourceFragment
        · exact hTargetFragment
        · simp [Term.inferSortWith, hFormula]
        · exact hTarget
        · simp only [Term.eval, contract.not_holds, contract.quote_holds, Formula.eval]
  | andE left right =>
      have hSort : resultSort = .bool := inferSortWith_andE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.andE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases left <;> cases right <;>
        simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.and_holds, contract.bool_holds, contract.quote_holds] <;>
        try cases ‹Bool› <;>
        simp_all <;>
        try (split at hStep <;> simp_all)
      all_goals
        try (rcases hStep with ⟨_, hTargetEq⟩ <;> simp_all)
      all_goals
        grind [Term.eval, Formula.eval, contract.and_holds, contract.bool_holds, contract.quote_holds]
  | orE left right =>
      have hSort : resultSort = .bool := inferSortWith_orE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.orE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases left <;> cases right <;>
        simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.or_holds, contract.bool_holds, contract.quote_holds] <;>
        try cases ‹Bool› <;>
        simp_all <;>
        try (split at hStep <;> simp_all)
      all_goals
        grind [Term.eval, Formula.eval, contract.or_holds, contract.bool_holds, contract.quote_holds]
  | impE left right =>
      have hSort : resultSort = .bool := inferSortWith_impE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.impE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      cases left <;> cases right <;>
        simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.imp_holds, contract.not_holds, contract.bool_holds, contract.quote_holds] <;>
        try cases ‹Bool› <;>
        simp_all <;>
        try (split at hStep <;> simp_all)
      all_goals
        grind [Term.eval, Formula.eval, contract.imp_holds, contract.not_holds, contract.bool_holds, contract.quote_holds]
  | iffE left right =>
      have hSort : resultSort = .bool := inferSortWith_iffE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.iffE left right) target
        hSourceFragment hTargetFragment hSource hTarget
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
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
  | quote formula =>
      have hSort : resultSort = .bool := inferSortWith_quote_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
        hBound hFree (.quote formula) target
        hSourceFragment hTargetFragment hSource hTarget
      cases formula <;>
        simp [rewriteRootTerm?, Config.foolOnly] at hStep <;>
        grind [Term.eval, Formula.eval, contract.quote_holds, contract.bool_holds]
  | lam domain codomain body => simp [rewriteRootTerm?, Config.foolOnly] at hStep
  | ite sort condition thenTerm elseTerm =>
      simp only [rewriteRootTerm?, Config.foolOnly] at hStep
      by_cases hTrue : condition = .trueE
      · subst condition
        simp at hStep
        rcases hStep with ⟨_, hTargetEq⟩
        subst target
        change Term.eval env (.ite sort .trueE thenTerm elseTerm) =
          Term.eval env thenTerm
        rw [Term.eval_ite contract]
        simp [Formula.Satisfies, Formula.eval]
      · by_cases hFalse : condition = .falseE
        · subst condition
          simp at hStep
          rcases hStep with ⟨_, hTargetEq⟩
          subst target
          change Term.eval env (.ite sort .falseE thenTerm elseTerm) =
            Term.eval env elseTerm
          rw [Term.eval_ite contract]
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
            rw [Term.eval_ite contract]
            by_cases hCondition : Formula.Satisfies env condition <;>
              simp [hCondition]
          · cases sort with
            | object | prop | named | arrow => simp [hEqual] at hStep
            | bool =>
                have hResult : resultSort = .bool :=
                  inferSortWith_ite_eq_declared hSource
                subst resultSort
                apply eval_eq_of_inferred_bool_holds_iff_fool contract bound env
                  hBound hFree (.ite .bool condition thenTerm elseTerm) target
                  hSourceFragment hTargetFragment hSource hTarget
                by_cases hThenTrue : thenTerm = .bool true
                · by_cases hElseFalse : elseTerm = .bool false
                  · subst thenTerm
                    subst elseTerm
                    simp [hEqual] at hStep
                    rcases hStep with ⟨_, hTargetEq⟩
                    subst target
                    by_cases hCondition : Formula.Satisfies env condition <;>
                      simp only [Formula.Satisfies] at hCondition <;>
                      simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.quote_holds, contract.bool_holds]
                  · subst thenTerm
                    simp [hEqual] at hStep
                    rcases hStep with ⟨_, hTargetEq⟩
                    subst target
                    by_cases hCondition : Formula.Satisfies env condition <;>
                      simp only [Formula.Satisfies] at hCondition <;>
                      simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.or_holds, contract.quote_holds, contract.bool_holds]
                · by_cases hThenFalse : thenTerm = .bool false
                  · by_cases hElseTrue : elseTerm = .bool true
                    · subst thenTerm
                      subst elseTerm
                      simp [hEqual] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract, Term.eval, Formula.eval, Formula.Satisfies, hCondition, contract.quote_holds, contract.bool_holds]
                    · subst thenTerm
                      simp [hEqual] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract, Term.eval, Formula.eval, Formula.Satisfies, hCondition, contract.and_holds, contract.quote_holds, contract.bool_holds]
                  · by_cases hElseTrue : elseTerm = .bool true
                    · subst elseTerm
                      simp [hEqual] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.imp_holds, contract.quote_holds, contract.bool_holds]
                    · by_cases hElseFalse : elseTerm = .bool false
                      · subst elseTerm
                        simp [hEqual] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition, contract.and_holds, contract.quote_holds, contract.bool_holds]
                      · simp [hEqual, hThenTrue, hThenFalse, hElseTrue, hElseFalse] at hStep
  | bvar => simp [rewriteRootTerm?] at hStep
  | fvar => simp [rewriteRootTerm?] at hStep
  | app => simp [rewriteRootTerm?] at hStep
  | bool => simp [rewriteRootTerm?] at hStep
theorem rewriteRootTerm?_fool_sound_of_typed {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Term}
    {rule : StepRule} {sourceSort targetSort : CoreSort} (hSourceFragment : Term.foolFragment source = true) (hTargetFragment : Term.foolFragment target = true) (hSource : Term.inferSortWith bound source = some
    sourceSort) (hTarget : Term.inferSortWith bound target = some targetSort) (hStep : rewriteRootTerm? Config.foolOnly source = some (rule, target)) : SemanticallyEqual env source target := by
  cases source with
  | apply fn argument => simp [Term.foolFragment] at hSourceFragment
  | lam domain codomain body => simp [Term.foolFragment] at hSourceFragment
  | notE body =>
      rcases inferSortWith_notE_parts hSource with ⟨rfl, hBody⟩
      have hTargetBool :=
        rewriteRootNot_target_bool hBody hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | andE left right =>
      rcases inferSortWith_andE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootAnd_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | orE left right =>
      rcases inferSortWith_orE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootOr_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | impE left right =>
      rcases inferSortWith_impE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootImp_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | iffE left right =>
      rcases inferSortWith_iffE_parts hSource with ⟨rfl, hLeft, hRight⟩
      have hTargetBool := rewriteRootIff_target_bool hLeft hRight hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | quote formula =>
      rcases inferSortWith_quote_parts hSource with ⟨rfl, hFormula⟩
      have hTargetBool := rewriteRootQuote_target_bool hFormula hStep
      have hTargetSort : targetSort = .bool :=
        inferSortWith_unique hTarget hTargetBool
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | ite declared condition thenTerm elseTerm =>
      rcases inferSortWith_ite_parts hSource with
        ⟨rfl, hCondition, hThen, hElse⟩
      have hTargetDeclared :=
        rewriteRootIte_target_sort hCondition hThen hElse hStep
      have hTargetSort : targetSort = sourceSort :=
        inferSortWith_unique hTarget hTargetDeclared
      subst targetSort
      exact rewriteRootTerm?_fool_sound contract bound env hBound hFree
        hSourceFragment hTargetFragment hSource hTarget hStep
  | bvar => simp [rewriteRootTerm?] at hStep
  | fvar => simp [rewriteRootTerm?] at hStep
  | app => simp [rewriteRootTerm?] at hStep
  | bool => simp [rewriteRootTerm?] at hStep
end Term
namespace Formula
theorem satisfies_boolEquality_iff_fool {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) (left right : Term)
    (hLeftFragment : Term.foolFragment left = true) (hRightFragment : Term.foolFragment right = true) (hLeft : Term.inferSortWith bound left = some .bool) (hRight : Term.inferSortWith bound right = some .bool) :
    Formula.Satisfies env (.equal .bool left right) ↔ (M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) := by
  have hLeftMem :=
    Term.eval_mem_of_inferSortWith_fool contract bound env hBound hFree
      left .bool hLeftFragment hLeft
  have hRightMem :=
    Term.eval_mem_of_inferSortWith_fool contract bound env hBound hFree
      right .bool hRightFragment hRight
  simpa only [Formula.Satisfies, Formula.eval] using
    contract.bool_extensionality _ _ hLeftMem hRightMem
theorem rewriteRootFormula?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Formula} {rule :
    StepRule} (hSourceFragment : Formula.foolFragment source = true) (_hTargetFragment : Formula.foolFragment target = true) (hSource : Formula.checkWith bound source = true) (_hTarget : Formula.checkWith bound target =
    true) (hStep : rewriteRootFormula? Config.foolOnly source = some (rule, target)) : SemanticallyEquivalent env source target := by
  cases source with
  | trueE => simp [rewriteRootFormula?] at hStep
  | falseE => simp [rewriteRootFormula?] at hStep
  | atom => simp [rewriteRootFormula?] at hStep
  | equal sort left right =>
      simp only [Formula.foolFragment, Bool.and_eq_true] at hSourceFragment
      have hSorts := inferSortWith_of_check_equal hSource
      by_cases hRefl : SyntaxEq.termEq left right = true
      · have hTerms : left = right := SyntaxEq.termEq_eq_true.mp hRefl
        subst right
        simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · cases sort with
        | arrow domain codomain => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        | bool =>
            have hBool :=
              satisfies_boolEquality_iff_fool contract bound env hBound hFree
                left right hSourceFragment.1 hSourceFragment.2
                hSorts.1 hSorts.2
            simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
            cases left <;> cases right <;>
              try cases ‹Bool› <;> try cases ‹Bool›
            all_goals
              rcases hStep with ⟨_, rfl⟩
              simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.bool_holds, contract.quote_holds] at hBool ⊢
            all_goals exact hBool
        | object => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        | prop => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
        | named => simp [rewriteRootFormula?, Config.foolOnly, hRefl] at hStep
  | boolTerm term =>
      simp only [Formula.foolFragment] at hSourceFragment
      cases term with
      | bool value =>
          cases value <;>
            simp [rewriteRootFormula?, Config.foolOnly] at hStep <;>
            rcases hStep with ⟨_, rfl⟩ <;>
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.bool_holds]
      | notE body =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.not_holds]
      | andE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.and_holds]
      | orE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.or_holds]
      | impE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.imp_holds]
      | iffE left right =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.iff_holds]
      | quote formula =>
          simp [rewriteRootFormula?, Config.foolOnly] at hStep
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval, contract.quote_holds]
      | ite sort condition thenTerm elseTerm =>
          cases sort <;> simp [rewriteRootFormula?, Config.foolOnly] at hStep
          next =>
            rcases hStep with ⟨_, rfl⟩
            by_cases hCondition : Formula.Satisfies env condition <;>
              simp only [Formula.Satisfies] at hCondition <;>
              simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval, Term.eval_ite contract, hCondition]
      | bvar => simp [rewriteRootFormula?, Config.foolOnly] at hStep
      | fvar => simp [rewriteRootFormula?, Config.foolOnly] at hStep
      | app => simp [rewriteRootFormula?, Config.foolOnly] at hStep
      | apply => simp [Term.foolFragment] at hSourceFragment
      | lam => simp [Term.foolFragment] at hSourceFragment
  | neg body =>
      cases body <;>
        simp [rewriteRootFormula?, Config.foolOnly] at hStep
      all_goals
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | imp left right
  | conj left right
  | disj left right
  | iffE left right =>
      by_cases hEqual : SyntaxEq.formulaEq left right = true
      · have hFormulas : left = right := SyntaxEq.formulaEq_eq_true.mp hEqual
        subst right
        cases left <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep <;>
          rcases hStep with ⟨_, rfl⟩ <;>
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · cases left <;> cases right <;>
          simp [rewriteRootFormula?, Config.foolOnly, hEqual] at hStep
        all_goals
          rcases hStep with ⟨_, rfl⟩
          simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | forallE sort body =>
      cases body <;>
        simp [rewriteRootFormula?, Config.foolOnly] at hStep
      rcases hStep with ⟨_, rfl⟩
      simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
  | existsE sort body =>
      cases body <;>
        simp [rewriteRootFormula?, Config.foolOnly] at hStep
      rcases hStep with ⟨_, rfl⟩
      simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
end Formula
open _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Formula _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics.Term
namespace FoolContract
/-- FOOL 实例保持原片段 guard；它不要求高阶模型合同。 -/
theorem rootRewriteSemantics {M : Model} (contract : FoolContract M) :
    RootRewriteSemantics M Config.foolOnly False where
  term bound env hBound hFree _ _ _ _ _ hSourceFragment hTargetFragment hSource hTarget hStep :=
    Term.rewriteRootTerm?_fool_sound_of_typed contract bound env hBound hFree
      (hSourceFragment.resolve_left id) (hTargetFragment.resolve_left id) hSource hTarget hStep
  formula bound env hBound hFree _ _ _ hSourceFragment hTargetFragment hSource hTarget hStep :=
    Formula.rewriteRootFormula?_fool_sound contract bound env hBound hFree
      (hSourceFragment.resolve_left id) (hTargetFragment.resolve_left id) hSource hTarget hStep
  lambda_congr hHigher := False.elim hHigher
end FoolContract

theorem Formula.rewriteOnceFormula?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target :
    Formula} {rule : StepRule} (hSourceFragment : Formula.foolFragment source = true) (hTargetFragment : Formula.foolFragment target = true) (hSource : Formula.checkWith bound source = true) (hTarget :
    Formula.checkWith bound target = true) (hStep : rewriteOnceFormula? Config.foolOnly source = some (rule, target)) : SemanticallyEquivalent env source target := by
  exact Formula.rewriteOnceFormula?_of_root contract.rootRewriteSemantics bound env hBound hFree
    (Or.inr hSourceFragment) (Or.inr hTargetFragment) hSource hTarget hStep

theorem Term.rewriteOnceTerm?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : Term} {rule
    : StepRule} {sourceSort targetSort : CoreSort} (hSourceFragment : Term.foolFragment source = true) (hTargetFragment : Term.foolFragment target = true) (hSource : Term.inferSortWith bound source = some sourceSort)
    (hTarget : Term.inferSortWith bound target = some targetSort) (hStep : rewriteOnceTerm? Config.foolOnly source = some (rule, target)) : SemanticallyEqual env source target := by
  exact Term.rewriteOnceTerm?_of_root contract.rootRewriteSemantics bound env hBound hFree
    (Or.inr hSourceFragment) (Or.inr hTargetFragment) hSource hTarget hStep

theorem Term.rewriteOnceTermList?_fool_sound {M : Model} (contract : FoolContract M) (bound : List CoreSort) (env : Env M) (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) {source target : List
    Term} {rule : StepRule} {sourceSorts targetSorts : List CoreSort} (hSourceFragment : Term.foolFragmentList source = true) (hTargetFragment : Term.foolFragmentList target = true) (hSource : Term.inferSortListWith
    bound source = some sourceSorts) (hTarget : Term.inferSortListWith bound target = some targetSorts) (hStep : rewriteOnceTermList? Config.foolOnly source = some (rule, target)) : ListSemanticallyEqual env source
    target := by
  exact Term.rewriteOnceTermList?_of_root contract.rootRewriteSemantics bound env hBound hFree
    (Or.inr hSourceFragment) (Or.inr hTargetFragment) hSource hTarget hStep

namespace Formula
def FoolSatisfiable (formula : Formula) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Nonempty (FoolContract M) ∧
    Env.RespectsFree env ∧ Formula.Satisfies env formula
end Formula
namespace Step
theorem sound_of_foolCheck {M : Model} (contract : FoolContract M) (env : Env M) (hFree : Env.RespectsFree env) (step : Step) (hCheck : step.foolCheck = true) : TraceExpr.SemanticallyEquivalent env step.before step.after := by
  have hBound : Env.RespectsBound [] env := Env.respectsBound_nil env
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Step.foolCheck, Bool.and_eq_true] at hCheck
  have hBeforeFragment := hCheck.1.1
  have hAfterFragment := hCheck.1.2
  have hStepCheck := hCheck.2
  rcases step with ⟨stepRule, before, after⟩
  unfold _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Step.check at hStepCheck
  rcases Bool.and_eq_true_iff.mp hStepCheck with ⟨hChecks, hRewrite⟩
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
                  cases hStep :
                      rewriteOnceTerm? Config.foolOnly source with
                  | none => simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
                  | some value =>
                      rcases value with ⟨rule, rewritten⟩
                      simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq, SyntaxEq.termEq_eq_true] at hRewrite
                      rcases hRewrite with ⟨_, hTarget⟩
                      subst target
                      simpa [TraceExpr.SemanticallyEquivalent] using
                        Term.rewriteOnceTerm?_fool_sound contract [] env
                          hBound hFree hBeforeFragment hAfterFragment
                          hSourceSort hTargetSort hStep
      | formula target =>
          cases hStep : rewriteOnceTerm? Config.foolOnly source <;>
            simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq] at hRewrite
  | formula source =>
      cases after with
      | term target =>
          cases hStep : rewriteOnceFormula? Config.foolOnly source <;>
            simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq] at hRewrite
      | formula target =>
          cases hStep :
              rewriteOnceFormula? Config.foolOnly source with
          | none => simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
          | some value =>
              rcases value with ⟨rule, rewritten⟩
              simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq, SyntaxEq.formulaEq_eq_true] at hRewrite
              rcases hRewrite with ⟨_, hTarget⟩
              subst target
              exact
                Formula.rewriteOnceFormula?_fool_sound contract [] env
                  hBound hFree hBeforeFragment hAfterFragment (by simpa [TraceExpr.check?, Formula.check?] using hBefore)
                    (by simpa [TraceExpr.check?, Formula.check?] using hAfter)
                    hStep
end Step
namespace Trace
theorem replay?_fool_sound {M : Model} (contract : FoolContract M) (env : Env M) (hFree : Env.RespectsFree env) (steps : List Step) (source target : TraceExpr) (hSteps : steps.all Step.foolCheck = true) (hReplay : _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay? Config.foolOnly source steps = some target) : TraceExpr.SemanticallyEquivalent env source target := by
  induction steps generalizing source with
  | nil =>
      simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      subst target
      exact TraceExpr.semanticallyEquivalent_refl env source
  | cons step rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hSteps
      simp only
        [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      by_cases hLink : (TraceExpr.eq source step.before && step.check Config.foolOnly) = true
      · simp [hLink] at hReplay
        have hLinkParts := Bool.and_eq_true_iff.mp hLink
        have hSource : source = step.before :=
          TraceExpr.eq_eq_true.mp hLinkParts.1
        have hStep :
            TraceExpr.SemanticallyEquivalent env step.before step.after :=
          Step.sound_of_foolCheck contract env hFree step hSteps.1
        have hRest :
            TraceExpr.SemanticallyEquivalent env step.after target :=
          ih step.after hSteps.2 hReplay
        subst source
        exact TraceExpr.semanticallyEquivalent_trans hStep hRest
      · simp [hLink] at hReplay
theorem sound_of_foolCheck {M : Model} (contract : FoolContract M) (env : Env M) (hFree : Env.RespectsFree env) (trace : Trace) (hCheck : trace.foolCheck = true) : TraceExpr.SemanticallyEquivalent env trace.source trace.target := by
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.foolCheck, Bool.and_eq_true] at hCheck
  have hSteps := hCheck.1.2
  have hStepsList :
      trace.steps.toList.all Step.foolCheck = true := by
    simpa only [Array.all_toList] using hSteps
  have hTrace := hCheck.2
  unfold _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.check at hTrace
  rcases Bool.and_eq_true_iff.mp hTrace with ⟨_, hReplayCheck⟩
  cases hReplay :
      _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?
        Config.foolOnly trace.source trace.steps.toList with
  | none => simp [hReplay] at hReplayCheck
  | some replayTarget =>
      have hEndpoints := Bool.and_eq_true_iff.mp (by
        simpa [hReplay] using hReplayCheck)
      have hTarget : replayTarget = trace.target :=
        TraceExpr.eq_eq_true.mp hEndpoints.1
      subst replayTarget
      exact replay?_fool_sound contract env hFree trace.steps.toList
        trace.source trace.target hStepsList hReplay
end Trace
end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
