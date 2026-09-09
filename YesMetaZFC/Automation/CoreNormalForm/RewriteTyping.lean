import YesMetaZFC.Automation.CoreNormalForm.AntiPrenexSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaSoundness

/-!
# 规范化改写的类型与环境接口

局部规则和外层语法递归共用类型分解与环境提升；这些接口不依赖具体模型合同。
-/

namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
def Term.RewriteFragment (higherOrder : Prop) (term : Term) : Prop :=
  higherOrder ∨ Term.foolFragment term = true

def Term.RewriteFragmentList (higherOrder : Prop) (terms : List Term) : Prop :=
  higherOrder ∨ Term.foolFragmentList terms = true

def Formula.RewriteFragment (higherOrder : Prop) (formula : Formula) : Prop :=
  higherOrder ∨ Formula.foolFragment formula = true

namespace Env
def RespectsBound {M : Model} (bound : List CoreSort) (env : Env M) : Prop :=
  ∀ index sort, TypeCheck.lookupBound? bound index = some sort →
    M.sortInterp sort (env.boundVal index)
def RespectsFree {M : Model} (env : Env M) : Prop :=
  ∀ sort id, M.sortInterp sort (env.freeVal sort id)
theorem respectsBound_push {M : Model} {bound : List CoreSort} {env : Env M} (hBound : RespectsBound bound env) {sort : CoreSort} {value : M.Carrier} (hValue : M.sortInterp sort value) : RespectsBound (sort :: bound) (env.push value) := by
  intro index target hLookup
  cases index with
  | zero =>
      simp only [TypeCheck.lookupBound?] at hLookup
      cases hLookup
      exact hValue
  | succ previous =>
      simp only [TypeCheck.lookupBound?, Env.push_bound_succ] at hLookup ⊢
      exact hBound previous target hLookup
theorem respectsFree_push {M : Model} {env : Env M} (hFree : RespectsFree env) (value : M.Carrier) : RespectsFree (env.push value) := by
  intro sort id
  simpa only [Env.push_free] using hFree sort id
theorem insertAt_zero_eq_push {M : Model} (env : Env M) (value : M.Carrier) : env.insertAt 0 value = env.push value := by
  cases env with
  | mk boundValue freeValue =>
      simp only [Env.insertAt, Env.push]
      congr 1
      funext index
      cases index <;> simp
theorem drop_zero_eq {M : Model} (env : Env M) : env.drop 0 = env := by
  cases env with
  | mk boundValue freeValue =>
      simp only [Env.drop]
      congr 1
end Env

theorem coreSort_eq_arrow_of_arrow?_eq_some {sort domain codomain : CoreSort} (hArrow : _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.CoreSort.arrow? sort = some (domain, codomain)) : sort = .arrow domain codomain := by
  cases sort with
  | object | bool | prop | named => simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.CoreSort.arrow?] at hArrow
  | arrow actualDomain actualCodomain =>
      simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.CoreSort.arrow?] at hArrow
      rcases hArrow with ⟨rfl, rfl⟩
      rfl

theorem coreSort_eq_of_beq_eq_true {left right : CoreSort} (hEqual : (left == right) = true) : left = right := by exact beq_iff_eq.mp hEqual

namespace Term
def SemanticallyEqual {M : Model} (env : Env M) (left right : Term) : Prop :=
  Term.eval env left = Term.eval env right

def ListSemanticallyEqual {M : Model} (env : Env M) (left right : List Term) : Prop :=
  left.map (Term.eval env) = right.map (Term.eval env)

theorem inferSortWith_apply_parts {bound : List CoreSort} {fn arg : Term} {result : CoreSort} (hSort : Term.inferSortWith bound (.apply fn arg) = some result) : ∃ domain, Term.inferSortWith bound fn = some (.arrow domain result) ∧ Term.inferSortWith bound arg = some domain := by
  cases hFn : Term.inferSortWith bound fn <;>
    cases hArg : Term.inferSortWith bound arg <;>
    simp [Term.inferSortWith, hFn, hArg] at hSort
  next fnSort argSort =>
    cases fnSort with
    | object | bool | prop | named =>
        simp only
          [_root_.YesMetaZFC.Automation.CoreSyntax.CoreSort.arrow?] at hSort
        contradiction
    | arrow domain codomain =>
        simp only
          [_root_.YesMetaZFC.Automation.CoreSyntax.CoreSort.arrow?] at hSort
        split at hSort
        next hDomain =>
          subst argSort
          simp at hSort
          subst result
          exact ⟨domain, rfl, rfl⟩
        next =>
          contradiction

theorem inferSortWith_notE_parts {bound : List CoreSort} {body : Term} {result : CoreSort} (hSort : Term.inferSortWith bound (.notE body) = some result) : result = .bool ∧ Term.inferSortWith bound body = some .bool := by
  cases hBody : Term.inferSortWith bound body <;>
    simp [Term.inferSortWith, hBody] at hSort
  subst_vars
  simp_all

theorem inferSortWith_andE_parts {bound : List CoreSort} {left right : Term} {result : CoreSort} (hSort : Term.inferSortWith bound (.andE left right) = some result) : result = .bool ∧ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool := by
  cases hLeft : Term.inferSortWith bound left <;>
    cases hRight : Term.inferSortWith bound right <;>
    simp [Term.inferSortWith, hLeft, hRight] at hSort
  subst_vars
  simp_all

theorem inferSortWith_orE_parts {bound : List CoreSort} {left right : Term} {result : CoreSort} (hSort : Term.inferSortWith bound (.orE left right) = some result) : result = .bool ∧ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool :=
  inferSortWith_andE_parts (by
    simpa only [Term.inferSortWith] using hSort)

theorem inferSortWith_impE_parts {bound : List CoreSort} {left right : Term} {result : CoreSort} (hSort : Term.inferSortWith bound (.impE left right) = some result) : result = .bool ∧ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool :=
  inferSortWith_andE_parts (by
    simpa only [Term.inferSortWith] using hSort)

theorem inferSortWith_iffE_parts {bound : List CoreSort} {left right : Term} {result : CoreSort} (hSort : Term.inferSortWith bound (.iffE left right) = some result) : result = .bool ∧ Term.inferSortWith bound left = some .bool ∧ Term.inferSortWith bound right = some .bool :=
  inferSortWith_andE_parts (by
    simpa only [Term.inferSortWith] using hSort)

theorem inferSortWith_quote_parts {bound : List CoreSort} {formula : Formula} {result : CoreSort} (hSort : Term.inferSortWith bound (.quote formula) = some result) : result = .bool ∧ Formula.checkWith bound formula = true := by
  cases hCheck : Formula.checkWith bound formula <;>
    simp [Term.inferSortWith, hCheck] at hSort
  subst_vars
  simp_all

theorem inferSortWith_lam_parts {bound : List CoreSort} {domain codomain result : CoreSort} {body : Term} (hSort : Term.inferSortWith bound (.lam domain codomain body) = some result) : result = .arrow domain codomain ∧ Term.inferSortWith (domain :: bound) body = some codomain := by
  cases hBody : Term.inferSortWith (domain :: bound) body <;>
    simp [Term.inferSortWith, hBody] at hSort
  subst_vars
  simp_all

theorem inferSortWith_ite_parts {bound : List CoreSort} {declared result : CoreSort} {condition : Formula} {thenTerm elseTerm : Term} (hSort : Term.inferSortWith bound (.ite declared condition thenTerm elseTerm) = some result) : result = declared ∧ Formula.checkWith bound condition = true ∧ Term.inferSortWith bound thenTerm = some declared ∧ Term.inferSortWith bound elseTerm = some declared := by
  cases hCheck : Formula.checkWith bound condition <;>
    simp [Term.inferSortWith, hCheck] at hSort
  cases hThen : Term.inferSortWith bound thenTerm <;>
    cases hElse : Term.inferSortWith bound elseTerm <;>
    simp [hThen, hElse] at hSort
  subst_vars
  simp_all

theorem inferSortWith_app_parts {bound : List CoreSort} {symbol : FunctionSymbol} {args : List Term} {result : CoreSort} (hSort : Term.inferSortWith bound (.app symbol args) = some result) : result = symbol.outputSort ∧ ∃ sorts, Term.inferSortListWith bound args = some sorts := by
  by_cases hArity : !symbol.arityOk || args.length != symbol.arity
  · simp [Term.inferSortWith, hArity] at hSort
  · cases hArgs : Term.inferSortListWith bound args with
    | none => simp [Term.inferSortWith, hArity, hArgs] at hSort
    | some sorts =>
        simp [Term.inferSortWith, hArity, hArgs] at hSort
        exact ⟨hSort.2.symm, sorts, rfl⟩

theorem inferSortListWith_cons_parts {bound : List CoreSort} {term : Term} {rest : List Term} {sorts : List CoreSort} (hSorts : Term.inferSortListWith bound (term :: rest) = some sorts) : ∃ sort restSorts, sorts = sort :: restSorts ∧ Term.inferSortWith bound term = some sort ∧ Term.inferSortListWith bound rest = some restSorts := by
  cases hTerm : Term.inferSortWith bound term <;>
    cases hRest : Term.inferSortListWith bound rest <;>
    simp [Term.inferSortListWith, hTerm, hRest] at hSorts
  subst_vars
  exact ⟨_, _, rfl, rfl, rfl⟩

end Term
namespace Formula
def SemanticallyEquivalent {M : Model} (env : Env M) (left right : Formula) : Prop :=
  Formula.Satisfies env left ↔ Formula.Satisfies env right

theorem inferSortListWith_of_check_atom {bound : List CoreSort} {predicate : PredicateSymbol} {args : List Term} (hCheck : Formula.checkWith bound (.atom predicate args) = true) : ∃ sorts, Term.inferSortListWith bound args = some sorts := by
  by_cases hArity : !predicate.arityOk || args.length != predicate.arity
  · simp [Formula.checkWith, hArity] at hCheck
  · cases hArgs : Term.inferSortListWith bound args with
    | none => simp [Formula.checkWith, hArity, hArgs] at hCheck
    | some sorts => exact ⟨sorts, rfl⟩

theorem inferSortWith_of_check_equal {bound : List CoreSort} {sort : CoreSort} {left right : Term} (hCheck : Formula.checkWith bound (.equal sort left right) = true) : Term.inferSortWith bound left = some sort ∧ Term.inferSortWith bound right = some sort := by
  simp only [Formula.checkWith] at hCheck
  cases hLeft : Term.inferSortWith bound left <;>
    cases hRight : Term.inferSortWith bound right <;>
    simp_all [coreSort_eq_of_beq_eq_true]

theorem inferSortWith_of_check_boolTerm {bound : List CoreSort} {term : Term} (hCheck : Formula.checkWith bound (.boolTerm term) = true) : Term.inferSortWith bound term = some .bool := by
  simp only [Formula.checkWith] at hCheck
  cases hSort : Term.inferSortWith bound term <;> simp_all

theorem checkWith_of_check_neg {bound : List CoreSort} {body : Formula} (hCheck : Formula.checkWith bound (.neg body) = true) : Formula.checkWith bound body = true := by simpa only [Formula.checkWith] using hCheck

theorem checkWith_of_check_imp {bound : List CoreSort} {left right : Formula} (hCheck : Formula.checkWith bound (.imp left right) = true) : Formula.checkWith bound left = true ∧ Formula.checkWith bound right = true := by simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

theorem checkWith_of_check_conj {bound : List CoreSort} {left right : Formula} (hCheck : Formula.checkWith bound (.conj left right) = true) : Formula.checkWith bound left = true ∧ Formula.checkWith bound right = true := by simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

theorem checkWith_of_check_disj {bound : List CoreSort} {left right : Formula} (hCheck : Formula.checkWith bound (.disj left right) = true) : Formula.checkWith bound left = true ∧ Formula.checkWith bound right = true := by simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

theorem checkWith_of_check_iffE {bound : List CoreSort} {left right : Formula} (hCheck : Formula.checkWith bound (.iffE left right) = true) : Formula.checkWith bound left = true ∧ Formula.checkWith bound right = true := by simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

theorem checkWith_of_check_forallE {bound : List CoreSort} {sort : CoreSort} {body : Formula} (hCheck : Formula.checkWith bound (.forallE sort body) = true) : Formula.checkWith (sort :: bound) body = true := by simpa only [Formula.checkWith] using hCheck

theorem checkWith_of_check_existsE {bound : List CoreSort} {sort : CoreSort} {body : Formula} (hCheck : Formula.checkWith bound (.existsE sort body) = true) : Formula.checkWith (sort :: bound) body = true := by simpa only [Formula.checkWith] using hCheck

end Formula

/-- 仅在语法片段允许高阶项时，才要求应用和 λ 的类型保持。 -/
structure HigherOrderTyping (M : Model) (higherOrder : Prop) : Prop where
  apply_sort : higherOrder → ∀ domain codomain fn argument,
    M.sortInterp (.arrow domain codomain) fn → M.sortInterp domain argument →
    M.sortInterp codomain (M.applyInterp fn argument)
  lambda_sort : higherOrder → ∀ domain codomain body,
    (∀ value, M.sortInterp domain value → M.sortInterp codomain (body value)) →
    M.sortInterp (.arrow domain codomain) (M.lambdaValue domain codomain body)

theorem HigherOrderTyping.fool (M : Model) : HigherOrderTyping M False where
  apply_sort := False.elim
  lambda_sort := False.elim

theorem FoolLambdaContract.higherOrderTyping {M : Model} (contract : FoolLambdaContract M) :
    HigherOrderTyping M True where
  apply_sort _ := contract.apply_sort
  lambda_sort _ := contract.lambda_sort

/-- 类型推断的语义保持只归纳一次；FOOL 和高阶实例分别提供片段与类型合同。 -/
theorem Term.eval_mem_of_inferSortWith_fragment
    {M : Model} {higherOrder : Prop} (contract : FoolContract M)
    (higher : HigherOrderTyping M higherOrder)
    (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) :
    ∀ term sort, Term.RewriteFragment higherOrder term →
      Term.inferSortWith bound term = some sort → M.sortInterp sort (Term.eval env term)
  | .bvar annotated index, sort, _, hSort => by
      cases hLookup : TypeCheck.lookupBound? bound index with
      | none => simp [Term.inferSortWith, hLookup] at hSort
      | some expected =>
          simp [Term.inferSortWith, hLookup] at hSort
          rcases hSort with ⟨rfl, rfl⟩
          simpa only [Term.eval] using hBound index _ hLookup
  | .fvar annotated id, sort, _, hSort => by
      cases Option.some.inj hSort
      simpa only [Term.eval] using hFree annotated id
  | .app symbol arguments, sort, _, hSort => by
      obtain ⟨rfl, _⟩ := inferSortWith_app_parts hSort
      simpa only [Term.eval] using contract.function_sort symbol (arguments.map (Term.eval env))
  | .apply fn argument, sort, hFragment, hSort => by
      have hHigher : higherOrder := by
        simpa only [RewriteFragment, Term.foolFragment, Bool.false_eq_true, or_false]
          using hFragment
      obtain ⟨domain, hFn, hArgument⟩ := inferSortWith_apply_parts hSort
      simpa only [Term.eval] using higher.apply_sort hHigher domain sort _ _
        (eval_mem_of_inferSortWith_fragment contract higher bound env hBound hFree
          fn (.arrow domain sort) (Or.inl hHigher) hFn)
        (eval_mem_of_inferSortWith_fragment contract higher bound env hBound hFree
          argument domain (Or.inl hHigher) hArgument)
  | .bool value, sort, _, hSort => by
      cases Option.some.inj hSort
      simpa only [Term.eval] using contract.bool_sort value
  | .notE body, sort, hFragment, hSort => by
      obtain ⟨rfl, hBody⟩ := inferSortWith_notE_parts hSort
      simpa only [Term.eval] using contract.not_sort _
        (eval_mem_of_inferSortWith_fragment contract higher bound env hBound hFree
          body .bool hFragment hBody)
  | .andE left right, sort, hFragment, hSort
  | .orE left right, sort, hFragment, hSort
  | .impE left right, sort, hFragment, hSort
  | .iffE left right, sort, hFragment, hSort => by
      obtain ⟨rfl, hLeftSort, hRightSort⟩ :=
        inferSortWith_andE_parts (left := left) (right := right) hSort
      simp only [RewriteFragment, Term.foolFragment, Bool.and_eq_true, or_and_left]
        at hFragment
      have hLeft := eval_mem_of_inferSortWith_fragment contract higher bound env
        hBound hFree left .bool hFragment.1 hLeftSort
      have hRight := eval_mem_of_inferSortWith_fragment contract higher bound env
        hBound hFree right .bool hFragment.2 hRightSort
      simp only [Term.eval]
      first
      | exact contract.and_sort _ _ hLeft hRight
      | exact contract.or_sort _ _ hLeft hRight
      | exact contract.imp_sort _ _ hLeft hRight
      | exact contract.iff_sort _ _ hLeft hRight
  | .quote formula, sort, _, hSort => by
      obtain ⟨rfl, _⟩ := inferSortWith_quote_parts hSort
      simpa only [Term.eval] using contract.quote_sort (Formula.eval env formula).holds
  | .lam domain codomain body, sort, hFragment, hSort => by
      have hHigher : higherOrder := by
        simpa only [RewriteFragment, Term.foolFragment, Bool.false_eq_true, or_false]
          using hFragment
      obtain ⟨rfl, hBody⟩ := inferSortWith_lam_parts hSort
      simp only [Term.eval]
      apply higher.lambda_sort hHigher
      intro value hValue
      exact eval_mem_of_inferSortWith_fragment contract higher (domain :: bound)
        (env.push value) (Env.respectsBound_push hBound hValue)
        (Env.respectsFree_push hFree value) body codomain (Or.inl hHigher) hBody
  | .ite declared condition thenTerm elseTerm, sort, hFragment, hSort => by
      obtain ⟨rfl, _, hThen, hElse⟩ := inferSortWith_ite_parts hSort
      simp only [RewriteFragment, Term.foolFragment, Bool.and_eq_true, or_and_left]
        at hFragment
      simpa only [Term.eval] using contract.ite_sort sort _ _ _
        (eval_mem_of_inferSortWith_fragment contract higher bound env hBound hFree
          thenTerm sort hFragment.1.2 hThen)
        (eval_mem_of_inferSortWith_fragment contract higher bound env hBound hFree
          elseTerm sort hFragment.2 hElse)

end YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
