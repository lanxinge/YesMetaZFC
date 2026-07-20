import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness

/-!
# FOOL 公式参数定义化 soundness

本模块为 `FormulaArgumentTrace` 与 `FOOLClausePayload` 建立对象层定义扩张语义。
定义函数同时携带局部 bound 上下文和 typed 自由变量参数；其解释直接取自定义
记录中的原始公式，因此递归定义化后的 body 不会形成语义循环。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm
namespace Semantics

universe x

mutual
  /-- sort 推断成功的项一定在当前 locally nameless 上下文中良定。 -/
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

  /-- checker 接受的公式一定在当前 locally nameless 上下文中良定。 -/
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

  /-- sort 推断成功的项列表逐项在当前上下文中良定。 -/
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

namespace Term

theorem wellScopedWith_of_inferSortWith
    (bound : List CoreSort) (term : Term) (sort : CoreSort)
    (hSort : Term.inferSortWith bound term = some sort) :
    Term.wellScopedWith bound term = true :=
  termWellScopedWithOfInferSortWith bound term sort hSort

theorem wellScopedListWith_of_inferSortListWith
    (bound : List CoreSort) (terms : List Term) (sorts : List CoreSort)
    (hSorts : Term.inferSortListWith bound terms = some sorts) :
    Term.wellScopedListWith bound terms = true :=
  termListWellScopedWithOfInferSortListWith bound terms sorts hSorts

end Term

namespace Formula

theorem wellScopedWith_of_checkWith
    (bound : List CoreSort) (formula : Formula)
    (hCheck : Formula.checkWith bound formula = true) :
    Formula.wellScopedWith bound formula = true :=
  formulaWellScopedWithOfCheckWith bound formula hCheck

end Formula

namespace FormulaArgumentDefinition

/-- 从定义函数实参中恢复局部 bound 环境。 -/
def boundValueFromArgsAux {M : Model} (base : Env M) :
    List CoreSort → List M.Carrier → Nat → Nat → M.Carrier
  | [], _, fallback, _ => base.boundVal fallback
  | _ :: _, [], fallback, _ => base.boundVal fallback
  | _ :: _, value :: _, _, 0 => value
  | _ :: rest, _ :: values, fallback, offset + 1 =>
      boundValueFromArgsAux base rest values fallback offset

/-- 从定义函数实参中恢复局部 bound 环境。 -/
def boundValueFromArgs {M : Model} (base : Env M) :
    List CoreSort → List M.Carrier → Nat → M.Carrier :=
  fun contextSorts args index =>
    boundValueFromArgsAux base contextSorts args index index

/-- 从定义函数实参中按 typed 变量身份恢复自由变量。 -/
def freeValueFromArgs {M : Model} (base : Env M) :
    List FirstOrderProjection.FormulaArgumentFreeVarParam →
      List M.Carrier → CoreSort → VarId → M.Carrier
  | [], _, sort, id => base.freeVal sort id
  | _ :: _, [], sort, id => base.freeVal sort id
  | parameter :: parameters, value :: values, sort, id =>
      if parameter.sort = sort ∧ parameter.varId = id then
        value
      else
        freeValueFromArgs base parameters values sort id

/-- 用定义函数的实参重建原始公式所需环境。 -/
def envForArgs {M : Model} (base : Env M)
    (definition : FirstOrderProjection.BoolDefinition)
    (args : List M.Carrier) : Env M where
  boundVal :=
    boundValueFromArgs base definition.contextSorts args
  freeVal :=
    freeValueFromArgs base definition.freeVarParams
      (args.drop definition.contextSorts.length)

/-- 把命题反射为模型的布尔值索引。 -/
noncomputable def truthBool (proposition : Prop) : Bool :=
  @ite Bool proposition (Classical.propDecidable proposition) true false

@[simp]
theorem truthBool_eq_true_iff (proposition : Prop) :
    truthBool proposition = true ↔ proposition := by
  classical
  simp [truthBool]

/-! 环境重建的基本引理。 -/

/-- 当前环境中局部 bound 值的参数列表。 -/
def contextValues {M : Model} (env : Env M) :
    Nat → List CoreSort → List M.Carrier
  | _, [] => []
  | index, _ :: sorts =>
      env.boundVal index :: contextValues env (index + 1) sorts

/-- 定义函数实参在当前环境中的解释。 -/
def evaluatedArguments {M : Model} (env : Env M)
    (definition : FirstOrderProjection.BoolDefinition) : List M.Carrier :=
  contextValues env 0 definition.contextSorts ++
    definition.freeVarParams.map (fun parameter =>
      env.freeVal parameter.sort parameter.varId)

theorem boundValueFromArgs_contextValues_append {M : Model} (base : Env M)
    (start : Nat) (contextSorts : List CoreSort) (values : List M.Carrier)
    (fallback offset : Nat) :
    boundValueFromArgsAux base contextSorts
        (contextValues base start contextSorts ++ values) fallback offset =
      if offset < contextSorts.length then
        base.boundVal (start + offset)
      else
        base.boundVal fallback := by
  induction contextSorts generalizing start fallback offset with
  | nil =>
      simp [boundValueFromArgsAux]
  | cons sort contextSorts ih =>
      cases offset with
      | zero =>
          rfl
      | succ offset =>
          simp only [contextValues, List.length_cons]
          simpa [Nat.succ_lt_succ_iff, Nat.succ_add] using
            ih (start + 1) fallback offset

theorem boundValueFromArgs_contextValues {M : Model} (base : Env M)
    (contextSorts : List CoreSort) (index : Nat) :
    boundValueFromArgs base contextSorts
        (contextValues base 0 contextSorts) index =
      base.boundVal index := by
  simpa [boundValueFromArgs] using
    boundValueFromArgs_contextValues_append base 0 contextSorts [] index index

theorem freeValueFromArgs_params {M : Model} (base : Env M)
    (parameters : List FirstOrderProjection.FormulaArgumentFreeVarParam)
    (sort : CoreSort) (id : VarId) :
    freeValueFromArgs base parameters
        (parameters.map (fun parameter =>
          base.freeVal parameter.sort parameter.varId)) sort id =
      base.freeVal sort id := by
  induction parameters with
  | nil =>
      rfl
  | cons parameter parameters ih =>
      by_cases hSort : parameter.sort = sort
      · by_cases hId : parameter.varId = id
        · simp [freeValueFromArgs, hSort, hId]
        · simp [freeValueFromArgs, hSort, hId, ih]
      · simp [freeValueFromArgs, hSort, ih]

theorem drop_contextValues_append {M : Model} (base : Env M)
    (start : Nat) (contextSorts : List CoreSort)
    (values : List M.Carrier) :
    (contextValues base start contextSorts ++ values).drop contextSorts.length = values := by
  induction contextSorts generalizing start values with
  | nil =>
      rfl
  | cons sort contextSorts ih =>
      simp [contextValues, ih]

theorem boundValueFromArgsAux_contextValues_append_of_lookup
    {M : Model} (base env : Env M)
    (start : Nat) (contextSorts : List CoreSort) (values : List M.Carrier)
    (fallback offset : Nat) (sort : CoreSort)
    (hLookup : TypeCheck.lookupBound? contextSorts offset = some sort) :
    boundValueFromArgsAux base contextSorts
        (contextValues env start contextSorts ++ values) fallback offset =
      env.boundVal (start + offset) := by
  induction contextSorts generalizing start offset with
  | nil =>
      simp [TypeCheck.lookupBound?] at hLookup
  | cons head contextSorts ih =>
      cases offset with
      | zero =>
          simp [contextValues, boundValueFromArgsAux]
      | succ previous =>
          simp only [TypeCheck.lookupBound?] at hLookup
          simp only [contextValues, List.cons_append, boundValueFromArgsAux]
          have hResult := ih (start + 1) previous hLookup
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

theorem boundValueFromArgs_contextValues_append_of_lookup
    {M : Model} (base env : Env M)
    (contextSorts : List CoreSort) (values : List M.Carrier)
    (index : Nat) (sort : CoreSort)
    (hLookup : TypeCheck.lookupBound? contextSorts index = some sort) :
    boundValueFromArgs base contextSorts
        (contextValues env 0 contextSorts ++ values) index =
      env.boundVal index := by
  simpa [boundValueFromArgs] using
    boundValueFromArgsAux_contextValues_append_of_lookup
      base env 0 contextSorts values index index sort hLookup

theorem freeValueFromArgs_map_of_free_eq
    {M : Model} (base env : Env M)
    (parameters : List FirstOrderProjection.FormulaArgumentFreeVarParam)
    (hFree : ∀ sort id, base.freeVal sort id = env.freeVal sort id)
    (sort : CoreSort) (id : VarId) :
    freeValueFromArgs base parameters
        (parameters.map (fun parameter =>
          env.freeVal parameter.sort parameter.varId)) sort id =
      env.freeVal sort id := by
  induction parameters with
  | nil =>
      simpa [freeValueFromArgs] using hFree sort id
  | cons parameter parameters ih =>
      by_cases hSort : parameter.sort = sort
      · by_cases hId : parameter.varId = id
        · simp [freeValueFromArgs, hSort, hId]
        · simp [freeValueFromArgs, hSort, hId, ih]
      · simp [freeValueFromArgs, hSort, ih]

theorem envForArgs_evaluatedArguments {M : Model} (env : Env M)
    (definition : FirstOrderProjection.BoolDefinition) :
    envForArgs env definition (evaluatedArguments env definition) = env := by
  cases env with
  | mk boundVal freeVal =>
      cases definition with
      | mk index symbol contextSorts freeVarParams sourceFormula formula =>
          have hBound :
              boundValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  contextSorts
                    (contextValues { boundVal := boundVal, freeVal := freeVal }
                      0 contextSorts ++
                      freeVarParams.map (fun parameter =>
                        freeVal parameter.sort parameter.varId)) =
                boundVal := by
            funext index
            simpa [boundValueFromArgs] using
              boundValueFromArgs_contextValues_append
                { boundVal := boundVal, freeVal := freeVal }
                0 contextSorts
                (freeVarParams.map (fun parameter =>
                  freeVal parameter.sort parameter.varId))
                index index
          have hFree :
              freeValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  freeVarParams
                  ((contextValues { boundVal := boundVal, freeVal := freeVal }
                    0 contextSorts ++
                      freeVarParams.map (fun parameter =>
                        freeVal parameter.sort parameter.varId)).drop contextSorts.length) =
                freeVal := by
            funext sort id
            have hDrop :=
              drop_contextValues_append
                { boundVal := boundVal, freeVal := freeVal }
                0 contextSorts
                (freeVarParams.map (fun parameter =>
                  freeVal parameter.sort parameter.varId))
            rw [hDrop]
            exact freeValueFromArgs_params
              { boundVal := boundVal, freeVal := freeVal }
              freeVarParams sort id
          change
            Env.mk
                (boundValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  contextSorts
                  (contextValues { boundVal := boundVal, freeVal := freeVal }
                    0 contextSorts ++
                    freeVarParams.map (fun parameter =>
                      freeVal parameter.sort parameter.varId)))
                (freeValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  freeVarParams
                  ((contextValues { boundVal := boundVal, freeVal := freeVal }
                    0 contextSorts ++
                      freeVarParams.map (fun parameter =>
                        freeVal parameter.sort parameter.varId)).drop contextSorts.length)) =
              Env.mk boundVal freeVal
          rw [hBound, hFree]

theorem contextArgsFrom_eval {M : Model} (env : Env M)
    (index : Nat) (contextSorts : List CoreSort) :
    (FirstOrderProjection.contextArgsFrom index contextSorts).map (Term.eval env) =
      contextValues env index contextSorts := by
  induction contextSorts generalizing index with
  | nil =>
      rfl
  | cons sort contextSorts ih =>
      simp [FirstOrderProjection.contextArgsFrom, contextValues, Term.eval, ih]

theorem evaluatedArguments_eq_eval_arguments {M : Model} (env : Env M)
    (definition : FirstOrderProjection.BoolDefinition) :
    definition.arguments.map (Term.eval env) =
      evaluatedArguments env definition := by
  unfold FirstOrderProjection.BoolDefinition.arguments evaluatedArguments
  have hContext := contextArgsFrom_eval env 0 definition.contextSorts
  have hContext' :
      (FirstOrderProjection.contextArgs definition.contextSorts).map
          (Term.eval env) =
        contextValues env 0 definition.contextSorts := by
    simpa [FirstOrderProjection.contextArgs] using hContext
  rw [List.map_append, hContext']
  induction definition.freeVarParams with
  | nil =>
      rfl
  | cons parameter parameters _ =>
      simp [FirstOrderProjection.FormulaArgumentFreeVarParam.terms,
        FirstOrderProjection.FormulaArgumentFreeVarParam.term, Term.eval]

end FormulaArgumentDefinition

namespace Env

def ScopedAgreement {M : Model} (bound : List CoreSort) (left right : Env M) : Prop :=
  (∀ sort index, TypeCheck.lookupBound? bound index = some sort →
      left.boundVal index = right.boundVal index) ∧
    ∀ sort id, left.freeVal sort id = right.freeVal sort id

theorem scopedAgreement_push {M : Model}
    {bound : List CoreSort} {left right : Env M}
    (hAgreement : ScopedAgreement bound left right)
    (sort : CoreSort) (value : M.Carrier) :
    ScopedAgreement (sort :: bound) (left.push value) (right.push value) := by
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

namespace FormulaArgumentDefinition

theorem envForArgs_evaluatedArguments_scopedAgreement
    {M : Model} (base env : Env M)
    (definition : FirstOrderProjection.BoolDefinition)
    (hFree : ∀ sort id, base.freeVal sort id = env.freeVal sort id) :
    Env.ScopedAgreement definition.contextSorts
      (envForArgs base definition (evaluatedArguments env definition)) env := by
  constructor
  · intro sort index hLookup
    unfold envForArgs evaluatedArguments
    exact boundValueFromArgs_contextValues_append_of_lookup
      base env definition.contextSorts
        (definition.freeVarParams.map (fun parameter =>
          env.freeVal parameter.sort parameter.varId))
        index sort hLookup
  · intro sort id
    unfold envForArgs evaluatedArguments
    rw [drop_contextValues_append]
    exact freeValueFromArgs_map_of_free_eq
      base env definition.freeVarParams hFree sort id

end FormulaArgumentDefinition

mutual

theorem Term.eval_eq_of_scopedAgreement
    {M : Model} (bound : List CoreSort) (left right : Env M)
    (hAgreement : Env.ScopedAgreement bound left right)
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
      exact Term.evalList_eq_of_scopedAgreement
        bound left right hAgreement args hScoped.2
  | apply fn arg =>
      unfold Term.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      unfold Term.eval
      rw [Term.eval_eq_of_scopedAgreement bound left right hAgreement fn hScoped.1,
        Term.eval_eq_of_scopedAgreement bound left right hAgreement arg hScoped.2]
  | bool value =>
      unfold Term.eval
      rfl
  | notE body =>
      unfold Term.wellScopedWith at hScoped
      unfold Term.eval
      rw [Term.eval_eq_of_scopedAgreement bound left right hAgreement body hScoped]
  | andE leftTerm rightTerm
  | orE leftTerm rightTerm
  | impE leftTerm rightTerm
  | iffE leftTerm rightTerm =>
      unfold Term.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      unfold Term.eval
      rw [Term.eval_eq_of_scopedAgreement bound left right hAgreement leftTerm hScoped.1,
        Term.eval_eq_of_scopedAgreement bound left right hAgreement rightTerm hScoped.2]
  | quote formula =>
      unfold Term.wellScopedWith at hScoped
      unfold Term.eval
      congr 1
      apply propext
      exact Formula.satisfies_iff_of_scopedAgreement
        bound left right hAgreement formula hScoped
  | lam domain codomain body =>
      unfold Term.wellScopedWith at hScoped
      unfold Term.eval
      congr 1
      funext value
      exact Term.eval_eq_of_scopedAgreement
        (domain :: bound) (left.push value) (right.push value)
        (Env.scopedAgreement_push hAgreement domain value) body hScoped
  | ite sort condition thenTerm elseTerm =>
      unfold Term.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      unfold Term.eval
      congr 1
      · apply propext
        exact Formula.satisfies_iff_of_scopedAgreement
          bound left right hAgreement condition hScoped.1.1
      · exact Term.eval_eq_of_scopedAgreement
          bound left right hAgreement thenTerm hScoped.1.2
      · exact Term.eval_eq_of_scopedAgreement
          bound left right hAgreement elseTerm hScoped.2

theorem Formula.satisfies_iff_of_scopedAgreement
    {M : Model} (bound : List CoreSort) (left right : Env M)
    (hAgreement : Env.ScopedAgreement bound left right)
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
      rw [Term.evalList_eq_of_scopedAgreement
        bound left right hAgreement args hScoped.2]
  | equal sort leftTerm rightTerm =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_eq_of_scopedAgreement
          bound left right hAgreement leftTerm hScoped.1,
        Term.eval_eq_of_scopedAgreement
          bound left right hAgreement rightTerm hScoped.2]
  | boolTerm term =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_eq_of_scopedAgreement bound left right hAgreement term hScoped]
  | neg body =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      exact not_congr
        (Formula.satisfies_iff_of_scopedAgreement bound left right hAgreement body hScoped)
  | imp leftFormula rightFormula
  | conj leftFormula rightFormula
  | disj leftFormula rightFormula
  | iffE leftFormula rightFormula =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      first
      | exact imp_congr
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement rightFormula hScoped.2)
      | exact and_congr
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement rightFormula hScoped.2)
      | exact or_congr
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement rightFormula hScoped.2)
      | exact iff_congr
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement leftFormula hScoped.1)
          (Formula.satisfies_iff_of_scopedAgreement
            bound left right hAgreement rightFormula hScoped.2)
  | forallE sort body =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      constructor <;> intro h value hSort
      · exact (Formula.satisfies_iff_of_scopedAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedAgreement_push hAgreement sort value) body hScoped).mp
            (h value hSort)
      · exact (Formula.satisfies_iff_of_scopedAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedAgreement_push hAgreement sort value) body hScoped).mpr
            (h value hSort)
  | existsE sort body =>
      unfold Formula.wellScopedWith at hScoped
      simp only [Formula.Satisfies, Formula.eval]
      constructor
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_iff_of_scopedAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedAgreement_push hAgreement sort value) body hScoped).mp hBody
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_iff_of_scopedAgreement
          (sort :: bound) (left.push value) (right.push value)
          (Env.scopedAgreement_push hAgreement sort value) body hScoped).mpr hBody

theorem Term.evalList_eq_of_scopedAgreement
    {M : Model} (bound : List CoreSort) (left right : Env M)
    (hAgreement : Env.ScopedAgreement bound left right)
    (terms : List Term) (hScoped : Term.wellScopedListWith bound terms = true) :
    terms.map (Term.eval left) = terms.map (Term.eval right) := by
  cases terms with
  | nil =>
      rfl
  | cons head tail =>
      unfold Term.wellScopedListWith at hScoped
      simp only [Bool.and_eq_true] at hScoped
      simp only [List.map_cons]
      congr 1
      · exact Term.eval_eq_of_scopedAgreement
          bound left right hAgreement head hScoped.1
      · exact Term.evalList_eq_of_scopedAgreement
          bound left right hAgreement tail hScoped.2

end

namespace Formula

/-- 公开投影层收集的 typed 自由变量参数。 -/
abbrev formulaArgumentFreeVarParams :=
  FirstOrderProjection.Formula.formulaArgumentFreeVarParams

theorem satisfies_closeForall_of
    {M : Model} (_base env : Env M) (contextSorts : List CoreSort) (body : Formula)
    (hBody :
      ∀ env', (∀ sort id, env'.freeVal sort id = env.freeVal sort id) →
        Formula.Satisfies env' body) :
    Formula.Satisfies env (FirstOrderProjection.closeForall contextSorts body) := by
  induction contextSorts generalizing body with
  | nil =>
      simpa [FirstOrderProjection.closeForall] using hBody env (by intro sort id; rfl)
  | cons sort rest ih =>
      have hClosed :
          ∀ env', (∀ target id, env'.freeVal target id = env.freeVal target id) →
            Formula.Satisfies env' (.forallE sort body) := by
        intro env' hFree
        simp only [Formula.Satisfies, Formula.eval]
        intro value hSort
        exact hBody (env'.push value)
          (by
            intro target id
            simpa [Env.push] using hFree target id)
      simpa [FirstOrderProjection.closeForall] using
        ih (body := Formula.forallE sort body) hClosed

end Formula

namespace FormulaArgumentState

def introducedDefinition
    (state : FirstOrderProjection.FormulaArgumentState)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula) :
    FirstOrderProjection.BoolDefinition :=
  let freeVarParams := Formula.formulaArgumentFreeVarParams sourceFormula
  let inputSorts :=
    contextSorts ++ FirstOrderProjection.FormulaArgumentFreeVarParam.sorts freeVarParams
  {
    index := state.definitions.size
    symbol := {
      id := state.nextDefinition
      arity := inputSorts.length
      role := FunctionRole.definition
      inputSorts := inputSorts
      outputSort := CoreSort.bool
    }
    contextSorts := contextSorts
    freeVarParams := freeVarParams
    sourceFormula := sourceFormula
    formula := formula
  }

theorem introBoolDefinition_run
    (state : FirstOrderProjection.FormulaArgumentState)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula) :
    (FirstOrderProjection.introBoolDefinition contextSorts sourceFormula formula).run state =
      (
        (introducedDefinition state contextSorts sourceFormula formula).replacement,
        {
          state with
          nextDefinition := state.nextDefinition + 1
          intros := state.intros.push
            (FirstOrderProjection.FormulaArgumentIntro.ofDefinition
              (introducedDefinition state contextSorts sourceFormula formula))
          definitions := state.definitions.push
            (introducedDefinition state contextSorts sourceFormula formula)
      }) := by
  unfold FirstOrderProjection.introBoolDefinition introducedDefinition
  rfl

/-- 定义函数的编号位于统一 fresh 窗口且互不重复。 -/
def FreshFrom (cutoff : Nat) (state : FirstOrderProjection.FormulaArgumentState) : Prop :=
  (∀ definition ∈ state.definitions.toList,
      cutoff ≤ definition.symbol.id ∧ definition.symbol.id < state.nextDefinition) ∧
    state.definitions.toList.Pairwise
      (fun left right => left.symbol ≠ right.symbol) ∧
    cutoff ≤ state.nextDefinition

/-- 后态保留前态已经生成的所有定义。 -/
def DefinitionsIncluded
    (before after : FirstOrderProjection.FormulaArgumentState) : Prop :=
  ∀ definition ∈ before.definitions.toList,
    definition ∈ after.definitions.toList

theorem freshFrom_empty (cutoff : Nat) :
    FreshFrom cutoff
      ({ nextDefinition := cutoff, intros := #[], definitions := #[] } :
        FirstOrderProjection.FormulaArgumentState) := by
  simp [FreshFrom]

theorem freshDefinition_preserves
    {cutoff : Nat} {state : FirstOrderProjection.FormulaArgumentState}
    (hState : FreshFrom cutoff state)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula) :
    FreshFrom cutoff
      (FirstOrderProjection.introBoolDefinition contextSorts
        sourceFormula formula |>.run state).2 := by
  change FreshFrom cutoff
    { state with
      nextDefinition := state.nextDefinition + 1
      definitions := state.definitions.push _
      intros := state.intros.push _ }
  unfold FreshFrom at hState ⊢
  simp only [Array.toList_push, List.mem_append, List.mem_singleton,
    List.pairwise_append, List.pairwise_cons]
  rcases hState with ⟨hBounds, hPairwise, hCutoff⟩
  constructor
  · intro definition hDefinition
    rcases hDefinition with hDefinition | rfl
    · rcases hBounds definition hDefinition with ⟨hLower, hUpper⟩
      exact ⟨hLower, Nat.lt_succ_of_lt hUpper⟩
    · exact ⟨hCutoff, Nat.lt_succ_self _⟩
  · constructor
    · constructor
      · exact hPairwise
      · constructor
        · constructor <;> simp
        · intro left hLeft right hRight hEqual
          have hRightId : right.symbol.id = state.nextDefinition := by
            rw [hRight]
          have hIdEq : left.symbol.id = right.symbol.id :=
            congrArg FunctionSymbol.id hEqual
          have hUpper := (hBounds left hLeft).2
          have hLeftId : left.symbol.id = state.nextDefinition :=
            hIdEq.trans hRightId
          rw [hLeftId] at hUpper
          exact (Nat.lt_irrefl _ hUpper).elim
    · exact Nat.le_trans hCutoff (Nat.le_succ _)

theorem freshDefinition_includes
    (state : FirstOrderProjection.FormulaArgumentState)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula) :
    DefinitionsIncluded state
      (FirstOrderProjection.introBoolDefinition contextSorts
        sourceFormula formula |>.run state).2 := by
  intro definition hDefinition
  change definition ∈ (state.definitions.push _).toList
  simp [Array.toList_push, hDefinition]

theorem introducedDefinition_mem
    (state : FirstOrderProjection.FormulaArgumentState)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula) :
    introducedDefinition state contextSorts sourceFormula formula ∈
      ((FirstOrderProjection.introBoolDefinition contextSorts sourceFormula formula).run
        state).2.definitions.toList := by
  rw [introBoolDefinition_run]
  simp [Array.toList_push]

theorem definitionsIncluded_trans
    {first second third : FirstOrderProjection.FormulaArgumentState}
    (hFirst : DefinitionsIncluded first second)
    (hSecond : DefinitionsIncluded second third) :
    DefinitionsIncluded first third := by
  intro definition hDefinition
  exact hSecond definition (hFirst definition hDefinition)

theorem stateM_run_pure_eq
    {σ α : Type} (value : α) (state : σ) :
    (pure value : StateM σ α).run state = (value, state) := by
  rw [StateT.run_pure]
  rfl

theorem stateM_run_bind_pure_snd
    {σ α β : Type} (first : StateM σ α) (last : α → β) (state : σ) :
    ((do
      let value ← first
      pure (last value)).run state).2 =
      (first.run state).2 := by
  rw [StateT.run_bind]
  cases hRun : first.run state with
  | mk value nextState =>
      change (((pure (last value) : StateM σ β).run nextState)).2 = nextState
      rw [StateT.run_pure]
      rfl

theorem stateM_run_bind3_dep_snd
    {σ α β γ : Type} (first : StateM σ α) (second : α → StateM σ β)
    (third : α → β → StateM σ γ) (state : σ)
    (firstValue : α) (firstState : σ) (secondValue : β) (secondState : σ)
    (hFirst : first.run state = (firstValue, firstState))
    (hSecond : (second firstValue).run firstState = (secondValue, secondState)) :
    ((do
      let firstValue ← first
      let secondValue ← second firstValue
      third firstValue secondValue).run state).2 =
      ((third firstValue secondValue).run secondState).2 := by
  rw [StateT.run_bind, hFirst]
  change ((do
    let secondValue ← second firstValue
    third firstValue secondValue).run firstState).2 =
      ((third firstValue secondValue).run secondState).2
  rw [StateT.run_bind, hSecond]
  rfl

theorem stateM_run_bind2_pure_eq
    {σ α β γ : Type} (first : StateM σ α) (second : α → StateM σ β)
    (constructor : α → β → γ) (state : σ)
    (firstValue : α) (firstState : σ) (secondValue : β) (secondState : σ)
    (hFirst : first.run state = (firstValue, firstState))
    (hSecond : (second firstValue).run firstState = (secondValue, secondState)) :
    ((do
      let firstValue ← first
      let secondValue ← second firstValue
      pure (constructor firstValue secondValue)).run state) =
        (constructor firstValue secondValue, secondState) := by
  rw [StateT.run_bind, hFirst]
  change ((do
    let secondValue ← second firstValue
    pure (constructor firstValue secondValue)).run firstState) =
      (constructor firstValue secondValue, secondState)
  rw [StateT.run_bind, hSecond]
  rfl

theorem stateM_run_bind_pure_eq
    {σ α β : Type} (first : StateM σ α) (constructor : α → β) (state : σ)
    (value : α) (nextState : σ)
    (hFirst : first.run state = (value, nextState)) :
    ((do
      let value ← first
      pure (constructor value)).run state) =
        (constructor value, nextState) := by
  rw [StateT.run_bind, hFirst]
  rfl

theorem stateM_run_bind3_pure_eq
    {σ α β γ δ : Type} (first : StateM σ α) (second : α → StateM σ β)
    (third : α → β → StateM σ γ) (constructor : α → β → γ → δ) (state : σ)
    (firstValue : α) (firstState : σ) (secondValue : β) (secondState : σ)
    (thirdValue : γ) (thirdState : σ)
    (hFirst : first.run state = (firstValue, firstState))
    (hSecond : (second firstValue).run firstState = (secondValue, secondState))
    (hThird : (third firstValue secondValue).run secondState =
      (thirdValue, thirdState)) :
    ((do
      let firstValue ← first
      let secondValue ← second firstValue
      let thirdValue ← third firstValue secondValue
      pure (constructor firstValue secondValue thirdValue)).run state) =
        (constructor firstValue secondValue thirdValue, thirdState) := by
  rw [StateT.run_bind, hFirst]
  change ((do
    let secondValue ← second firstValue
    let thirdValue ← third firstValue secondValue
    pure (constructor firstValue secondValue thirdValue)).run firstState) =
      (constructor firstValue secondValue thirdValue, thirdState)
  rw [StateT.run_bind, hSecond]
  change ((do
    let thirdValue ← third firstValue secondValue
    pure (constructor firstValue secondValue thirdValue)).run secondState) =
      (constructor firstValue secondValue thirdValue, thirdState)
  rw [StateT.run_bind, hThird]
  rfl

theorem stateM_binary_definitionsIncluded
    (constructor : Term → Term → Term)
    (hReduce : ∀ contextSorts left right,
      FirstOrderProjection.introduceTermFormulaArguments contextSorts
          (constructor left right) =
        (do
          let left' ← FirstOrderProjection.introduceTermFormulaArguments contextSorts left
          let right' ← FirstOrderProjection.introduceTermFormulaArguments contextSorts right
          pure (constructor left' right')))
    (left right : Term)
    (hLeft :
      ∀ contextSorts state,
        DefinitionsIncluded state
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state).2)
    (hRight :
      ∀ contextSorts state,
        DefinitionsIncluded state
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run state).2) :
    ∀ contextSorts state,
      DefinitionsIncluded state
        ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
          (constructor left right)).run state).2 := by
  intro contextSorts state
  cases hLeftRun :
      (FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state with
  | mk left' leftState =>
      cases hRightRun :
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run leftState with
      | mk right' rightState =>
          have hLeftIncluded :
              DefinitionsIncluded state leftState := by
            simpa [hLeftRun] using hLeft contextSorts state
          have hRightIncluded :
              DefinitionsIncluded leftState rightState := by
            simpa [hRightRun] using hRight contextSorts leftState
          rw [hReduce contextSorts left right]
          rw [stateM_run_bind3_dep_snd
            (first := FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
            (second := fun _ =>
              FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
            (third := fun left' right' => pure (constructor left' right'))
            (state := state) (firstValue := left') (firstState := leftState)
            (secondValue := right') (secondState := rightState) hLeftRun hRightRun]
          simp only [StateT.run_pure]
          exact definitionsIncluded_trans hLeftIncluded hRightIncluded

theorem stateM_formula_binary_definitionsIncluded
    (constructor : Formula → Formula → Formula)
    (hReduce : ∀ contextSorts left right,
      FirstOrderProjection.introduceFormulaArguments contextSorts
          (constructor left right) =
        (do
          let left' ← FirstOrderProjection.introduceFormulaArguments contextSorts left
          let right' ← FirstOrderProjection.introduceFormulaArguments contextSorts right
          pure (constructor left' right')))
    (left right : Formula)
    (hLeft :
      ∀ contextSorts state,
        DefinitionsIncluded state
          ((FirstOrderProjection.introduceFormulaArguments contextSorts left).run state).2)
    (hRight :
      ∀ contextSorts state,
        DefinitionsIncluded state
          ((FirstOrderProjection.introduceFormulaArguments contextSorts right).run state).2) :
    ∀ contextSorts state,
      DefinitionsIncluded state
        ((FirstOrderProjection.introduceFormulaArguments contextSorts
          (constructor left right)).run state).2 := by
  intro contextSorts state
  cases hLeftRun :
      (FirstOrderProjection.introduceFormulaArguments contextSorts left).run state with
  | mk left' leftState =>
      cases hRightRun :
          (FirstOrderProjection.introduceFormulaArguments contextSorts right).run leftState with
      | mk right' rightState =>
          have hLeftIncluded :
              DefinitionsIncluded state leftState := by
            simpa [hLeftRun] using hLeft contextSorts state
          have hRightIncluded :
              DefinitionsIncluded leftState rightState := by
            simpa [hRightRun] using hRight contextSorts leftState
          rw [hReduce contextSorts left right]
          rw [stateM_run_bind3_dep_snd
            (first := FirstOrderProjection.introduceFormulaArguments contextSorts left)
            (second := fun _ =>
              FirstOrderProjection.introduceFormulaArguments contextSorts right)
            (third := fun left' right' => pure (constructor left' right'))
            (state := state) (firstValue := left') (firstState := leftState)
            (secondValue := right') (secondState := rightState) hLeftRun hRightRun]
          simp only [StateT.run_pure]
          exact definitionsIncluded_trans hLeftIncluded hRightIncluded

theorem introduceFormulaArguments_includes
    (contextSorts : List CoreSort) (source : Formula)
    (state : FirstOrderProjection.FormulaArgumentState) :
    DefinitionsIncluded state
      ((FirstOrderProjection.introduceFormulaArguments contextSorts source).run state).2 := by
  apply Formula.rec
    (motive_1 := fun term =>
      (∀ contextSorts state,
        DefinitionsIncluded state
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts term).run state).2) ∧
      (∀ contextSorts state,
        DefinitionsIncluded state
          ((FirstOrderProjection.introduceBoolViewTermFormulaArguments contextSorts term).run
            state).2))
    (motive_2 := fun formula => ∀ contextSorts state,
      DefinitionsIncluded state
        ((FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state).2)
    (motive_3 := fun terms => ∀ contextSorts state,
      DefinitionsIncluded state
        ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts terms).run state).2)
  case bvar =>
    intro sort index
    constructor
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure,
        DefinitionsIncluded] using
        (fun definition hDefinition => hDefinition)
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure,
        DefinitionsIncluded] using
        (fun definition hDefinition => hDefinition)
  case fvar =>
    intro sort id
    constructor
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure,
        DefinitionsIncluded] using
        (fun definition hDefinition => hDefinition)
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure,
        DefinitionsIncluded] using
        (fun definition hDefinition => hDefinition)
  case app =>
    intro symbol args ihArgs
    constructor
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceTermFormulaArguments] using
          ihArgs contextSorts state
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
          FirstOrderProjection.introduceTermFormulaArguments] using
        ihArgs contextSorts state
  case apply =>
    intro fn arg ihFn ihArg
    have hTerm :
        ∀ contextSorts state,
          DefinitionsIncluded state
            ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
              (Term.apply fn arg)).run state).2 := by
      exact stateM_binary_definitionsIncluded Term.apply
        (by
          intro contextSorts left right
          simp [FirstOrderProjection.introduceTermFormulaArguments])
        fn arg
        (fun contextSorts state => (ihFn).1 contextSorts state)
        (fun contextSorts state => (ihArg).1 contextSorts state)
    constructor
    · exact hTerm
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
  case bool =>
    intro value
    constructor
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure,
        DefinitionsIncluded] using
        (fun definition hDefinition => hDefinition)
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure,
        DefinitionsIncluded] using
        (fun definition hDefinition => hDefinition)
  case notE =>
    intro body ihBody
    constructor
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceTermFormulaArguments] using
        (ihBody).1 contextSorts state
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments] using
        (ihBody).1 contextSorts state
  case andE
  =>
    intro left right ihLeft ihRight
    have hTerm := stateM_binary_definitionsIncluded Term.andE (by
      intro contextSorts left right
      simp [FirstOrderProjection.introduceTermFormulaArguments]) left right
      (fun contextSorts state => (ihLeft).1 contextSorts state)
      (fun contextSorts state => (ihRight).1 contextSorts state)
    constructor
    · exact hTerm
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
  case orE =>
    intro left right ihLeft ihRight
    have hTerm := stateM_binary_definitionsIncluded Term.orE (by
      intro contextSorts left right
      simp [FirstOrderProjection.introduceTermFormulaArguments]) left right
      (fun contextSorts state => (ihLeft).1 contextSorts state)
      (fun contextSorts state => (ihRight).1 contextSorts state)
    constructor
    · exact hTerm
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
  case impE =>
    intro left right ihLeft ihRight
    have hTerm := stateM_binary_definitionsIncluded Term.impE (by
      intro contextSorts left right
      simp [FirstOrderProjection.introduceTermFormulaArguments]) left right
      (fun contextSorts state => (ihLeft).1 contextSorts state)
      (fun contextSorts state => (ihRight).1 contextSorts state)
    constructor
    · exact hTerm
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
  case iffE =>
    intro left right ihLeft ihRight
    have hTerm := stateM_binary_definitionsIncluded Term.iffE (by
      intro contextSorts left right
      simp [FirstOrderProjection.introduceTermFormulaArguments]) left right
      (fun contextSorts state => (ihLeft).1 contextSorts state)
      (fun contextSorts state => (ihRight).1 contextSorts state)
    constructor
    · exact hTerm
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
  case quote =>
    intro formula ihFormula
    constructor
    · intro contextSorts state
      cases hFormula :
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state with
      | mk formula' formulaState =>
          have hFormulaIncluded :
              DefinitionsIncluded state formulaState := by
            simpa [hFormula] using ihFormula contextSorts state
          simp [FirstOrderProjection.introduceTermFormulaArguments, hFormula]
          exact definitionsIncluded_trans hFormulaIncluded
            (freshDefinition_includes formulaState contextSorts formula formula')
    · intro contextSorts state
      cases hFormula :
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state with
      | mk formula' formulaState =>
          have hFormulaIncluded :
              DefinitionsIncluded state formulaState := by
            simpa [hFormula] using ihFormula contextSorts state
          simp [FirstOrderProjection.introduceBoolViewTermFormulaArguments, hFormula]
          exact hFormulaIncluded
  case lam =>
    intro domain codomain body ihBody
    have hTerm :
        ∀ contextSorts state,
          DefinitionsIncluded state
            ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
              (Term.lam domain codomain body)).run state).2 := by
      intro contextSorts state
      have hReduce :
          FirstOrderProjection.introduceTermFormulaArguments contextSorts
              (Term.lam domain codomain body) =
            (do
              let body' ← FirstOrderProjection.introduceTermFormulaArguments
                (domain :: contextSorts) body
              pure (Term.lam domain codomain body')) := by
        simp [FirstOrderProjection.introduceTermFormulaArguments]
      rw [hReduce, stateM_run_bind_pure_snd]
      exact (ihBody).1 (domain :: contextSorts) state
    constructor
    · exact hTerm
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
  case ite =>
    intro sort condition thenTerm elseTerm ihCondition ihThen ihElse
    have hTerm :
        ∀ contextSorts state,
          DefinitionsIncluded state
            ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
              (Term.ite sort condition thenTerm elseTerm)).run state).2 := by
      intro contextSorts state
      cases hCondition :
          (FirstOrderProjection.introduceFormulaArguments contextSorts condition).run state with
      | mk condition' conditionState =>
          cases hThen :
              (FirstOrderProjection.introduceTermFormulaArguments contextSorts thenTerm).run
                conditionState with
          | mk then' thenState =>
              cases hElse :
                  (FirstOrderProjection.introduceTermFormulaArguments contextSorts elseTerm).run
                    thenState with
              | mk else' elseState =>
                  have hConditionIncluded :
                      DefinitionsIncluded state conditionState := by
                    simpa [hCondition] using ihCondition contextSorts state
                  have hThenIncluded :
                      DefinitionsIncluded conditionState thenState := by
                    simpa [hThen] using (ihThen).1 contextSorts conditionState
                  have hElseIncluded :
                      DefinitionsIncluded thenState elseState := by
                    simpa [hElse] using (ihElse).1 contextSorts thenState
                  have hReduce :
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts
                          (Term.ite sort condition thenTerm elseTerm) =
                        (do
                          let condition' ←
                            FirstOrderProjection.introduceFormulaArguments contextSorts condition
                          let then' ←
                            FirstOrderProjection.introduceTermFormulaArguments contextSorts thenTerm
                          let else' ←
                            FirstOrderProjection.introduceTermFormulaArguments contextSorts elseTerm
                          pure (Term.ite sort condition' then' else')) := by
                    simp [FirstOrderProjection.introduceTermFormulaArguments]
                  rw [hReduce]
                  rw [stateM_run_bind3_dep_snd
                    (first := FirstOrderProjection.introduceFormulaArguments contextSorts condition)
                    (second := fun _ =>
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts thenTerm)
                    (third := fun condition' then' => do
                      let else' ←
                        FirstOrderProjection.introduceTermFormulaArguments contextSorts elseTerm
                      pure (Term.ite sort condition' then' else'))
                    (state := state) (firstValue := condition') (firstState := conditionState)
                    (secondValue := then') (secondState := thenState) hCondition hThen]
                  rw [StateT.run_bind, hElse]
                  simp only [StateT.run_pure]
                  exact definitionsIncluded_trans hConditionIncluded
                    (definitionsIncluded_trans hThenIncluded hElseIncluded)
    constructor
    · exact hTerm
    · intro contextSorts state
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
  case trueE =>
    intro contextSorts state
    simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure,
      DefinitionsIncluded] using
      (fun definition hDefinition => hDefinition)
  case falseE =>
    intro contextSorts state
    simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure,
      DefinitionsIncluded] using
      (fun definition hDefinition => hDefinition)
  case atom =>
    intro predicate args ihArgs contextSorts state
    simpa [FirstOrderProjection.introduceFormulaArguments] using
      ihArgs contextSorts state
  case equal =>
    intro sort left right ihLeft ihRight contextSorts state
    cases hLeft :
        (FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state with
    | mk left' leftState =>
        cases hRight :
            (FirstOrderProjection.introduceTermFormulaArguments
              contextSorts right).run leftState with
        | mk right' rightState =>
            have hReduce :
                FirstOrderProjection.introduceFormulaArguments contextSorts
                    (Formula.equal sort left right) =
                  (do
                    let left' ←
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts left
                    let right' ←
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts right
                    pure (Formula.equal sort left' right')) := by
              simp [FirstOrderProjection.introduceFormulaArguments]
            rw [hReduce]
            rw [stateM_run_bind3_dep_snd
              (first := FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
              (second := fun _ =>
                FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
              (third := fun left' right' => pure (Formula.equal sort left' right'))
              (state := state) (firstValue := left') (firstState := leftState)
              (secondValue := right') (secondState := rightState) hLeft hRight]
            simp only [StateT.run_pure]
            exact definitionsIncluded_trans
              (by simpa [hLeft] using (ihLeft).1 contextSorts state)
              (by simpa [hRight] using (ihRight).1 contextSorts leftState)
  case boolTerm =>
    intro term ihTerm contextSorts state
    cases term with
    | quote formula =>
        simpa [FirstOrderProjection.introduceFormulaArguments,
          FirstOrderProjection.introduceBoolViewTermFormulaArguments,
          StateT.run_pure] using
          (ihTerm).2 contextSorts state
    | bvar sort index
    | fvar sort id
    | app symbol args
    | apply fn arg
    | bool value
    | notE body
    | andE left right
    | orE left right
    | impE left right
    | iffE left right
    | lam domain codomain body
    | ite sort condition thenTerm elseTerm =>
        simpa [FirstOrderProjection.introduceFormulaArguments,
          FirstOrderProjection.introduceBoolViewTermFormulaArguments,
          StateT.run_pure] using
          (ihTerm).1 contextSorts state
  case neg =>
    intro body ihBody contextSorts state
    simpa [FirstOrderProjection.introduceFormulaArguments] using
      ihBody contextSorts state
  case imp =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_definitionsIncluded Formula.imp
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case conj =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_definitionsIncluded Formula.conj
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case disj =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_definitionsIncluded Formula.disj
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case iffE =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_definitionsIncluded Formula.iffE
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case forallE
  | existsE =>
    intro sort body ihBody contextSorts state
    simpa [FirstOrderProjection.introduceFormulaArguments] using
      ihBody (sort :: contextSorts) state
  case nil =>
    intro contextSorts state
    simpa [FirstOrderProjection.introduceTermListFormulaArguments, StateT.run_pure,
      DefinitionsIncluded] using
      (fun definition hDefinition => hDefinition)
  case cons =>
    intro head tail ihHead ihTail contextSorts state
    cases hTerm :
        (FirstOrderProjection.introduceTermFormulaArguments contextSorts head).run state with
    | mk term' termState =>
        cases hRest :
            (FirstOrderProjection.introduceTermListFormulaArguments contextSorts tail).run
              termState with
        | mk rest' restState =>
            have hTermIncluded :
                DefinitionsIncluded state termState := by
              simpa [hTerm] using (ihHead).1 contextSorts state
            have hRestIncluded :
                DefinitionsIncluded termState restState := by
              simpa [hRest] using ihTail contextSorts termState
            have hReduce :
                FirstOrderProjection.introduceTermListFormulaArguments contextSorts
                    (head :: tail) =
                  (do
                    let head' ←
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts head
                    let tail' ←
                      FirstOrderProjection.introduceTermListFormulaArguments contextSorts tail
                    pure (head' :: tail')) := by
              simp [FirstOrderProjection.introduceTermListFormulaArguments]
            rw [hReduce]
            rw [stateM_run_bind3_dep_snd
              (first := FirstOrderProjection.introduceTermFormulaArguments contextSorts head)
              (second := fun _ =>
                FirstOrderProjection.introduceTermListFormulaArguments contextSorts tail)
              (third := fun head' tail' => pure (head' :: tail'))
              (state := state) (firstValue := term') (firstState := termState)
              (secondValue := rest') (secondState := restState) hTerm hRest]
            simp only [StateT.run_pure]
            exact definitionsIncluded_trans hTermIncluded hRestIncluded

theorem stateM_bind2_pure_preserves
    {σ α β γ : Type} (P : σ → Prop)
    (first : StateM σ α) (second : α → StateM σ β)
    (constructor : α → β → γ)
    (hFirst : ∀ state, P state → P (first.run state).2)
    (hSecond : ∀ value state, P state → P ((second value).run state).2) :
    ∀ state, P state →
      P ((do
        let firstValue ← first
        let secondValue ← second firstValue
        pure (constructor firstValue secondValue)).run state).2 := by
  intro state hState
  cases hFirstRun : first.run state with
  | mk firstValue firstState =>
      cases hSecondRun : (second firstValue).run firstState with
      | mk secondValue secondState =>
          rw [StateT.run_bind, hFirstRun]
          change P ((do
            let secondValue ← second firstValue
            pure (constructor firstValue secondValue)).run firstState).2
          rw [StateT.run_bind, hSecondRun]
          change P secondState
          have hFirstFresh : P firstState := by
            simpa [hFirstRun] using hFirst state hState
          simpa [hSecondRun] using hSecond firstValue firstState hFirstFresh

theorem stateM_bind3_pure_preserves
    {σ α β γ δ : Type} (P : σ → Prop)
    (first : StateM σ α) (second : α → StateM σ β)
    (third : α → β → StateM σ γ) (constructor : α → β → γ → δ)
    (hFirst : ∀ state, P state → P (first.run state).2)
    (hSecond : ∀ value state, P state → P ((second value).run state).2)
    (hThird : ∀ firstValue secondValue state, P state →
      P ((third firstValue secondValue).run state).2) :
    ∀ state, P state →
      P ((do
        let firstValue ← first
        let secondValue ← second firstValue
        let thirdValue ← third firstValue secondValue
        pure (constructor firstValue secondValue thirdValue)).run state).2 := by
  intro state hState
  cases hFirstRun : first.run state with
  | mk firstValue firstState =>
      cases hSecondRun : (second firstValue).run firstState with
      | mk secondValue secondState =>
          cases hThirdRun : (third firstValue secondValue).run secondState with
          | mk thirdValue thirdState =>
              rw [StateT.run_bind, hFirstRun]
              change P ((do
                let secondValue ← second firstValue
                let thirdValue ← third firstValue secondValue
                pure (constructor firstValue secondValue thirdValue)).run firstState).2
              rw [StateT.run_bind, hSecondRun]
              change P ((do
                let thirdValue ← third firstValue secondValue
                pure (constructor firstValue secondValue thirdValue)).run secondState).2
              rw [StateT.run_bind, hThirdRun]
              change P thirdState
              have hFirstFresh : P firstState := by
                simpa [hFirstRun] using hFirst state hState
              have hSecondFresh : P secondState := by
                simpa [hSecondRun] using hSecond firstValue firstState hFirstFresh
              simpa [hThirdRun] using
                hThird firstValue secondValue secondState hSecondFresh

theorem stateM_term_binary_fresh
    (cutoff : Nat) (constructor : Term → Term → Term)
    (hReduce : ∀ contextSorts left right,
      FirstOrderProjection.introduceTermFormulaArguments contextSorts
          (constructor left right) =
        (do
          let left' ← FirstOrderProjection.introduceTermFormulaArguments contextSorts left
          let right' ← FirstOrderProjection.introduceTermFormulaArguments contextSorts right
          pure (constructor left' right')))
    (left right : Term)
    (hLeft : ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state).2)
    (hRight : ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run state).2) :
    ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
          (constructor left right)).run state).2 := by
  intro contextSorts state hState
  rw [hReduce contextSorts left right]
  exact stateM_bind2_pure_preserves (FreshFrom cutoff)
    (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
    (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
    constructor
    (fun state hState => hLeft contextSorts state hState)
    (fun _ state hState => hRight contextSorts state hState)
    state hState

theorem stateM_formula_binary_fresh
    (cutoff : Nat) (constructor : Formula → Formula → Formula)
    (hReduce : ∀ contextSorts left right,
      FirstOrderProjection.introduceFormulaArguments contextSorts
          (constructor left right) =
        (do
          let left' ← FirstOrderProjection.introduceFormulaArguments contextSorts left
          let right' ← FirstOrderProjection.introduceFormulaArguments contextSorts right
          pure (constructor left' right')))
    (left right : Formula)
    (hLeft : ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceFormulaArguments contextSorts left).run state).2)
    (hRight : ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceFormulaArguments contextSorts right).run state).2) :
    ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceFormulaArguments contextSorts
          (constructor left right)).run state).2 := by
  intro contextSorts state hState
  rw [hReduce contextSorts left right]
  exact stateM_bind2_pure_preserves (FreshFrom cutoff)
    (FirstOrderProjection.introduceFormulaArguments contextSorts left)
    (fun _ => FirstOrderProjection.introduceFormulaArguments contextSorts right)
    constructor
    (fun state hState => hLeft contextSorts state hState)
    (fun _ state hState => hRight contextSorts state hState)
    state hState

theorem introduceFormulaArguments_fresh
    (cutoff : Nat) (source : Formula) :
    ∀ contextSorts (state : FirstOrderProjection.FormulaArgumentState),
      FreshFrom cutoff state →
        FreshFrom cutoff
          ((FirstOrderProjection.introduceFormulaArguments contextSorts source).run state).2 := by
  apply Formula.rec
    (motive_1 := fun term =>
      (∀ contextSorts state, FreshFrom cutoff state →
        FreshFrom cutoff
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts term).run state).2) ∧
      (∀ contextSorts state, FreshFrom cutoff state →
        FreshFrom cutoff
          ((FirstOrderProjection.introduceBoolViewTermFormulaArguments contextSorts term).run
            state).2))
    (motive_2 := fun formula => ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state).2)
    (motive_3 := fun terms => ∀ contextSorts state, FreshFrom cutoff state →
      FreshFrom cutoff
        ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts terms).run state).2)
  case bvar =>
    intro sort index
    constructor
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
  case fvar =>
    intro sort id
    constructor
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
  case app =>
    intro symbol args ihArgs
    constructor
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceTermFormulaArguments] using
        ihArgs contextSorts state hState
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments] using
        ihArgs contextSorts state hState
  case apply =>
    intro fn arg ihFn ihArg
    have hTerm := stateM_term_binary_fresh cutoff Term.apply
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceTermFormulaArguments])
      fn arg
      (fun contextSorts state hState => (ihFn).1 contextSorts state hState)
      (fun contextSorts state hState => (ihArg).1 contextSorts state hState)
    constructor
    · exact hTerm
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state hState
  case bool =>
    intro value
    constructor
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
  case notE =>
    intro body ihBody
    constructor
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceTermFormulaArguments] using
        (ihBody).1 contextSorts state hState
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments] using
        (ihBody).1 contextSorts state hState
  case andE =>
    intro left right ihLeft ihRight
    have hTerm := stateM_term_binary_fresh cutoff Term.andE
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceTermFormulaArguments])
      left right
      (fun contextSorts state hState => (ihLeft).1 contextSorts state hState)
      (fun contextSorts state hState => (ihRight).1 contextSorts state hState)
    constructor
    · exact hTerm
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state hState
  case orE =>
    intro left right ihLeft ihRight
    have hTerm := stateM_term_binary_fresh cutoff Term.orE
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceTermFormulaArguments])
      left right
      (fun contextSorts state hState => (ihLeft).1 contextSorts state hState)
      (fun contextSorts state hState => (ihRight).1 contextSorts state hState)
    constructor
    · exact hTerm
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state hState
  case impE =>
    intro left right ihLeft ihRight
    have hTerm := stateM_term_binary_fresh cutoff Term.impE
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceTermFormulaArguments])
      left right
      (fun contextSorts state hState => (ihLeft).1 contextSorts state hState)
      (fun contextSorts state hState => (ihRight).1 contextSorts state hState)
    constructor
    · exact hTerm
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state hState
  case iffE =>
    intro left right ihLeft ihRight
    have hTerm := stateM_term_binary_fresh cutoff Term.iffE
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceTermFormulaArguments])
      left right
      (fun contextSorts state hState => (ihLeft).1 contextSorts state hState)
      (fun contextSorts state hState => (ihRight).1 contextSorts state hState)
    constructor
    · exact hTerm
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state hState
  case quote =>
    intro formula ihFormula
    constructor
    · intro contextSorts state hState
      cases hFormula :
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state with
      | mk formula' formulaState =>
          have hFormulaFresh : FreshFrom cutoff formulaState := by
            simpa [hFormula] using ihFormula contextSorts state hState
          simp [FirstOrderProjection.introduceTermFormulaArguments, hFormula]
          exact freshDefinition_preserves hFormulaFresh contextSorts formula formula'
    · intro contextSorts state hState
      cases hFormula :
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state with
      | mk formula' formulaState =>
          have hFormulaFresh : FreshFrom cutoff formulaState := by
            simpa [hFormula] using ihFormula contextSorts state hState
          simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments, hFormula] using
            hFormulaFresh
  case lam =>
    intro domain codomain body ihBody
    have hTerm :
        ∀ contextSorts state, FreshFrom cutoff state →
          FreshFrom cutoff
            ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
              (Term.lam domain codomain body)).run state).2 := by
      intro contextSorts state hState
      simpa [FirstOrderProjection.introduceTermFormulaArguments] using
        (ihBody).1 (domain :: contextSorts) state hState
    constructor
    · exact hTerm
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state hState
  case ite =>
    intro sort condition thenTerm elseTerm ihCondition ihThen ihElse
    have hTerm :
        ∀ contextSorts state, FreshFrom cutoff state →
          FreshFrom cutoff
            ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
              (Term.ite sort condition thenTerm elseTerm)).run state).2 := by
      intro contextSorts state hState
      rw [show
        FirstOrderProjection.introduceTermFormulaArguments contextSorts
            (Term.ite sort condition thenTerm elseTerm) =
          (do
            let condition' ←
              FirstOrderProjection.introduceFormulaArguments contextSorts condition
            let thenTerm' ←
              FirstOrderProjection.introduceTermFormulaArguments contextSorts thenTerm
            let elseTerm' ←
              FirstOrderProjection.introduceTermFormulaArguments contextSorts elseTerm
            pure (Term.ite sort condition' thenTerm' elseTerm')) by
          simp [FirstOrderProjection.introduceTermFormulaArguments]]
      exact stateM_bind3_pure_preserves (FreshFrom cutoff)
        (FirstOrderProjection.introduceFormulaArguments contextSorts condition)
        (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts thenTerm)
        (fun _ _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts elseTerm)
        (Term.ite sort)
        (fun state hState => ihCondition contextSorts state hState)
        (fun _ state hState => (ihThen).1 contextSorts state hState)
        (fun _ _ state hState => (ihElse).1 contextSorts state hState)
        state hState
    constructor
    · exact hTerm
    · intro contextSorts state hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state hState
  case trueE =>
    intro contextSorts state hState
    simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hState
  case falseE =>
    intro contextSorts state hState
    simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hState
  case atom =>
    intro predicate args ihArgs contextSorts state hState
    simpa [FirstOrderProjection.introduceFormulaArguments] using
      ihArgs contextSorts state hState
  case equal =>
    intro sort left right ihLeft ihRight contextSorts state hState
    rw [show
      FirstOrderProjection.introduceFormulaArguments contextSorts
          (Formula.equal sort left right) =
        (do
          let left' ← FirstOrderProjection.introduceTermFormulaArguments contextSorts left
          let right' ← FirstOrderProjection.introduceTermFormulaArguments contextSorts right
          pure (Formula.equal sort left' right')) by
        simp [FirstOrderProjection.introduceFormulaArguments]]
    exact stateM_bind2_pure_preserves (FreshFrom cutoff)
      (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
      (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
      (Formula.equal sort)
      (fun state hState => (ihLeft).1 contextSorts state hState)
      (fun _ state hState => (ihRight).1 contextSorts state hState)
      state hState
  case boolTerm =>
    intro term ihTerm contextSorts state hState
    cases term with
    | quote formula =>
        simpa [FirstOrderProjection.introduceFormulaArguments,
          FirstOrderProjection.introduceBoolViewTermFormulaArguments, StateT.run_pure] using
          (ihTerm).2 contextSorts state hState
    | bvar sort index
    | fvar sort id
    | app symbol args
    | apply fn arg
    | bool value
    | notE body
    | andE left right
    | orE left right
    | impE left right
    | iffE left right
    | lam domain codomain body
    | ite sort condition thenTerm elseTerm =>
        simpa [FirstOrderProjection.introduceFormulaArguments,
          FirstOrderProjection.introduceBoolViewTermFormulaArguments, StateT.run_pure] using
          (ihTerm).1 contextSorts state hState
  case neg =>
    intro body ihBody contextSorts state hState
    simpa [FirstOrderProjection.introduceFormulaArguments] using
      ihBody contextSorts state hState
  case imp =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_fresh cutoff Formula.imp
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case conj =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_fresh cutoff Formula.conj
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case disj =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_fresh cutoff Formula.disj
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case iffE =>
    intro left right ihLeft ihRight
    exact stateM_formula_binary_fresh cutoff Formula.iffE
      (by
        intro contextSorts left right
        simp [FirstOrderProjection.introduceFormulaArguments])
      left right ihLeft ihRight
  case forallE
  | existsE =>
    intro sort body ihBody contextSorts state hState
    simpa [FirstOrderProjection.introduceFormulaArguments] using
      ihBody (sort :: contextSorts) state hState
  case nil =>
    intro contextSorts state hState
    simpa [FirstOrderProjection.introduceTermListFormulaArguments, StateT.run_pure] using hState
  case cons =>
    intro head tail ihHead ihTail contextSorts state hState
    rw [show
      FirstOrderProjection.introduceTermListFormulaArguments contextSorts
          (head :: tail) =
        (do
          let head' ← FirstOrderProjection.introduceTermFormulaArguments contextSorts head
          let tail' ← FirstOrderProjection.introduceTermListFormulaArguments contextSorts tail
          pure (head' :: tail')) by
        simp [FirstOrderProjection.introduceTermListFormulaArguments]]
    exact stateM_bind2_pure_preserves (FreshFrom cutoff)
      (FirstOrderProjection.introduceTermFormulaArguments contextSorts head)
      (fun _ => FirstOrderProjection.introduceTermListFormulaArguments contextSorts tail)
      List.cons
      (fun state hState => (ihHead).1 contextSorts state hState)
      (fun _ state hState => ihTail contextSorts state hState)
      state hState

theorem introduceTermFormulaArguments_fresh
    (cutoff : Nat) (source : Term) :
    ∀ contextSorts (state : FirstOrderProjection.FormulaArgumentState),
      FreshFrom cutoff state →
        FreshFrom cutoff
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts source).run
            state).2 := by
  intro contextSorts state hState
  have hWrapped := introduceFormulaArguments_fresh cutoff
    (Formula.atom default [source]) contextSorts state hState
  simpa [FirstOrderProjection.introduceFormulaArguments,
    FirstOrderProjection.introduceTermListFormulaArguments, StateT.run_pure] using hWrapped

theorem introduceBoolViewTermFormulaArguments_fresh
    (cutoff : Nat) (source : Term) :
    ∀ contextSorts (state : FirstOrderProjection.FormulaArgumentState),
      FreshFrom cutoff state →
        FreshFrom cutoff
          ((FirstOrderProjection.introduceBoolViewTermFormulaArguments contextSorts source).run
            state).2 := by
  intro contextSorts state hState
  have hWrapped := introduceFormulaArguments_fresh cutoff
    (Formula.boolTerm source) contextSorts state hState
  simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hWrapped

theorem introduceTermListFormulaArguments_fresh
    (cutoff : Nat) (source : List Term) :
    ∀ contextSorts (state : FirstOrderProjection.FormulaArgumentState),
      FreshFrom cutoff state →
        FreshFrom cutoff
          ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts source).run
            state).2 := by
  intro contextSorts state hState
  have hWrapped := introduceFormulaArguments_fresh cutoff
    (Formula.atom default source) contextSorts state hState
  simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hWrapped

theorem build_state_fresh (source : Formula) :
    FreshFrom (FirstOrderProjection.Formula.maxFunctionIdSucc source + 1)
      ((FirstOrderProjection.introduceFormulaArguments [] source).run
        { nextDefinition := FirstOrderProjection.Formula.maxFunctionIdSucc source + 1 }).2 := by
  exact introduceFormulaArguments_fresh
    (FirstOrderProjection.Formula.maxFunctionIdSucc source + 1) source [] _
      (freshFrom_empty _)

theorem introduceTermFormulaArguments_includes
    (contextSorts : List CoreSort) (source : Term)
    (state : FirstOrderProjection.FormulaArgumentState) :
    DefinitionsIncluded state
      ((FirstOrderProjection.introduceTermFormulaArguments contextSorts source).run state).2 := by
  have hWrapped :=
    introduceFormulaArguments_includes contextSorts
      (Formula.atom default [source]) state
  simpa [FirstOrderProjection.introduceFormulaArguments,
    FirstOrderProjection.introduceTermListFormulaArguments,
    StateT.run_pure] using hWrapped

theorem introduceBoolViewTermFormulaArguments_includes
    (contextSorts : List CoreSort) (source : Term)
    (state : FirstOrderProjection.FormulaArgumentState) :
    DefinitionsIncluded state
      ((FirstOrderProjection.introduceBoolViewTermFormulaArguments contextSorts source).run
        state).2 := by
  have hWrapped :=
    introduceFormulaArguments_includes contextSorts
      (Formula.boolTerm source) state
  simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hWrapped

theorem introduceTermListFormulaArguments_includes
    (contextSorts : List CoreSort) (source : List Term)
    (state : FirstOrderProjection.FormulaArgumentState) :
    DefinitionsIncluded state
      ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts source).run
        state).2 := by
  have hWrapped :=
    introduceFormulaArguments_includes contextSorts
      (Formula.atom default source) state
  simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hWrapped

end FormulaArgumentState

namespace Model

/-- 在定义表中按函数符号查找 FOOL 布尔定义。 -/
def lookupFormulaArgumentDefinition? :
    List FirstOrderProjection.BoolDefinition → FunctionSymbol →
      Option FirstOrderProjection.BoolDefinition
  | [], _ => none
  | definition :: definitions, target =>
      if definition.symbol = target then
        some definition
      else
        lookupFormulaArgumentDefinition? definitions target

theorem lookupFormulaArgumentDefinition?_none_of_id_lt
    (definitions : List FirstOrderProjection.BoolDefinition) (target : FunctionSymbol)
    (cutoff : Nat) (hId : target.id < cutoff)
    (hFresh :
      ∀ definition ∈ definitions, cutoff ≤ definition.symbol.id) :
    lookupFormulaArgumentDefinition? definitions target = none := by
  induction definitions with
  | nil =>
      rfl
  | cons definition definitions ih =>
      have hDefinition : cutoff ≤ definition.symbol.id :=
        hFresh definition (by simp)
      have hRest :
          ∀ candidate ∈ definitions, cutoff ≤ candidate.symbol.id := by
        intro candidate hCandidate
        exact hFresh candidate (by simp [hCandidate])
      have hNe : definition.symbol ≠ target := by
        intro hEq
        have hIdEq : definition.symbol.id = target.id :=
          congrArg FunctionSymbol.id hEq
        have hTarget : definition.symbol.id < cutoff := by
          simpa [hIdEq] using hId
        exact (Nat.not_lt_of_ge hDefinition) hTarget
      simp [lookupFormulaArgumentDefinition?, hNe, ih hRest]

theorem lookupFormulaArgumentDefinition?_eq_some_of_mem
    (definitions : List FirstOrderProjection.BoolDefinition)
    (target : FirstOrderProjection.BoolDefinition)
    (hMem : target ∈ definitions)
    (hUnique :
      definitions.Pairwise
        (fun left right => left.symbol ≠ right.symbol)) :
    lookupFormulaArgumentDefinition? definitions target.symbol = some target := by
  induction definitions with
  | nil =>
      simp at hMem
  | cons definition definitions ih =>
      rw [List.pairwise_cons] at hUnique
      rcases hUnique with ⟨hHead, hTail⟩
      by_cases hEq : definition = target
      · subst definition
        simp [lookupFormulaArgumentDefinition?]
      · have hTargetMem : target ∈ definitions := by
          simpa [hEq, Ne.symm hEq] using hMem
        have hSymbolNe : definition.symbol ≠ target.symbol :=
          hHead target hTargetMem
        simp [lookupFormulaArgumentDefinition?, hSymbolNe, ih hTargetMem hTail]

theorem lookupFormulaArgumentDefinition?_eq_some_of_fresh_mem
    {cutoff : Nat} {state : FirstOrderProjection.FormulaArgumentState}
    {definition : FirstOrderProjection.BoolDefinition}
    (hState : FormulaArgumentState.FreshFrom cutoff state)
    (hDefinition : definition ∈ state.definitions.toList) :
    lookupFormulaArgumentDefinition? state.definitions.toList definition.symbol =
      some definition :=
  lookupFormulaArgumentDefinition?_eq_some_of_mem
    state.definitions.toList definition hDefinition hState.2.1

/--
批量解释 FOOL 公式参数定义函数。

每个定义函数直接读取基础模型中 `sourceFormula` 的真值；递归转换后的 `formula`
只用于目标定义公式，因此这里没有递归模型方程。
-/
noncomputable def overrideFormulaArgumentDefinitions (M : Model) (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition) : Model where
  Carrier := M.Carrier
  default := M.default
  sortInterp := M.sortInterp
  sortNonempty := M.sortNonempty
  functionInterp := fun target args =>
    match lookupFormulaArgumentDefinition? definitions.toList target with
    | some definition =>
        if definition.symbol.outputSort = CoreSort.bool then
          M.boolValue
            (FormulaArgumentDefinition.truthBool
              (Formula.Satisfies
                (FormulaArgumentDefinition.envForArgs base definition args)
                definition.sourceFormula))
        else
          M.functionInterp target args
    | none => M.functionInterp target args
  predicateInterp := M.predicateInterp
  applyInterp := M.applyInterp
  boolValue := M.boolValue
  notValue := M.notValue
  andValue := M.andValue
  orValue := M.orValue
  impValue := M.impValue
  iffValue := M.iffValue
  quoteValue := M.quoteValue
  lambdaValue := M.lambdaValue
  iteValue := M.iteValue
  boolHolds := M.boolHolds

theorem overrideFormulaArgumentDefinitions_functionInterp_of_id_lt
    (M : Model) (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (target : FunctionSymbol) (args : List M.Carrier) (cutoff : Nat)
    (hId : target.id < cutoff)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.symbol.id) :
    (overrideFormulaArgumentDefinitions M base definitions).functionInterp target args =
      M.functionInterp target args := by
    simp only [overrideFormulaArgumentDefinitions,
    lookupFormulaArgumentDefinition?_none_of_id_lt
      definitions.toList target cutoff hId hFresh]

end Model

mutual

theorem Term.eval_override_of_function_lt
    {M : Model} (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideFormulaArgumentDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.symbol.id)
    (term : Term)
    (hMax : FirstOrderProjection.Term.maxFunctionIdSucc term ≤ cutoff) :
    Term.eval extendedEnv term = Term.eval env term := by
  cases term with
  | bvar sort index =>
      simpa [Term.eval, Model.overrideFormulaArgumentDefinitions] using hBound index
  | fvar sort id =>
      simpa [Term.eval, Model.overrideFormulaArgumentDefinitions] using hFree sort id
  | app symbol args =>
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      have hId : symbol.id < cutoff := Nat.lt_of_succ_le hMax'.1
      have hArgs := Term.evalList_override_of_function_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh args hMax'.2
      simp only [Term.eval]
      rw [hArgs]
      exact Model.overrideFormulaArgumentDefinitions_functionInterp_of_id_lt
        M base definitions symbol (args.map (Term.eval env)) cutoff hId hFresh
  | apply fn arg =>
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Term.eval, Model.overrideFormulaArgumentDefinitions]
      congr 1
      · exact Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh fn hMax'.1
      · exact Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh arg hMax'.2
  | bool value =>
      simp [Term.eval, Model.overrideFormulaArgumentDefinitions]
  | notE body =>
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      simp only [Term.eval, Model.overrideFormulaArgumentDefinitions]
      congr 1
      exact Term.eval_override_of_function_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh body hMax
  | andE left right
  | orE left right
  | impE left right
  | iffE left right =>
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Term.eval, Model.overrideFormulaArgumentDefinitions]
      congr 1
      · exact Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1
      · exact Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2
  | quote formula =>
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      simp only [Term.eval, Model.overrideFormulaArgumentDefinitions]
      congr 1
      apply propext
      exact Formula.satisfies_override_of_function_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh formula hMax
  | lam domain codomain body =>
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      simp only [Term.eval, Model.overrideFormulaArgumentDefinitions]
      congr 1
      funext value
      apply Term.eval_override_of_function_lt
        base definitions cutoff (env.push value) (extendedEnv.push value)
      · intro index
        cases index <;> simp [Env.push, hBound]
      · intro sort id
        simp [Env.push, hFree]
      · exact hFresh
      · exact hMax
  | ite sort condition thenTerm elseTerm =>
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      have hMax'' := Nat.max_le.mp hMax'.2
      simp only [Term.eval, Model.overrideFormulaArgumentDefinitions]
      congr 1
      · apply propext
        exact Formula.satisfies_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh condition hMax'.1
      · exact Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh thenTerm hMax''.1
      · exact Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh elseTerm hMax''.2

theorem Formula.satisfies_override_of_function_lt
    {M : Model} (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideFormulaArgumentDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.symbol.id)
    (formula : Formula)
    (hMax : FirstOrderProjection.Formula.maxFunctionIdSucc formula ≤ cutoff) :
    Formula.Satisfies extendedEnv formula ↔ Formula.Satisfies env formula := by
  cases formula with
  | trueE
  | falseE =>
      simp [Formula.Satisfies, Formula.eval]
  | atom predicate args =>
      simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
      have hArgs := Term.evalList_override_of_function_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh args hMax
      simp only [Formula.Satisfies, Formula.eval]
      rw [hArgs]
      rfl
  | equal sort left right =>
      simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1,
        Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2]
      rfl
  | boolTerm term =>
      simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_override_of_function_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh term hMax]
      rfl
  | neg body =>
      simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      simpa only [Formula.Satisfies] using
        not_congr (Formula.satisfies_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh body hMax)
  | imp left right
  | conj left right
  | disj left right
  | iffE left right =>
      simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Formula.Satisfies, Formula.eval]
      first
      | exact and_congr
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
      | exact or_congr
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
      | exact imp_congr
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
      | exact iff_congr
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_function_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
  | forallE sort body =>
      simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      constructor <;> intro h value hSort
      · exact (Formula.satisfies_override_of_function_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mp (h value hSort)
      · exact (Formula.satisfies_override_of_function_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mpr (h value hSort)
  | existsE sort body =>
      simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      constructor
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_override_of_function_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mp hBody
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_override_of_function_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mpr hBody

theorem Term.evalList_override_of_function_lt
    {M : Model} (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideFormulaArgumentDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.symbol.id)
    (terms : List Term)
    (hMax : FirstOrderProjection.Term.maxFunctionListIdSucc terms ≤ cutoff) :
    terms.map (Term.eval extendedEnv) = terms.map (Term.eval env) := by
  cases terms with
  | nil =>
      rfl
  | cons head tail =>
      simp only [FirstOrderProjection.Term.maxFunctionListIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [List.map_cons]
      congr 1
      · exact Term.eval_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh head hMax'.1
      · exact Term.evalList_override_of_function_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh tail hMax'.2

end

namespace Env

/-- 基础环境提升到 FOOL 定义扩张模型。 -/
def liftFormulaArgumentDefinitions {M : Model} (base env : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition) :
    Env (Model.overrideFormulaArgumentDefinitions M base definitions) where
  boundVal := env.boundVal
  freeVal := env.freeVal

@[simp]
theorem liftFormulaArgumentDefinitions_bound {M : Model}
    (base env : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition) (index : Nat) :
    (liftFormulaArgumentDefinitions base env definitions).boundVal index =
      env.boundVal index :=
  rfl

@[simp]
theorem liftFormulaArgumentDefinitions_free {M : Model}
    (base env : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (sort : CoreSort) (id : VarId) :
    (liftFormulaArgumentDefinitions base env definitions).freeVal sort id =
      env.freeVal sort id :=
  rfl

@[simp]
theorem liftFormulaArgumentDefinitions_push {M : Model}
    (base env : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (value : M.Carrier) :
    (liftFormulaArgumentDefinitions base env definitions).push value =
      liftFormulaArgumentDefinitions base (env.push value) definitions := by
  rfl

end Env

namespace FormulaArgumentDefinition

theorem evaluatedArguments_liftFormulaArgumentDefinitions
    {M : Model} (base env : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (definition : FirstOrderProjection.BoolDefinition) :
    evaluatedArguments
        (Env.liftFormulaArgumentDefinitions base env definitions) definition =
      evaluatedArguments env definition := by
  unfold evaluatedArguments
  have hContext :
      ∀ start,
        contextValues (Env.liftFormulaArgumentDefinitions base env definitions)
            start definition.contextSorts =
          contextValues env start definition.contextSorts := by
    intro start
    induction definition.contextSorts generalizing start with
    | nil =>
        rfl
    | cons sort rest ih =>
        simp only [contextValues, Env.liftFormulaArgumentDefinitions_bound]
        congr 1
        exact ih (start + 1)
  have hContextZero := hContext 0
  rw [hContextZero]
  rfl

end FormulaArgumentDefinition

namespace FoolLambdaContract

private theorem lookupFormulaArgumentDefinition?_symbol_eq
    {definitions : List FirstOrderProjection.BoolDefinition}
    {target : FunctionSymbol}
    {definition : FirstOrderProjection.BoolDefinition}
    (hLookup :
      Model.lookupFormulaArgumentDefinition? definitions target = some definition) :
    definition.symbol = target := by
  induction definitions with
  | nil =>
      simp [Model.lookupFormulaArgumentDefinition?] at hLookup
  | cons head tail ih =>
      by_cases hEqual : head.symbol = target
      · simp [Model.lookupFormulaArgumentDefinition?, hEqual] at hLookup
        subst definition
        exact hEqual
      · simp [Model.lookupFormulaArgumentDefinition?, hEqual] at hLookup
        exact ih hLookup

/-- FOOL/lambda 合同沿定义函数模型扩张保持。 -/
def overrideFormulaArgumentDefinitions {M : Model}
    (contract : FoolLambdaContract M) (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition) :
    FoolLambdaContract
      (Model.overrideFormulaArgumentDefinitions M base definitions) where
  function_sort := by
    intro symbol arguments
    simp only [Model.overrideFormulaArgumentDefinitions]
    split <;> rename_i definition hLookup
    · split <;> rename_i hOutput
      · have hSymbol := lookupFormulaArgumentDefinition?_symbol_eq hLookup
        subst symbol
        rw [hOutput]
        exact contract.bool_sort _
      · exact contract.function_sort symbol arguments
    · exact contract.function_sort symbol arguments
  apply_sort := contract.apply_sort
  bool_sort := contract.bool_sort
  not_sort := contract.not_sort
  and_sort := contract.and_sort
  or_sort := contract.or_sort
  imp_sort := contract.imp_sort
  iff_sort := contract.iff_sort
  quote_sort := contract.quote_sort
  lambda_sort := contract.lambda_sort
  lambda_congr := contract.lambda_congr
  ite_sort := contract.ite_sort
  bool_holds := contract.bool_holds
  bool_extensionality := contract.bool_extensionality
  quote_eq_iff := contract.quote_eq_iff
  quote_holds := contract.quote_holds
  not_holds := contract.not_holds
  and_holds := contract.and_holds
  or_holds := contract.or_holds
  imp_holds := contract.imp_holds
  iff_holds := contract.iff_holds
  ite_value := contract.ite_value
  beta := contract.beta
  eta := contract.eta
  function_extensionality := contract.function_extensionality

end FoolLambdaContract

namespace Model

/-- 命中定义函数时，其真值恰好是原始公式在重建环境中的真值。 -/
theorem boolHolds_functionInterp_definition_iff {M : Model}
    (contract : FoolLambdaContract M) (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (definition : FirstOrderProjection.BoolDefinition)
    (arguments : List M.Carrier)
    (hLookup :
      lookupFormulaArgumentDefinition? definitions.toList definition.symbol =
        some definition)
    (hOutput : definition.symbol.outputSort = CoreSort.bool) :
    (overrideFormulaArgumentDefinitions M base definitions).boolHolds
        ((overrideFormulaArgumentDefinitions M base definitions).functionInterp
          definition.symbol arguments) ↔
    Formula.Satisfies
        (FormulaArgumentDefinition.envForArgs base definition arguments)
        definition.sourceFormula := by
  simp [overrideFormulaArgumentDefinitions, hLookup, hOutput, contract.bool_holds,
    FormulaArgumentDefinition.truthBool_eq_true_iff]

theorem functionInterp_definition_eq_quoteValue {M : Model}
    (contract : FoolLambdaContract M) (base : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (definition : FirstOrderProjection.BoolDefinition)
    (arguments : List M.Carrier)
    (hLookup :
      lookupFormulaArgumentDefinition? definitions.toList definition.symbol =
        some definition)
    (hOutput : definition.symbol.outputSort = CoreSort.bool) :
    (overrideFormulaArgumentDefinitions M base definitions).functionInterp
        definition.symbol arguments =
      M.quoteValue
        (Formula.Satisfies
          (FormulaArgumentDefinition.envForArgs base definition arguments)
          definition.sourceFormula) := by
  let extendedContract :=
    FoolLambdaContract.overrideFormulaArgumentDefinitions contract base definitions
  have hLeftSort :
      (overrideFormulaArgumentDefinitions M base definitions).sortInterp CoreSort.bool
        ((overrideFormulaArgumentDefinitions M base definitions).functionInterp
          definition.symbol arguments) := by
    simpa [hOutput] using extendedContract.function_sort definition.symbol arguments
  have hRightSort :
      (overrideFormulaArgumentDefinitions M base definitions).sortInterp CoreSort.bool
        (M.quoteValue
          (Formula.Satisfies
            (FormulaArgumentDefinition.envForArgs base definition arguments)
            definition.sourceFormula)) :=
    extendedContract.quote_sort _
  apply (extendedContract.bool_extensionality
    ((overrideFormulaArgumentDefinitions M base definitions).functionInterp
      definition.symbol arguments)
    (M.quoteValue
      (Formula.Satisfies
        (FormulaArgumentDefinition.envForArgs base definition arguments)
        definition.sourceFormula))
    hLeftSort hRightSort).mpr
  have hFunction :
      (overrideFormulaArgumentDefinitions M base definitions).functionInterp
          definition.symbol arguments =
        M.boolValue
          (FormulaArgumentDefinition.truthBool
            (Formula.Satisfies
              (FormulaArgumentDefinition.envForArgs base definition arguments)
              definition.sourceFormula)) := by
    simp [Model.overrideFormulaArgumentDefinitions, hLookup, hOutput]
  rw [hFunction]
  constructor
  · intro h
    apply (extendedContract.quote_holds _).mpr
    apply (FormulaArgumentDefinition.truthBool_eq_true_iff _).mp
    exact (extendedContract.bool_holds _).mp h
  · intro h
    apply (extendedContract.bool_holds _).mpr
    apply (FormulaArgumentDefinition.truthBool_eq_true_iff _).mpr
    exact (extendedContract.quote_holds _).mp h

theorem boolTerm_replacement_satisfies_iff
    {M : Model} (contract : FoolLambdaContract M)
    (base env : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (definition : FirstOrderProjection.BoolDefinition)
    (hLookup :
      lookupFormulaArgumentDefinition? definitions.toList definition.symbol =
        some definition)
    (hOutput : definition.symbol.outputSort = CoreSort.bool)
    (hEnv :
      FormulaArgumentDefinition.envForArgs base definition
          (FormulaArgumentDefinition.evaluatedArguments env definition) = env) :
    Formula.Satisfies
        (Env.liftFormulaArgumentDefinitions base env definitions)
        (.boolTerm definition.replacement) ↔
      Formula.Satisfies env definition.sourceFormula := by
  have hArguments :
      definition.arguments.map (Term.eval
        (Env.liftFormulaArgumentDefinitions base env definitions)) =
        FormulaArgumentDefinition.evaluatedArguments env definition := by
    calc
      definition.arguments.map (Term.eval
          (Env.liftFormulaArgumentDefinitions base env definitions)) =
          FormulaArgumentDefinition.evaluatedArguments
            (Env.liftFormulaArgumentDefinitions base env definitions) definition :=
        FormulaArgumentDefinition.evaluatedArguments_eq_eval_arguments
          (Env.liftFormulaArgumentDefinitions base env definitions) definition
      _ = FormulaArgumentDefinition.evaluatedArguments env definition := by
        exact FormulaArgumentDefinition.evaluatedArguments_liftFormulaArgumentDefinitions
          base env definitions definition
  simp only [Formula.Satisfies, Formula.eval, Term.eval,
    FirstOrderProjection.BoolDefinition.replacement]
  rw [hArguments]
  rw [Model.boolHolds_functionInterp_definition_iff
    contract base definitions definition
    (FormulaArgumentDefinition.evaluatedArguments env definition) hLookup hOutput]
  simp [hEnv, Formula.Satisfies]

theorem Term.eval_replacement_eq_quoteValue
    {M : Model} (contract : FoolLambdaContract M)
    (base env : Env M)
    (definitions : Array FirstOrderProjection.BoolDefinition)
    (definition : FirstOrderProjection.BoolDefinition)
    (hLookup :
      lookupFormulaArgumentDefinition? definitions.toList definition.symbol =
        some definition)
    (hOutput : definition.symbol.outputSort = CoreSort.bool) :
    Term.eval
        (Env.liftFormulaArgumentDefinitions base env definitions)
        definition.replacement =
      M.quoteValue
        (Formula.Satisfies
          (FormulaArgumentDefinition.envForArgs base definition
            (FormulaArgumentDefinition.evaluatedArguments env definition))
          definition.sourceFormula) := by
  have hArguments :
      definition.arguments.map (Term.eval
        (Env.liftFormulaArgumentDefinitions base env definitions)) =
        FormulaArgumentDefinition.evaluatedArguments env definition := by
    calc
      definition.arguments.map (Term.eval
          (Env.liftFormulaArgumentDefinitions base env definitions)) =
          FormulaArgumentDefinition.evaluatedArguments
            (Env.liftFormulaArgumentDefinitions base env definitions) definition :=
        FormulaArgumentDefinition.evaluatedArguments_eq_eval_arguments
          (Env.liftFormulaArgumentDefinitions base env definitions) definition
      _ = FormulaArgumentDefinition.evaluatedArguments env definition := by
        exact FormulaArgumentDefinition.evaluatedArguments_liftFormulaArgumentDefinitions
          base env definitions definition
  simp only [FirstOrderProjection.BoolDefinition.replacement, Term.eval]
  rw [hArguments]
  exact Model.functionInterp_definition_eq_quoteValue
    contract base definitions definition
      (FormulaArgumentDefinition.evaluatedArguments env definition) hLookup hOutput

theorem Term.eval_introducedDefinition_eq_quote
    {M : Model} (contract : FoolLambdaContract M)
    (base env : Env M) (cutoff : Nat)
    (state finalState : FirstOrderProjection.FormulaArgumentState)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula)
    (hFinalFresh : FormulaArgumentState.FreshFrom cutoff finalState)
    (hDefinition :
      FormulaArgumentState.introducedDefinition
          state contextSorts sourceFormula formula ∈
        finalState.definitions.toList)
    (hFree : ∀ sort id, base.freeVal sort id = env.freeVal sort id)
    (hScoped : Formula.wellScopedWith contextSorts sourceFormula = true) :
    Term.eval
        (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
        (FormulaArgumentState.introducedDefinition
          state contextSorts sourceFormula formula).replacement =
      Term.eval env (.quote sourceFormula) := by
  let definition :=
    FormulaArgumentState.introducedDefinition state contextSorts sourceFormula formula
  have hLookup :
      Model.lookupFormulaArgumentDefinition? finalState.definitions.toList definition.symbol =
        some definition :=
    Model.lookupFormulaArgumentDefinition?_eq_some_of_fresh_mem hFinalFresh hDefinition
  rw [Term.eval_replacement_eq_quoteValue
    contract base env finalState.definitions definition hLookup]
  · unfold Term.eval
    change M.quoteValue
        (Formula.Satisfies
          (FormulaArgumentDefinition.envForArgs base definition
            (FormulaArgumentDefinition.evaluatedArguments env definition))
          definition.sourceFormula) =
      M.quoteValue (Formula.Satisfies env sourceFormula)
    congr 1
    apply propext
    have hAgreement :=
      FormulaArgumentDefinition.envForArgs_evaluatedArguments_scopedAgreement
        base env definition hFree
    simpa [definition, FormulaArgumentState.introducedDefinition] using
      Formula.satisfies_iff_of_scopedAgreement
        contextSorts
        (FormulaArgumentDefinition.envForArgs base definition
          (FormulaArgumentDefinition.evaluatedArguments env definition))
        env hAgreement sourceFormula hScoped
  · rfl

theorem introduceFormulaArguments_satisfies
    {M : Model} (contract : FoolLambdaContract M) (base : Env M)
    (cutoff : Nat) (finalState : FirstOrderProjection.FormulaArgumentState)
    (hFinalFresh : FormulaArgumentState.FreshFrom cutoff finalState)
    (source : Formula) :
    ∀ contextSorts state (env : Env M),
      FormulaArgumentState.DefinitionsIncluded
        ((FirstOrderProjection.introduceFormulaArguments contextSorts source).run state).2
        finalState →
      FirstOrderProjection.Formula.maxFunctionIdSucc source ≤ cutoff →
      (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
      Formula.wellScopedWith contextSorts source = true →
      (Formula.Satisfies
          (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
          ((FirstOrderProjection.introduceFormulaArguments contextSorts source).run state).1 ↔
        Formula.Satisfies env source) := by
  apply Formula.rec
    (motive_1 := fun term =>
      (∀ contextSorts state (env : Env M),
        FormulaArgumentState.DefinitionsIncluded
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts term).run state).2
          finalState →
        FirstOrderProjection.Term.maxFunctionIdSucc term ≤ cutoff →
        (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
        Term.wellScopedWith contextSorts term = true →
        Term.eval
            (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
            ((FirstOrderProjection.introduceTermFormulaArguments contextSorts term).run state).1 =
          Term.eval env term) ∧
      (∀ contextSorts state (env : Env M),
        FormulaArgumentState.DefinitionsIncluded
          ((FirstOrderProjection.introduceBoolViewTermFormulaArguments contextSorts term).run
            state).2 finalState →
        FirstOrderProjection.Term.maxFunctionIdSucc term ≤ cutoff →
        (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
        Term.wellScopedWith contextSorts term = true →
        Term.eval
            (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
            ((FirstOrderProjection.introduceBoolViewTermFormulaArguments
              contextSorts term).run state).1 =
          Term.eval env term))
    (motive_2 := fun formula => ∀ contextSorts state (env : Env M),
      FormulaArgumentState.DefinitionsIncluded
        ((FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state).2
        finalState →
      FirstOrderProjection.Formula.maxFunctionIdSucc formula ≤ cutoff →
      (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
      Formula.wellScopedWith contextSorts formula = true →
      (Formula.Satisfies
          (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
          ((FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state).1 ↔
        Formula.Satisfies env formula))
    (motive_3 := fun terms => ∀ contextSorts state (env : Env M),
      FormulaArgumentState.DefinitionsIncluded
        ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts terms).run state).2
        finalState →
      FirstOrderProjection.Term.maxFunctionListIdSucc terms ≤ cutoff →
      (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
      Term.wellScopedListWith contextSorts terms = true →
      ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts terms).run state).1.map
          (Term.eval
            (Env.liftFormulaArgumentDefinitions base env finalState.definitions)) =
        terms.map (Term.eval env))
  case bvar =>
    intro sort index
    constructor
    · intro contextSorts state env hIncluded hMax hFree hScoped
      rw [show
        (FirstOrderProjection.introduceTermFormulaArguments
          contextSorts (Term.bvar sort index)).run state =
            (Term.bvar sort index, state) by
        simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
          FormulaArgumentState.stateM_run_pure_eq (Term.bvar sort index) state]
      simp [Term.eval, Env.liftFormulaArgumentDefinitions_bound]
    · intro contextSorts state env hIncluded hMax hFree hScoped
      rw [show
        (FirstOrderProjection.introduceBoolViewTermFormulaArguments
          contextSorts (Term.bvar sort index)).run state =
            (Term.bvar sort index, state) by
        simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
          FirstOrderProjection.introduceTermFormulaArguments] using
            FormulaArgumentState.stateM_run_pure_eq (Term.bvar sort index) state]
      simp [Term.eval, Env.liftFormulaArgumentDefinitions_bound]
  case fvar =>
    intro sort id
    constructor
    · intro contextSorts state env hIncluded hMax hFree hScoped
      rw [show
        (FirstOrderProjection.introduceTermFormulaArguments
          contextSorts (Term.fvar sort id)).run state =
            (Term.fvar sort id, state) by
        simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
          FormulaArgumentState.stateM_run_pure_eq (Term.fvar sort id) state]
      simp [Term.eval, Env.liftFormulaArgumentDefinitions_free]
    · intro contextSorts state env hIncluded hMax hFree hScoped
      rw [show
        (FirstOrderProjection.introduceBoolViewTermFormulaArguments
          contextSorts (Term.fvar sort id)).run state =
            (Term.fvar sort id, state) by
        simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
          FirstOrderProjection.introduceTermFormulaArguments] using
            FormulaArgumentState.stateM_run_pure_eq (Term.fvar sort id) state]
      simp [Term.eval, Env.liftFormulaArgumentDefinitions_free]
  case app =>
    intro symbol args ihArgs
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.app symbol args)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.app symbol args) ≤ cutoff →
          (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
          Term.wellScopedWith contextSorts (Term.app symbol args) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.app symbol args)).run state).1 =
            Term.eval env (Term.app symbol args) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hArgs :
          (FirstOrderProjection.introduceTermListFormulaArguments contextSorts args).run state with
      | mk args' argsState =>
          have hRun :
              (FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.app symbol args)).run state =
                (Term.app symbol args', argsState) := by
            simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
              FormulaArgumentState.stateM_run_bind_pure_eq
                (FirstOrderProjection.introduceTermListFormulaArguments contextSorts args)
                (Term.app symbol) state args' argsState hArgs
          have hArgsIncluded :
              FormulaArgumentState.DefinitionsIncluded argsState finalState := by
            simpa [hRun] using hIncluded
          simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
          have hMaxParts := Nat.max_le.mp hMax
          have hArgsScoped : Term.wellScopedListWith contextSorts args = true := by
            simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
            exact hScoped.2
          have hArgsEval :=
            ihArgs contextSorts state env (by simpa [hArgs] using hArgsIncluded)
              hMaxParts.2 hFree hArgsScoped
          have hArgsEval' :
              args'.map
                  (Term.eval
                    (Env.liftFormulaArgumentDefinitions base env finalState.definitions)) =
                args.map (Term.eval env) := by
            simpa [hArgs] using hArgsEval
          simp only [hRun, Term.eval]
          rw [hArgsEval']
          exact overrideFormulaArgumentDefinitions_functionInterp_of_id_lt
            M base finalState.definitions symbol (args.map (Term.eval env)) cutoff
              (Nat.lt_of_succ_le hMaxParts.1)
              (fun definition hDefinition => (hFinalFresh.1 definition hDefinition).1)
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hFree hScoped
  case apply =>
    intro fn arg ihFn ihArg
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.apply fn arg)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.apply fn arg) ≤ cutoff →
          (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
          Term.wellScopedWith contextSorts (Term.apply fn arg) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.apply fn arg)).run state).1 =
            Term.eval env (Term.apply fn arg) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hFn :
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts fn).run state with
      | mk fn' fnState =>
          cases hArg :
              (FirstOrderProjection.introduceTermFormulaArguments contextSorts arg).run
                fnState with
          | mk arg' argState =>
              have hRun :
                  (FirstOrderProjection.introduceTermFormulaArguments
                    contextSorts (Term.apply fn arg)).run state =
                    (Term.apply fn' arg', argState) := by
                simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                  FormulaArgumentState.stateM_run_bind2_pure_eq
                    (FirstOrderProjection.introduceTermFormulaArguments contextSorts fn)
                    (fun _ =>
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts arg)
                    Term.apply state fn' fnState arg' argState hFn hArg
              have hArgIncluded :
                  FormulaArgumentState.DefinitionsIncluded argState finalState := by
                simpa [hRun] using hIncluded
              have hFnIncluded :
                  FormulaArgumentState.DefinitionsIncluded fnState finalState :=
                FormulaArgumentState.definitionsIncluded_trans
                  (FormulaArgumentState.introduceTermFormulaArguments_includes
                    contextSorts arg fnState)
                  (by simpa [hArg] using hArgIncluded)
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              have hFnEval :=
                (ihFn).1 contextSorts state env
                  (by simpa [hFn] using hFnIncluded)
                  hMaxParts.1 hFree hScoped.1
              have hArgEval :=
                (ihArg).1 contextSorts fnState env
                  (by simpa [hArg] using hArgIncluded)
                  hMaxParts.2 hFree hScoped.2
              have hFnEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions) fn' =
                    Term.eval env fn := by
                simpa [hFn] using hFnEval
              have hArgEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions) arg' =
                    Term.eval env arg := by
                simpa [hArg] using hArgEval
              simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
              congr 1
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hFree hScoped
  case bool =>
    intro value
    constructor
    · intro contextSorts state env hIncluded hMax hFree hScoped
      rw [show
        (FirstOrderProjection.introduceTermFormulaArguments
          contextSorts (Term.bool value)).run state =
            (Term.bool value, state) by
        simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
          FormulaArgumentState.stateM_run_pure_eq (Term.bool value) state]
      simp [Term.eval, Model.overrideFormulaArgumentDefinitions]
    · intro contextSorts state env hIncluded hMax hFree hScoped
      rw [show
        (FirstOrderProjection.introduceBoolViewTermFormulaArguments
          contextSorts (Term.bool value)).run state =
            (Term.bool value, state) by
        simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
          FirstOrderProjection.introduceTermFormulaArguments] using
            FormulaArgumentState.stateM_run_pure_eq (Term.bool value) state]
      simp [Term.eval, Model.overrideFormulaArgumentDefinitions]
  case notE =>
    intro body ihBody
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.notE body)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.notE body) ≤ cutoff →
          (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
          Term.wellScopedWith contextSorts (Term.notE body) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.notE body)).run state).1 =
            Term.eval env (Term.notE body) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hBodyRun :
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts body).run state with
      | mk body' bodyState =>
          have hRun :
              (FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.notE body)).run state =
                (Term.notE body', bodyState) := by
            simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
              FormulaArgumentState.stateM_run_bind_pure_eq
                (FirstOrderProjection.introduceTermFormulaArguments contextSorts body)
                Term.notE state body' bodyState hBodyRun
          have hBodyIncluded :
              FormulaArgumentState.DefinitionsIncluded bodyState finalState := by
            simpa [hRun] using hIncluded
          have hBody :=
            (ihBody).1 contextSorts state env
              (by simpa [hBodyRun] using hBodyIncluded)
              (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
              hFree (by simpa [Term.wellScopedWith] using hScoped)
          have hBody' :
              Term.eval
                  (Env.liftFormulaArgumentDefinitions base env finalState.definitions) body' =
                Term.eval env body := by
            simpa [hBodyRun] using hBody
          simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
          congr 1
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hFree hScoped
  case andE =>
    intro left right ihLeft ihRight
    constructor
    · intro contextSorts state env hIncluded hMax hFree hScoped
      cases hLeft :
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state with
      | mk left' leftState =>
          cases hRight :
              (FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run
                leftState with
          | mk right' rightState =>
              have hRun :
                  (FirstOrderProjection.introduceTermFormulaArguments
                    contextSorts (Term.andE left right)).run state =
                    (Term.andE left' right', rightState) := by
                simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                  FormulaArgumentState.stateM_run_bind2_pure_eq
                    (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                    (fun _ =>
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                    Term.andE state left' leftState right' rightState hLeft hRight
              have hRightIncluded :
                  FormulaArgumentState.DefinitionsIncluded rightState finalState := by
                simpa [hRun] using hIncluded
              have hLeftIncluded :
                  FormulaArgumentState.DefinitionsIncluded leftState finalState :=
                FormulaArgumentState.definitionsIncluded_trans
                  (FormulaArgumentState.introduceTermFormulaArguments_includes
                    contextSorts right leftState)
                  (by simpa [hRight] using hRightIncluded)
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              have hLeftEval := (ihLeft).1 contextSorts state env
                (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
              have hRightEval := (ihRight).1 contextSorts leftState env
                (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
              have hLeftEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      left' =
                    Term.eval env left := by
                simpa [hLeft] using hLeftEval
              have hRightEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      right' =
                    Term.eval env right := by
                simpa [hRight] using hRightEval
              simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
              congr 1
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        (show Term.eval
            (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
            ((FirstOrderProjection.introduceTermFormulaArguments contextSorts
              (Term.andE left right)).run state).1 =
              Term.eval env (Term.andE left right) from
          (by
            cases hLeft :
                (FirstOrderProjection.introduceTermFormulaArguments
                  contextSorts left).run state with
            | mk left' leftState =>
                cases hRight :
                    (FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run
                      leftState with
                | mk right' rightState =>
                    have hRun :
                        (FirstOrderProjection.introduceTermFormulaArguments
                          contextSorts (Term.andE left right)).run state =
                          (Term.andE left' right', rightState) := by
                      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                        FormulaArgumentState.stateM_run_bind2_pure_eq
                          (FirstOrderProjection.introduceTermFormulaArguments
                            contextSorts left)
                          (fun _ =>
                            FirstOrderProjection.introduceTermFormulaArguments
                              contextSorts right)
                          Term.andE state left' leftState right' rightState hLeft hRight
                    have hRightIncluded :
                        FormulaArgumentState.DefinitionsIncluded rightState finalState := by
                      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
                        hRun] using hIncluded
                    have hLeftIncluded :
                        FormulaArgumentState.DefinitionsIncluded leftState finalState :=
                      FormulaArgumentState.definitionsIncluded_trans
                        (FormulaArgumentState.introduceTermFormulaArguments_includes
                          contextSorts right leftState)
                        (by simpa [hRight] using hRightIncluded)
                    simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
                    have hMaxParts := Nat.max_le.mp hMax
                    simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
                    have hLeftEval := (ihLeft).1 contextSorts state env
                      (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
                    have hRightEval := (ihRight).1 contextSorts leftState env
                      (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
                    have hLeftEval' :
                        Term.eval
                            (Env.liftFormulaArgumentDefinitions
                              base env finalState.definitions) left' =
                          Term.eval env left := by
                      simpa [hLeft] using hLeftEval
                    have hRightEval' :
                        Term.eval
                            (Env.liftFormulaArgumentDefinitions
                              base env finalState.definitions) right' =
                          Term.eval env right := by
                      simpa [hRight] using hRightEval
                    simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
                    congr 1
                    ))
  case orE =>
    intro left right ihLeft ihRight
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.orE left right)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.orE left right) ≤ cutoff →
          (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
          Term.wellScopedWith contextSorts (Term.orE left right) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.orE left right)).run state).1 =
            Term.eval env (Term.orE left right) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hLeft :
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state with
      | mk left' leftState =>
          cases hRight :
              (FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run
                leftState with
          | mk right' rightState =>
              have hRun :
                  (FirstOrderProjection.introduceTermFormulaArguments
                    contextSorts (Term.orE left right)).run state =
                    (Term.orE left' right', rightState) := by
                simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                  FormulaArgumentState.stateM_run_bind2_pure_eq
                    (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                    (fun _ =>
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                    Term.orE state left' leftState right' rightState hLeft hRight
              have hRightIncluded :
                  FormulaArgumentState.DefinitionsIncluded rightState finalState := by
                simpa [hRun] using hIncluded
              have hLeftIncluded :
                  FormulaArgumentState.DefinitionsIncluded leftState finalState :=
                FormulaArgumentState.definitionsIncluded_trans
                  (FormulaArgumentState.introduceTermFormulaArguments_includes
                    contextSorts right leftState)
                  (by simpa [hRight] using hRightIncluded)
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              have hLeftEval := (ihLeft).1 contextSorts state env
                (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
              have hRightEval := (ihRight).1 contextSorts leftState env
                (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
              have hLeftEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      left' =
                    Term.eval env left := by
                simpa [hLeft] using hLeftEval
              have hRightEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      right' =
                    Term.eval env right := by
                simpa [hRight] using hRightEval
              simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
              congr 1
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hFree hScoped
  case impE =>
    intro left right ihLeft ihRight
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.impE left right)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.impE left right) ≤ cutoff →
          (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
          Term.wellScopedWith contextSorts (Term.impE left right) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.impE left right)).run state).1 =
            Term.eval env (Term.impE left right) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hLeft :
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state with
      | mk left' leftState =>
          cases hRight :
              (FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run
                leftState with
          | mk right' rightState =>
              have hRun :
                  (FirstOrderProjection.introduceTermFormulaArguments
                    contextSorts (Term.impE left right)).run state =
                    (Term.impE left' right', rightState) := by
                simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                  FormulaArgumentState.stateM_run_bind2_pure_eq
                    (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                    (fun _ =>
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                    Term.impE state left' leftState right' rightState hLeft hRight
              have hRightIncluded :
                  FormulaArgumentState.DefinitionsIncluded rightState finalState := by
                simpa [hRun] using hIncluded
              have hLeftIncluded :
                  FormulaArgumentState.DefinitionsIncluded leftState finalState :=
                FormulaArgumentState.definitionsIncluded_trans
                  (FormulaArgumentState.introduceTermFormulaArguments_includes
                    contextSorts right leftState)
                  (by simpa [hRight] using hRightIncluded)
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              have hLeftEval := (ihLeft).1 contextSorts state env
                (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
              have hRightEval := (ihRight).1 contextSorts leftState env
                (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
              have hLeftEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      left' =
                    Term.eval env left := by
                simpa [hLeft] using hLeftEval
              have hRightEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      right' =
                    Term.eval env right := by
                simpa [hRight] using hRightEval
              simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
              congr 1
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hFree hScoped
  case iffE =>
    intro left right ihLeft ihRight
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.iffE left right)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.iffE left right) ≤ cutoff →
          (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
          Term.wellScopedWith contextSorts (Term.iffE left right) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.iffE left right)).run state).1 =
            Term.eval env (Term.iffE left right) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hLeft :
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state with
      | mk left' leftState =>
          cases hRight :
              (FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run
                leftState with
          | mk right' rightState =>
              have hRun :
                  (FirstOrderProjection.introduceTermFormulaArguments
                    contextSorts (Term.iffE left right)).run state =
                    (Term.iffE left' right', rightState) := by
                simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                  FormulaArgumentState.stateM_run_bind2_pure_eq
                    (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                    (fun _ =>
                      FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                    Term.iffE state left' leftState right' rightState hLeft hRight
              have hRightIncluded :
                  FormulaArgumentState.DefinitionsIncluded rightState finalState := by
                simpa [hRun] using hIncluded
              have hLeftIncluded :
                  FormulaArgumentState.DefinitionsIncluded leftState finalState :=
                FormulaArgumentState.definitionsIncluded_trans
                  (FormulaArgumentState.introduceTermFormulaArguments_includes
                    contextSorts right leftState)
                  (by simpa [hRight] using hRightIncluded)
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              have hLeftEval := (ihLeft).1 contextSorts state env
                (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
              have hRightEval := (ihRight).1 contextSorts leftState env
                (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
              have hLeftEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      left' =
                    Term.eval env left := by
                simpa [hLeft] using hLeftEval
              have hRightEval' :
                  Term.eval
                      (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                      right' =
                    Term.eval env right := by
                simpa [hRight] using hRightEval
              simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
              congr 1
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hFree hScoped
  case quote =>
    intro formula ihFormula
    constructor
    · intro contextSorts state env hIncluded hMax hFree hScoped
      cases hFormula :
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state with
      | mk formula' formulaState =>
          let definition :=
            FormulaArgumentState.introducedDefinition
              formulaState contextSorts formula formula'
          have hDefinition : definition ∈ finalState.definitions.toList := by
            apply hIncluded
            simpa [FirstOrderProjection.introduceTermFormulaArguments,
              hFormula, definition] using
              FormulaArgumentState.introducedDefinition_mem
                formulaState contextSorts formula formula'
          simp only [FirstOrderProjection.introduceTermFormulaArguments,
            StateT.run_bind, hFormula, FormulaArgumentState.introBoolDefinition_run]
          exact Term.eval_introducedDefinition_eq_quote
            contract base env cutoff formulaState finalState contextSorts formula formula'
              hFinalFresh hDefinition hFree
              (by simpa [Term.wellScopedWith] using hScoped)
    · intro contextSorts state env hIncluded hMax hFree hScoped
      cases hFormula :
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state with
      | mk formula' formulaState =>
          have hRun :
              (FirstOrderProjection.introduceBoolViewTermFormulaArguments
                contextSorts (Term.quote formula)).run state =
                  (Term.quote formula', formulaState) := by
            simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
              FormulaArgumentState.stateM_run_bind_pure_eq
                (FirstOrderProjection.introduceFormulaArguments contextSorts formula)
                Term.quote state formula' formulaState hFormula
          have hFormulaIncluded :
              FormulaArgumentState.DefinitionsIncluded formulaState finalState := by
            simpa [hRun] using hIncluded
          have hSem := ihFormula contextSorts state env
            (by simpa [hFormula] using hFormulaIncluded)
            (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
            hFree (by simpa [Term.wellScopedWith] using hScoped)
          have hSem' :
              Formula.Satisfies
                  (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
                  formula' ↔
                Formula.Satisfies env formula := by
            simpa [hFormula] using hSem
          simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
          exact congrArg M.quoteValue (propext hSem')
  case lam =>
    intro domain codomain body ihBody
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.lam domain codomain body)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc
              (Term.lam domain codomain body) ≤ cutoff →
          (∀ sort id, base.freeVal sort id = env.freeVal sort id) →
          Term.wellScopedWith contextSorts (Term.lam domain codomain body) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.lam domain codomain body)).run state).1 =
            Term.eval env (Term.lam domain codomain body) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hBody :
          (FirstOrderProjection.introduceTermFormulaArguments
            (domain :: contextSorts) body).run state with
      | mk body' bodyState =>
          have hRun :
              (FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.lam domain codomain body)).run state =
                  (Term.lam domain codomain body', bodyState) := by
            simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
              FormulaArgumentState.stateM_run_bind_pure_eq
                (FirstOrderProjection.introduceTermFormulaArguments
                  (domain :: contextSorts) body)
                (Term.lam domain codomain) state body' bodyState hBody
          have hBodyIncluded :
              FormulaArgumentState.DefinitionsIncluded bodyState finalState := by
            simpa [hRun] using hIncluded
          have hBodyEval :
              ∀ value,
                Term.eval
                    (Env.liftFormulaArgumentDefinitions
                      base (env.push value) finalState.definitions) body' =
                  Term.eval (env.push value) body := by
            intro value
            simpa [hBody] using
              (ihBody).1 (domain :: contextSorts) state (env.push value)
                (by simpa [hBody] using hBodyIncluded)
                (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
                (by intro sort id; simpa [Env.push] using hFree sort id)
                (by simpa [Term.wellScopedWith] using hScoped)
          simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
          apply congrArg (M.lambdaValue domain codomain)
          funext value
          simpa [Env.liftFormulaArgumentDefinitions_push] using hBodyEval value
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
              hIncluded)
          hMax hFree hScoped
  case ite =>
    intro sort condition thenTerm elseTerm ihCondition ihThen ihElse
    have hTerm :
        ∀ contextSorts state (env : Env M),
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.ite sort condition thenTerm elseTerm)).run state).2
              finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc
              (Term.ite sort condition thenTerm elseTerm) ≤ cutoff →
          (∀ target id, base.freeVal target id = env.freeVal target id) →
          Term.wellScopedWith contextSorts
              (Term.ite sort condition thenTerm elseTerm) = true →
          Term.eval
              (Env.liftFormulaArgumentDefinitions base env finalState.definitions)
              ((FirstOrderProjection.introduceTermFormulaArguments
                contextSorts (Term.ite sort condition thenTerm elseTerm)).run state).1 =
            Term.eval env (Term.ite sort condition thenTerm elseTerm) := by
      intro contextSorts state env hIncluded hMax hFree hScoped
      cases hCondition :
          (FirstOrderProjection.introduceFormulaArguments contextSorts condition).run state with
      | mk condition' conditionState =>
          cases hThen :
              (FirstOrderProjection.introduceTermFormulaArguments
                contextSorts thenTerm).run conditionState with
          | mk thenTerm' thenState =>
              cases hElse :
                  (FirstOrderProjection.introduceTermFormulaArguments
                    contextSorts elseTerm).run thenState with
              | mk elseTerm' elseState =>
                  have hRun :
                      (FirstOrderProjection.introduceTermFormulaArguments
                        contextSorts
                        (Term.ite sort condition thenTerm elseTerm)).run state =
                          (Term.ite sort condition' thenTerm' elseTerm', elseState) := by
                    simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                      FormulaArgumentState.stateM_run_bind3_pure_eq
                        (FirstOrderProjection.introduceFormulaArguments
                          contextSorts condition)
                        (fun _ =>
                          FirstOrderProjection.introduceTermFormulaArguments
                            contextSorts thenTerm)
                        (fun _ _ =>
                          FirstOrderProjection.introduceTermFormulaArguments
                            contextSorts elseTerm)
                        (Term.ite sort) state
                        condition' conditionState thenTerm' thenState elseTerm' elseState
                        hCondition hThen hElse
                  have hElseIncluded :
                      FormulaArgumentState.DefinitionsIncluded elseState finalState := by
                    simpa [hRun] using hIncluded
                  have hThenIncluded :
                      FormulaArgumentState.DefinitionsIncluded thenState finalState :=
                    FormulaArgumentState.definitionsIncluded_trans
                      (FormulaArgumentState.introduceTermFormulaArguments_includes
                        contextSorts elseTerm thenState)
                      (by simpa [hElse] using hElseIncluded)
                  have hConditionIncluded :
                      FormulaArgumentState.DefinitionsIncluded conditionState finalState :=
                    FormulaArgumentState.definitionsIncluded_trans
                      (FormulaArgumentState.introduceTermFormulaArguments_includes
                        contextSorts thenTerm conditionState)
                      (by simpa [hThen] using hThenIncluded)
                  simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
                  have hMaxParts := Nat.max_le.mp hMax
                  have hBranchMax := Nat.max_le.mp hMaxParts.2
                  simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
                  have hConditionSem := ihCondition contextSorts state env
                    (by simpa [hCondition] using hConditionIncluded)
                    hMaxParts.1 hFree hScoped.1.1
                  have hThenEval := (ihThen).1 contextSorts conditionState env
                    (by simpa [hThen] using hThenIncluded)
                    hBranchMax.1 hFree hScoped.1.2
                  have hElseEval := (ihElse).1 contextSorts thenState env
                    (by simpa [hElse] using hElseIncluded)
                    hBranchMax.2 hFree hScoped.2
                  have hConditionSem' :
                      Formula.Satisfies
                          (Env.liftFormulaArgumentDefinitions
                            base env finalState.definitions) condition' ↔
                        Formula.Satisfies env condition := by
                    simpa [hCondition] using hConditionSem
                  have hThenEval' :
                      Term.eval
                          (Env.liftFormulaArgumentDefinitions
                            base env finalState.definitions) thenTerm' =
                        Term.eval env thenTerm := by
                    simpa [hThen] using hThenEval
                  have hElseEval' :
                      Term.eval
                          (Env.liftFormulaArgumentDefinitions
                            base env finalState.definitions) elseTerm' =
                        Term.eval env elseTerm := by
                    simpa [hElse] using hElseEval
                  have hConditionEq :
                      (Formula.eval
                          (Env.liftFormulaArgumentDefinitions
                            base env finalState.definitions) condition').holds =
                        (Formula.eval env condition).holds :=
                    propext hConditionSem'
                  simp only [hRun, Term.eval, Model.overrideFormulaArgumentDefinitions]
                  congr 1
    constructor
    · exact hTerm
    · intro contextSorts state env hIncluded hMax hFree hScoped
      simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state env
          (by
            simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
              hIncluded)
          hMax hFree hScoped
  case trueE =>
    intro contextSorts state env hIncluded hMax hFree hScoped
    rw [show
      (FirstOrderProjection.introduceFormulaArguments
        contextSorts Formula.trueE).run state = (Formula.trueE, state) by
      simpa only [FirstOrderProjection.introduceFormulaArguments] using
        FormulaArgumentState.stateM_run_pure_eq Formula.trueE state]
    simp [Formula.Satisfies, Formula.eval]
  case falseE =>
    intro contextSorts state env hIncluded hMax hFree hScoped
    rw [show
      (FirstOrderProjection.introduceFormulaArguments
        contextSorts Formula.falseE).run state = (Formula.falseE, state) by
      simpa only [FirstOrderProjection.introduceFormulaArguments] using
        FormulaArgumentState.stateM_run_pure_eq Formula.falseE state]
    simp [Formula.Satisfies, Formula.eval]
  case atom =>
    intro predicate args ihArgs contextSorts state env hIncluded hMax hFree hScoped
    cases hArgs :
        (FirstOrderProjection.introduceTermListFormulaArguments contextSorts args).run state with
    | mk args' argsState =>
        have hRun :
            (FirstOrderProjection.introduceFormulaArguments
              contextSorts (Formula.atom predicate args)).run state =
                (Formula.atom predicate args', argsState) := by
          simpa only [FirstOrderProjection.introduceFormulaArguments] using
            FormulaArgumentState.stateM_run_bind_pure_eq
              (FirstOrderProjection.introduceTermListFormulaArguments contextSorts args)
              (Formula.atom predicate) state args' argsState hArgs
        have hArgsIncluded :
            FormulaArgumentState.DefinitionsIncluded argsState finalState := by
          simpa [hRun] using hIncluded
        have hArgsScoped : Term.wellScopedListWith contextSorts args = true := by
          simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
          exact hScoped.2
        have hArgsEval := ihArgs contextSorts state env
          (by simpa [hArgs] using hArgsIncluded)
          (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
          hFree hArgsScoped
        have hArgsEval' :
            args'.map
                (Term.eval
                  (Env.liftFormulaArgumentDefinitions base env finalState.definitions)) =
              args.map (Term.eval env) := by
          simpa [hArgs] using hArgsEval
        simp only [hRun, Formula.Satisfies, Formula.eval,
          Model.overrideFormulaArgumentDefinitions]
        constructor
        · intro h
          exact Eq.mp (congrArg (M.predicateInterp predicate) hArgsEval') h
        · intro h
          exact Eq.mpr (congrArg (M.predicateInterp predicate) hArgsEval') h
  case equal =>
    intro sort left right ihLeft ihRight contextSorts state env
      hIncluded hMax hFree hScoped
    cases hLeft :
        (FirstOrderProjection.introduceTermFormulaArguments contextSorts left).run state with
    | mk left' leftState =>
        cases hRight :
            (FirstOrderProjection.introduceTermFormulaArguments contextSorts right).run
              leftState with
        | mk right' rightState =>
            have hRun :
                (FirstOrderProjection.introduceFormulaArguments
                  contextSorts (Formula.equal sort left right)).run state =
                    (Formula.equal sort left' right', rightState) := by
              simpa only [FirstOrderProjection.introduceFormulaArguments] using
                FormulaArgumentState.stateM_run_bind2_pure_eq
                  (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                  (Formula.equal sort) state left' leftState right' rightState hLeft hRight
            have hRightIncluded :
                FormulaArgumentState.DefinitionsIncluded rightState finalState := by
              simpa [hRun] using hIncluded
            have hLeftIncluded :
                FormulaArgumentState.DefinitionsIncluded leftState finalState :=
              FormulaArgumentState.definitionsIncluded_trans
                (FormulaArgumentState.introduceTermFormulaArguments_includes
                  contextSorts right leftState)
                (by simpa [hRight] using hRightIncluded)
            simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
            have hMaxParts := Nat.max_le.mp hMax
            simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
            have hLeftEval := (ihLeft).1 contextSorts state env
              (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
            have hRightEval := (ihRight).1 contextSorts leftState env
              (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
            have hLeftEval' :
                Term.eval
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) left' =
                  Term.eval env left := by
              simpa [hLeft] using hLeftEval
            have hRightEval' :
                Term.eval
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) right' =
                  Term.eval env right := by
              simpa [hRight] using hRightEval
            simp only [hRun, Formula.Satisfies, Formula.eval]
            constructor
            · intro h
              exact hLeftEval'.symm.trans (h.trans hRightEval')
            · intro h
              exact hLeftEval'.trans (h.trans hRightEval'.symm)
  case boolTerm =>
    intro term ihTerm contextSorts state env hIncluded hMax hFree hScoped
    cases hTerm :
        (FirstOrderProjection.introduceBoolViewTermFormulaArguments
          contextSorts term).run state with
    | mk term' termState =>
        have hRun :
            (FirstOrderProjection.introduceFormulaArguments
              contextSorts (Formula.boolTerm term)).run state =
                (Formula.boolTerm term', termState) := by
          simpa only [FirstOrderProjection.introduceFormulaArguments] using
            FormulaArgumentState.stateM_run_bind_pure_eq
              (FirstOrderProjection.introduceBoolViewTermFormulaArguments
                contextSorts term)
              Formula.boolTerm state term' termState hTerm
        have hTermIncluded :
            FormulaArgumentState.DefinitionsIncluded termState finalState := by
          simpa [hRun] using hIncluded
        have hTermEval := (ihTerm).2 contextSorts state env
          (by simpa [hTerm] using hTermIncluded)
          (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
          hFree (by simpa [Formula.wellScopedWith] using hScoped)
        have hTermEval' :
            Term.eval
                (Env.liftFormulaArgumentDefinitions base env finalState.definitions) term' =
              Term.eval env term := by
          simpa [hTerm] using hTermEval
        simp only [hRun, Formula.Satisfies, Formula.eval,
          Model.overrideFormulaArgumentDefinitions]
        constructor
        · intro h
          exact Eq.mp (congrArg M.boolHolds hTermEval') h
        · intro h
          exact Eq.mpr (congrArg M.boolHolds hTermEval') h
  case neg =>
    intro body ihBody contextSorts state env hIncluded hMax hFree hScoped
    cases hBody :
        (FirstOrderProjection.introduceFormulaArguments contextSorts body).run state with
    | mk body' bodyState =>
        have hRun :
            (FirstOrderProjection.introduceFormulaArguments
              contextSorts (Formula.neg body)).run state =
                (Formula.neg body', bodyState) := by
          simpa only [FirstOrderProjection.introduceFormulaArguments] using
            FormulaArgumentState.stateM_run_bind_pure_eq
              (FirstOrderProjection.introduceFormulaArguments contextSorts body)
              Formula.neg state body' bodyState hBody
        have hBodyIncluded :
            FormulaArgumentState.DefinitionsIncluded bodyState finalState := by
          simpa [hRun] using hIncluded
        have hBodySem := ihBody contextSorts state env
          (by simpa [hBody] using hBodyIncluded)
          (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
          hFree (by simpa [Formula.wellScopedWith] using hScoped)
        have hBodySem' :
            Formula.Satisfies
                (Env.liftFormulaArgumentDefinitions base env finalState.definitions) body' ↔
              Formula.Satisfies env body := by
          simpa [hBody] using hBodySem
        simpa only [hRun, Formula.Satisfies, Formula.eval] using not_congr hBodySem'
  case imp =>
    intro left right ihLeft ihRight contextSorts state env
      hIncluded hMax hFree hScoped
    cases hLeft :
        (FirstOrderProjection.introduceFormulaArguments contextSorts left).run state with
    | mk left' leftState =>
        cases hRight :
            (FirstOrderProjection.introduceFormulaArguments contextSorts right).run
              leftState with
        | mk right' rightState =>
            have hRun :
                (FirstOrderProjection.introduceFormulaArguments
                  contextSorts (Formula.imp left right)).run state =
                    (Formula.imp left' right', rightState) := by
              simpa only [FirstOrderProjection.introduceFormulaArguments] using
                FormulaArgumentState.stateM_run_bind2_pure_eq
                  (FirstOrderProjection.introduceFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceFormulaArguments contextSorts right)
                  Formula.imp state left' leftState right' rightState hLeft hRight
            have hRightIncluded :
                FormulaArgumentState.DefinitionsIncluded rightState finalState := by
              simpa [hRun] using hIncluded
            have hLeftIncluded :
                FormulaArgumentState.DefinitionsIncluded leftState finalState :=
              FormulaArgumentState.definitionsIncluded_trans
                (FormulaArgumentState.introduceFormulaArguments_includes
                  contextSorts right leftState)
                (by simpa [hRight] using hRightIncluded)
            simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
            have hMaxParts := Nat.max_le.mp hMax
            simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
            have hLeftSem := ihLeft contextSorts state env
              (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
            have hRightSem := ihRight contextSorts leftState env
              (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
            have hLeftSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) left' ↔
                  Formula.Satisfies env left := by
              simpa [hLeft] using hLeftSem
            have hRightSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) right' ↔
                  Formula.Satisfies env right := by
              simpa [hRight] using hRightSem
            simpa only [hRun, Formula.Satisfies, Formula.eval] using
              imp_congr hLeftSem' hRightSem'
  case conj =>
    intro left right ihLeft ihRight contextSorts state env
      hIncluded hMax hFree hScoped
    cases hLeft :
        (FirstOrderProjection.introduceFormulaArguments contextSorts left).run state with
    | mk left' leftState =>
        cases hRight :
            (FirstOrderProjection.introduceFormulaArguments contextSorts right).run
              leftState with
        | mk right' rightState =>
            have hRun :
                (FirstOrderProjection.introduceFormulaArguments
                  contextSorts (Formula.conj left right)).run state =
                    (Formula.conj left' right', rightState) := by
              simpa only [FirstOrderProjection.introduceFormulaArguments] using
                FormulaArgumentState.stateM_run_bind2_pure_eq
                  (FirstOrderProjection.introduceFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceFormulaArguments contextSorts right)
                  Formula.conj state left' leftState right' rightState hLeft hRight
            have hRightIncluded :
                FormulaArgumentState.DefinitionsIncluded rightState finalState := by
              simpa [hRun] using hIncluded
            have hLeftIncluded :
                FormulaArgumentState.DefinitionsIncluded leftState finalState :=
              FormulaArgumentState.definitionsIncluded_trans
                (FormulaArgumentState.introduceFormulaArguments_includes
                  contextSorts right leftState)
                (by simpa [hRight] using hRightIncluded)
            simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
            have hMaxParts := Nat.max_le.mp hMax
            simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
            have hLeftSem := ihLeft contextSorts state env
              (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
            have hRightSem := ihRight contextSorts leftState env
              (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
            have hLeftSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) left' ↔
                  Formula.Satisfies env left := by
              simpa [hLeft] using hLeftSem
            have hRightSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) right' ↔
                  Formula.Satisfies env right := by
              simpa [hRight] using hRightSem
            simpa only [hRun, Formula.Satisfies, Formula.eval] using
              and_congr hLeftSem' hRightSem'
  case disj =>
    intro left right ihLeft ihRight contextSorts state env
      hIncluded hMax hFree hScoped
    cases hLeft :
        (FirstOrderProjection.introduceFormulaArguments contextSorts left).run state with
    | mk left' leftState =>
        cases hRight :
            (FirstOrderProjection.introduceFormulaArguments contextSorts right).run
              leftState with
        | mk right' rightState =>
            have hRun :
                (FirstOrderProjection.introduceFormulaArguments
                  contextSorts (Formula.disj left right)).run state =
                    (Formula.disj left' right', rightState) := by
              simpa only [FirstOrderProjection.introduceFormulaArguments] using
                FormulaArgumentState.stateM_run_bind2_pure_eq
                  (FirstOrderProjection.introduceFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceFormulaArguments contextSorts right)
                  Formula.disj state left' leftState right' rightState hLeft hRight
            have hRightIncluded :
                FormulaArgumentState.DefinitionsIncluded rightState finalState := by
              simpa [hRun] using hIncluded
            have hLeftIncluded :
                FormulaArgumentState.DefinitionsIncluded leftState finalState :=
              FormulaArgumentState.definitionsIncluded_trans
                (FormulaArgumentState.introduceFormulaArguments_includes
                  contextSorts right leftState)
                (by simpa [hRight] using hRightIncluded)
            simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
            have hMaxParts := Nat.max_le.mp hMax
            simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
            have hLeftSem := ihLeft contextSorts state env
              (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
            have hRightSem := ihRight contextSorts leftState env
              (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
            have hLeftSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) left' ↔
                  Formula.Satisfies env left := by
              simpa [hLeft] using hLeftSem
            have hRightSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) right' ↔
                  Formula.Satisfies env right := by
              simpa [hRight] using hRightSem
            simpa only [hRun, Formula.Satisfies, Formula.eval] using
              or_congr hLeftSem' hRightSem'
  case iffE =>
    intro left right ihLeft ihRight contextSorts state env
      hIncluded hMax hFree hScoped
    cases hLeft :
        (FirstOrderProjection.introduceFormulaArguments contextSorts left).run state with
    | mk left' leftState =>
        cases hRight :
            (FirstOrderProjection.introduceFormulaArguments contextSorts right).run
              leftState with
        | mk right' rightState =>
            have hRun :
                (FirstOrderProjection.introduceFormulaArguments
                  contextSorts (Formula.iffE left right)).run state =
                    (Formula.iffE left' right', rightState) := by
              simpa only [FirstOrderProjection.introduceFormulaArguments] using
                FormulaArgumentState.stateM_run_bind2_pure_eq
                  (FirstOrderProjection.introduceFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceFormulaArguments contextSorts right)
                  Formula.iffE state left' leftState right' rightState hLeft hRight
            have hRightIncluded :
                FormulaArgumentState.DefinitionsIncluded rightState finalState := by
              simpa [hRun] using hIncluded
            have hLeftIncluded :
                FormulaArgumentState.DefinitionsIncluded leftState finalState :=
              FormulaArgumentState.definitionsIncluded_trans
                (FormulaArgumentState.introduceFormulaArguments_includes
                  contextSorts right leftState)
                (by simpa [hRight] using hRightIncluded)
            simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
            have hMaxParts := Nat.max_le.mp hMax
            simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
            have hLeftSem := ihLeft contextSorts state env
              (by simpa [hLeft] using hLeftIncluded) hMaxParts.1 hFree hScoped.1
            have hRightSem := ihRight contextSorts leftState env
              (by simpa [hRight] using hRightIncluded) hMaxParts.2 hFree hScoped.2
            have hLeftSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) left' ↔
                  Formula.Satisfies env left := by
              simpa [hLeft] using hLeftSem
            have hRightSem' :
                Formula.Satisfies
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) right' ↔
                  Formula.Satisfies env right := by
              simpa [hRight] using hRightSem
            simpa only [hRun, Formula.Satisfies, Formula.eval] using
              iff_congr hLeftSem' hRightSem'
  case forallE =>
    intro sort body ihBody contextSorts state env hIncluded hMax hFree hScoped
    cases hBody :
        (FirstOrderProjection.introduceFormulaArguments
          (sort :: contextSorts) body).run state with
    | mk body' bodyState =>
        have hRun :
            (FirstOrderProjection.introduceFormulaArguments
              contextSorts (Formula.forallE sort body)).run state =
                (Formula.forallE sort body', bodyState) := by
          simpa only [FirstOrderProjection.introduceFormulaArguments] using
            FormulaArgumentState.stateM_run_bind_pure_eq
              (FirstOrderProjection.introduceFormulaArguments
                (sort :: contextSorts) body)
              (Formula.forallE sort) state body' bodyState hBody
        have hBodyIncluded :
            FormulaArgumentState.DefinitionsIncluded bodyState finalState := by
          simpa [hRun] using hIncluded
        have hBodySem :
            ∀ value,
              Formula.Satisfies
                  ((Env.liftFormulaArgumentDefinitions
                    base env finalState.definitions).push value) body' ↔
                Formula.Satisfies (env.push value) body := by
          intro value
          simpa [hBody, Env.liftFormulaArgumentDefinitions_push] using
            ihBody (sort :: contextSorts) state (env.push value)
              (by simpa [hBody] using hBodyIncluded)
              (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
              (by intro target id; simpa [Env.push] using hFree target id)
              (by simpa [Formula.wellScopedWith] using hScoped)
        simp only [hRun, Formula.Satisfies, Formula.eval,
          Model.overrideFormulaArgumentDefinitions]
        constructor <;> intro h value hSort
        · exact (hBodySem value).mp (h value hSort)
        · exact (hBodySem value).mpr (h value hSort)
  case existsE =>
    intro sort body ihBody contextSorts state env hIncluded hMax hFree hScoped
    cases hBody :
        (FirstOrderProjection.introduceFormulaArguments
          (sort :: contextSorts) body).run state with
    | mk body' bodyState =>
        have hRun :
            (FirstOrderProjection.introduceFormulaArguments
              contextSorts (Formula.existsE sort body)).run state =
                (Formula.existsE sort body', bodyState) := by
          simpa only [FirstOrderProjection.introduceFormulaArguments] using
            FormulaArgumentState.stateM_run_bind_pure_eq
              (FirstOrderProjection.introduceFormulaArguments
                (sort :: contextSorts) body)
              (Formula.existsE sort) state body' bodyState hBody
        have hBodyIncluded :
            FormulaArgumentState.DefinitionsIncluded bodyState finalState := by
          simpa [hRun] using hIncluded
        have hBodySem :
            ∀ value,
              Formula.Satisfies
                  ((Env.liftFormulaArgumentDefinitions
                    base env finalState.definitions).push value) body' ↔
                Formula.Satisfies (env.push value) body := by
          intro value
          simpa [hBody, Env.liftFormulaArgumentDefinitions_push] using
            ihBody (sort :: contextSorts) state (env.push value)
              (by simpa [hBody] using hBodyIncluded)
              (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
              (by intro target id; simpa [Env.push] using hFree target id)
              (by simpa [Formula.wellScopedWith] using hScoped)
        simp only [hRun, Formula.Satisfies, Formula.eval,
          Model.overrideFormulaArgumentDefinitions]
        constructor
        · rintro ⟨value, hSort, hValue⟩
          exact ⟨value, hSort, (hBodySem value).mp hValue⟩
        · rintro ⟨value, hSort, hValue⟩
          exact ⟨value, hSort, (hBodySem value).mpr hValue⟩
  case nil =>
    intro contextSorts state env hIncluded hMax hFree hScoped
    rw [show
      (FirstOrderProjection.introduceTermListFormulaArguments
        contextSorts []).run state = ([], state) by
      simpa only [FirstOrderProjection.introduceTermListFormulaArguments] using
        FormulaArgumentState.stateM_run_pure_eq ([] : List Term) state]
    rfl
  case cons =>
    intro head tail ihHead ihTail contextSorts state env hIncluded hMax hFree hScoped
    cases hHead :
        (FirstOrderProjection.introduceTermFormulaArguments contextSorts head).run state with
    | mk head' headState =>
        cases hTail :
            (FirstOrderProjection.introduceTermListFormulaArguments contextSorts tail).run
              headState with
        | mk tail' tailState =>
            have hRun :
                (FirstOrderProjection.introduceTermListFormulaArguments
                  contextSorts (head :: tail)).run state =
                    (head' :: tail', tailState) := by
              simpa only [FirstOrderProjection.introduceTermListFormulaArguments] using
                FormulaArgumentState.stateM_run_bind2_pure_eq
                  (FirstOrderProjection.introduceTermFormulaArguments contextSorts head)
                  (fun _ =>
                    FirstOrderProjection.introduceTermListFormulaArguments
                      contextSorts tail)
                  List.cons state head' headState tail' tailState hHead hTail
            have hTailIncluded :
                FormulaArgumentState.DefinitionsIncluded tailState finalState := by
              simpa [hRun] using hIncluded
            have hHeadIncluded :
                FormulaArgumentState.DefinitionsIncluded headState finalState :=
              FormulaArgumentState.definitionsIncluded_trans
                (FormulaArgumentState.introduceTermListFormulaArguments_includes
                  contextSorts tail headState)
                (by simpa [hTail] using hTailIncluded)
            simp only [FirstOrderProjection.Term.maxFunctionListIdSucc] at hMax
            have hMaxParts := Nat.max_le.mp hMax
            simp only [Term.wellScopedListWith, Bool.and_eq_true] at hScoped
            have hHeadEval := (ihHead).1 contextSorts state env
              (by simpa [hHead] using hHeadIncluded) hMaxParts.1 hFree hScoped.1
            have hTailEval := ihTail contextSorts headState env
              (by simpa [hTail] using hTailIncluded) hMaxParts.2 hFree hScoped.2
            have hHeadEval' :
                Term.eval
                    (Env.liftFormulaArgumentDefinitions
                      base env finalState.definitions) head' =
                  Term.eval env head := by
              simpa [hHead] using hHeadEval
            have hTailEval' :
                tail'.map
                    (Term.eval
                      (Env.liftFormulaArgumentDefinitions
                        base env finalState.definitions)) =
                  tail.map (Term.eval env) := by
              simpa [hTail] using hTailEval
            simp only [hRun, List.map_cons]
            congr 1

/--
一次真实公式参数引入产生的定义公式，在最终定义扩张模型中恒成立。

这里把任意闭合量词环境降回基础模型，再同时使用替换项语义与递归转换语义；
因此定义左侧和右侧都精确回到同一个源公式真值。
-/
theorem introducedDefinition_definitionFormula_satisfies
    {M : Model} (contract : FoolLambdaContract M) (base : Env M)
    (cutoff : Nat) (finalState : FirstOrderProjection.FormulaArgumentState)
    (hFinalFresh : FormulaArgumentState.FreshFrom cutoff finalState)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula)
    (state formulaState : FirstOrderProjection.FormulaArgumentState)
    (hRun :
      (FirstOrderProjection.introduceFormulaArguments contextSorts sourceFormula).run state =
        (formula, formulaState))
    (hFormulaStateIncluded :
      FormulaArgumentState.DefinitionsIncluded formulaState finalState)
    (hDefinition :
      FormulaArgumentState.introducedDefinition
          formulaState contextSorts sourceFormula formula ∈
        finalState.definitions.toList)
    (hMax :
      FirstOrderProjection.Formula.maxFunctionIdSucc sourceFormula ≤ cutoff)
    (hScoped : Formula.wellScopedWith contextSorts sourceFormula = true) :
    Formula.Satisfies
      (Env.liftFormulaArgumentDefinitions base base finalState.definitions)
      (FormulaArgumentState.introducedDefinition
        formulaState contextSorts sourceFormula formula).definitionFormula := by
  let definition :=
    FormulaArgumentState.introducedDefinition
      formulaState contextSorts sourceFormula formula
  let extendedBase :=
    Env.liftFormulaArgumentDefinitions base base finalState.definitions
  apply Formula.satisfies_closeForall_of extendedBase extendedBase contextSorts
  intro extendedEnv hExtendedFree
  let env : Env M := {
    boundVal := extendedEnv.boundVal
    freeVal := extendedEnv.freeVal
  }
  have hFree : ∀ sort id, base.freeVal sort id = env.freeVal sort id := by
    intro sort id
    simpa [env, extendedBase] using (hExtendedFree sort id).symm
  have hLift :
      Env.liftFormulaArgumentDefinitions base env finalState.definitions =
        extendedEnv := by
    cases extendedEnv
    rfl
  have hFormulaSem :=
    introduceFormulaArguments_satisfies
      contract base cutoff finalState hFinalFresh sourceFormula
        contextSorts state env
        (by simpa [hRun] using hFormulaStateIncluded)
        hMax hFree hScoped
  rw [hLift] at hFormulaSem
  have hFormulaSem' :
      Formula.Satisfies extendedEnv formula ↔
        Formula.Satisfies env sourceFormula := by
    simpa [hRun] using hFormulaSem
  have hReplacement :=
    Term.eval_introducedDefinition_eq_quote
      contract base env cutoff formulaState finalState contextSorts
        sourceFormula formula hFinalFresh hDefinition hFree hScoped
  let extendedContract :=
    FoolLambdaContract.overrideFormulaArgumentDefinitions
      contract base finalState.definitions
  have hReplacementSem :
      Formula.Satisfies extendedEnv (.boolTerm definition.replacement) ↔
        Formula.Satisfies env sourceFormula := by
    simp only [Formula.Satisfies, Formula.eval]
    rw [← hLift, hReplacement]
    simpa only [Term.eval, Model.overrideFormulaArgumentDefinitions] using
      extendedContract.quote_holds (Formula.Satisfies env sourceFormula)
  change Formula.Satisfies extendedEnv
    ((Formula.boolTerm definition.replacement).iffE definition.formula)
  simpa only [Formula.Satisfies, Formula.eval] using
    hReplacementSem.trans hFormulaSem'.symm

/-- 某个构造状态中已经登记的全部定义公式都在给定环境中成立。 -/
def FormulaArgumentDefinitionsSatisfied
    {M : Model} (env : Env M)
    (state : FirstOrderProjection.FormulaArgumentState) : Prop :=
  ∀ definition ∈ state.definitions.toList,
    Formula.Satisfies env definition.definitionFormula

theorem formulaArgumentDefinitionsSatisfied_introBoolDefinition
    {M : Model} {env : Env M}
    (state : FirstOrderProjection.FormulaArgumentState)
    (contextSorts : List CoreSort) (sourceFormula formula : Formula)
    (hState : FormulaArgumentDefinitionsSatisfied env state)
    (hDefinition :
      Formula.Satisfies env
        (FormulaArgumentState.introducedDefinition
          state contextSorts sourceFormula formula).definitionFormula) :
    FormulaArgumentDefinitionsSatisfied env
      ((FirstOrderProjection.introBoolDefinition
        contextSorts sourceFormula formula).run state).2 := by
  intro definition hMem
  rw [FormulaArgumentState.introBoolDefinition_run] at hMem
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hOld | rfl
  · exact hState definition hOld
  · exact hDefinition

theorem stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
    {M : Model} {env : Env M} {α β : Type}
    (first : StateM FirstOrderProjection.FormulaArgumentState α)
    (constructor : α → β)
    (state finalState : FirstOrderProjection.FormulaArgumentState)
    (hIncluded :
      FormulaArgumentState.DefinitionsIncluded
        ((do
          let value ← first
          pure (constructor value)).run state).2
        finalState)
    (hFirstPreserves :
      ∀ nextState,
        FormulaArgumentState.DefinitionsIncluded
            (first.run nextState).2 finalState →
          FormulaArgumentDefinitionsSatisfied env nextState →
          FormulaArgumentDefinitionsSatisfied env (first.run nextState).2)
    (hState : FormulaArgumentDefinitionsSatisfied env state) :
    FormulaArgumentDefinitionsSatisfied env
      ((do
        let value ← first
        pure (constructor value)).run state).2 := by
  rw [FormulaArgumentState.stateM_run_bind_pure_snd]
  apply hFirstPreserves state
  · simpa [FormulaArgumentState.stateM_run_bind_pure_snd] using hIncluded
  · exact hState

theorem stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
    {M : Model} {env : Env M} {α β γ : Type}
    (first : StateM FirstOrderProjection.FormulaArgumentState α)
    (second : α → StateM FirstOrderProjection.FormulaArgumentState β)
    (constructor : α → β → γ)
    (state finalState : FirstOrderProjection.FormulaArgumentState)
    (hIncluded :
      FormulaArgumentState.DefinitionsIncluded
        ((do
          let firstValue ← first
          let secondValue ← second firstValue
          pure (constructor firstValue secondValue)).run state).2
        finalState)
    (hSecondIncludes :
      ∀ value nextState,
        FormulaArgumentState.DefinitionsIncluded nextState
          ((second value).run nextState).2)
    (hFirstPreserves :
      ∀ nextState,
        FormulaArgumentState.DefinitionsIncluded
            (first.run nextState).2 finalState →
          FormulaArgumentDefinitionsSatisfied env nextState →
          FormulaArgumentDefinitionsSatisfied env (first.run nextState).2)
    (hSecondPreserves :
      ∀ value nextState,
        FormulaArgumentState.DefinitionsIncluded
            ((second value).run nextState).2 finalState →
          FormulaArgumentDefinitionsSatisfied env nextState →
          FormulaArgumentDefinitionsSatisfied env ((second value).run nextState).2)
    (hState : FormulaArgumentDefinitionsSatisfied env state) :
    FormulaArgumentDefinitionsSatisfied env
      ((do
        let firstValue ← first
        let secondValue ← second firstValue
        pure (constructor firstValue secondValue)).run state).2 := by
  cases hFirst : first.run state with
  | mk firstValue firstState =>
      cases hSecond : (second firstValue).run firstState with
      | mk secondValue secondState =>
          have hRun :
              ((do
                let firstValue ← first
                let secondValue ← second firstValue
                pure (constructor firstValue secondValue)).run state) =
                  (constructor firstValue secondValue, secondState) :=
            FormulaArgumentState.stateM_run_bind2_pure_eq
              first second constructor state firstValue firstState secondValue secondState
                hFirst hSecond
          have hSecondIncluded :
              FormulaArgumentState.DefinitionsIncluded secondState finalState := by
            rw [hRun] at hIncluded
            exact hIncluded
          have hFirstIncluded :
              FormulaArgumentState.DefinitionsIncluded firstState finalState :=
            FormulaArgumentState.definitionsIncluded_trans
              (by simpa [hSecond] using hSecondIncludes firstValue firstState)
              hSecondIncluded
          have hFirstSatisfied :
              FormulaArgumentDefinitionsSatisfied env firstState := by
            simpa [hFirst] using hFirstPreserves state
              (by simpa [hFirst] using hFirstIncluded) hState
          have hSecondSatisfied :
              FormulaArgumentDefinitionsSatisfied env secondState := by
            simpa [hSecond] using hSecondPreserves firstValue firstState
              (by simpa [hSecond] using hSecondIncluded) hFirstSatisfied
          rw [hRun]
          exact hSecondSatisfied

theorem stateM_bind3_pure_preserves_formulaArgumentDefinitionsSatisfied
    {M : Model} {env : Env M} {α β γ δ : Type}
    (first : StateM FirstOrderProjection.FormulaArgumentState α)
    (second : α → StateM FirstOrderProjection.FormulaArgumentState β)
    (third : α → β → StateM FirstOrderProjection.FormulaArgumentState γ)
    (constructor : α → β → γ → δ)
    (state finalState : FirstOrderProjection.FormulaArgumentState)
    (hIncluded :
      FormulaArgumentState.DefinitionsIncluded
        ((do
          let firstValue ← first
          let secondValue ← second firstValue
          let thirdValue ← third firstValue secondValue
          pure (constructor firstValue secondValue thirdValue)).run state).2
        finalState)
    (hSecondIncludes :
      ∀ value nextState,
        FormulaArgumentState.DefinitionsIncluded nextState
          ((second value).run nextState).2)
    (hThirdIncludes :
      ∀ firstValue secondValue nextState,
        FormulaArgumentState.DefinitionsIncluded nextState
          ((third firstValue secondValue).run nextState).2)
    (hFirstPreserves :
      ∀ nextState,
        FormulaArgumentState.DefinitionsIncluded
            (first.run nextState).2 finalState →
          FormulaArgumentDefinitionsSatisfied env nextState →
          FormulaArgumentDefinitionsSatisfied env (first.run nextState).2)
    (hSecondPreserves :
      ∀ value nextState,
        FormulaArgumentState.DefinitionsIncluded
            ((second value).run nextState).2 finalState →
          FormulaArgumentDefinitionsSatisfied env nextState →
          FormulaArgumentDefinitionsSatisfied env ((second value).run nextState).2)
    (hThirdPreserves :
      ∀ firstValue secondValue nextState,
        FormulaArgumentState.DefinitionsIncluded
            ((third firstValue secondValue).run nextState).2 finalState →
          FormulaArgumentDefinitionsSatisfied env nextState →
          FormulaArgumentDefinitionsSatisfied env
            ((third firstValue secondValue).run nextState).2)
    (hState : FormulaArgumentDefinitionsSatisfied env state) :
    FormulaArgumentDefinitionsSatisfied env
      ((do
        let firstValue ← first
        let secondValue ← second firstValue
        let thirdValue ← third firstValue secondValue
        pure (constructor firstValue secondValue thirdValue)).run state).2 := by
  cases hFirst : first.run state with
  | mk firstValue firstState =>
      cases hSecond : (second firstValue).run firstState with
      | mk secondValue secondState =>
          cases hThird : (third firstValue secondValue).run secondState with
          | mk thirdValue thirdState =>
              have hRun :
                  ((do
                    let firstValue ← first
                    let secondValue ← second firstValue
                    let thirdValue ← third firstValue secondValue
                    pure (constructor firstValue secondValue thirdValue)).run state) =
                      (constructor firstValue secondValue thirdValue, thirdState) :=
                FormulaArgumentState.stateM_run_bind3_pure_eq
                  first second third constructor state firstValue firstState
                    secondValue secondState thirdValue thirdState hFirst hSecond hThird
              have hThirdIncluded :
                  FormulaArgumentState.DefinitionsIncluded thirdState finalState := by
                rw [hRun] at hIncluded
                exact hIncluded
              have hSecondIncluded :
                  FormulaArgumentState.DefinitionsIncluded secondState finalState :=
                FormulaArgumentState.definitionsIncluded_trans
                  (by
                    simpa [hThird] using
                      hThirdIncludes firstValue secondValue secondState)
                  hThirdIncluded
              have hFirstIncluded :
                  FormulaArgumentState.DefinitionsIncluded firstState finalState :=
                FormulaArgumentState.definitionsIncluded_trans
                  (by simpa [hSecond] using hSecondIncludes firstValue firstState)
                  hSecondIncluded
              have hFirstSatisfied :
                  FormulaArgumentDefinitionsSatisfied env firstState := by
                simpa [hFirst] using hFirstPreserves state
                  (by simpa [hFirst] using hFirstIncluded) hState
              have hSecondSatisfied :
                  FormulaArgumentDefinitionsSatisfied env secondState := by
                simpa [hSecond] using hSecondPreserves firstValue firstState
                  (by simpa [hSecond] using hSecondIncluded) hFirstSatisfied
              have hThirdSatisfied :
                  FormulaArgumentDefinitionsSatisfied env thirdState := by
                simpa [hThird] using
                  hThirdPreserves firstValue secondValue secondState
                    (by simpa [hThird] using hThirdIncluded) hSecondSatisfied
              rw [hRun]
              exact hThirdSatisfied

/-- 公式参数引入沿完整互递归遍历保持全部定义公式成立。 -/
theorem introduceFormulaArguments_preserves_definitions_satisfied
    {M : Model} (contract : FoolLambdaContract M) (base : Env M)
    (cutoff : Nat) (finalState : FirstOrderProjection.FormulaArgumentState)
    (hFinalFresh : FormulaArgumentState.FreshFrom cutoff finalState)
    (source : Formula) :
    ∀ contextSorts state,
      FormulaArgumentState.DefinitionsIncluded
        ((FirstOrderProjection.introduceFormulaArguments contextSorts source).run state).2
        finalState →
      FirstOrderProjection.Formula.maxFunctionIdSucc source ≤ cutoff →
      Formula.wellScopedWith contextSorts source = true →
      FormulaArgumentDefinitionsSatisfied
        (Env.liftFormulaArgumentDefinitions base base finalState.definitions) state →
      FormulaArgumentDefinitionsSatisfied
        (Env.liftFormulaArgumentDefinitions base base finalState.definitions)
        ((FirstOrderProjection.introduceFormulaArguments contextSorts source).run state).2 := by
  let extendedEnv :=
    Env.liftFormulaArgumentDefinitions base base finalState.definitions
  apply Formula.rec
    (motive_1 := fun term =>
      (∀ contextSorts state,
        FormulaArgumentState.DefinitionsIncluded
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts term).run state).2
          finalState →
        FirstOrderProjection.Term.maxFunctionIdSucc term ≤ cutoff →
        Term.wellScopedWith contextSorts term = true →
        FormulaArgumentDefinitionsSatisfied extendedEnv state →
        FormulaArgumentDefinitionsSatisfied extendedEnv
          ((FirstOrderProjection.introduceTermFormulaArguments contextSorts term).run state).2) ∧
      (∀ contextSorts state,
        FormulaArgumentState.DefinitionsIncluded
          ((FirstOrderProjection.introduceBoolViewTermFormulaArguments
            contextSorts term).run state).2 finalState →
        FirstOrderProjection.Term.maxFunctionIdSucc term ≤ cutoff →
        Term.wellScopedWith contextSorts term = true →
        FormulaArgumentDefinitionsSatisfied extendedEnv state →
        FormulaArgumentDefinitionsSatisfied extendedEnv
          ((FirstOrderProjection.introduceBoolViewTermFormulaArguments
            contextSorts term).run state).2))
    (motive_2 := fun formula => ∀ contextSorts state,
      FormulaArgumentState.DefinitionsIncluded
        ((FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state).2
        finalState →
      FirstOrderProjection.Formula.maxFunctionIdSucc formula ≤ cutoff →
      Formula.wellScopedWith contextSorts formula = true →
      FormulaArgumentDefinitionsSatisfied extendedEnv state →
      FormulaArgumentDefinitionsSatisfied extendedEnv
        ((FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state).2)
    (motive_3 := fun terms => ∀ contextSorts state,
      FormulaArgumentState.DefinitionsIncluded
        ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts terms).run state).2
        finalState →
      FirstOrderProjection.Term.maxFunctionListIdSucc terms ≤ cutoff →
      Term.wellScopedListWith contextSorts terms = true →
      FormulaArgumentDefinitionsSatisfied extendedEnv state →
      FormulaArgumentDefinitionsSatisfied extendedEnv
        ((FirstOrderProjection.introduceTermListFormulaArguments contextSorts terms).run state).2)
  case bvar =>
    intro sort index
    constructor <;>
      intro contextSorts state hIncluded hMax hScoped hState <;>
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
  case fvar =>
    intro sort id
    constructor <;>
      intro contextSorts state hIncluded hMax hScoped hState <;>
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
  case app =>
    intro symbol args ihArgs
    have hTerm :
        ∀ contextSorts state,
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.app symbol args)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.app symbol args) ≤ cutoff →
          Term.wellScopedWith contextSorts (Term.app symbol args) = true →
          FormulaArgumentDefinitionsSatisfied extendedEnv state →
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.app symbol args)).run state).2 := by
      intro contextSorts state hIncluded hMax hScoped hState
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMaxParts := Nat.max_le.mp hMax
      simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermListFormulaArguments contextSorts args)
          (Term.app symbol) state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun nextState hNextIncluded hNextState =>
            ihArgs contextSorts nextState hNextIncluded hMaxParts.2 hScoped.2 hNextState)
          hState
    constructor
    · exact hTerm
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hScoped hState
  case apply =>
    intro fn arg ihFn ihArg
    have hTerm :
        ∀ contextSorts state,
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.apply fn arg)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.apply fn arg) ≤ cutoff →
          Term.wellScopedWith contextSorts (Term.apply fn arg) = true →
          FormulaArgumentDefinitionsSatisfied extendedEnv state →
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.apply fn arg)).run state).2 := by
      intro contextSorts state hIncluded hMax hScoped hState
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMaxParts := Nat.max_le.mp hMax
      simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts fn)
          (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts arg)
          Term.apply state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun _ nextState =>
            FormulaArgumentState.introduceTermFormulaArguments_includes
              contextSorts arg nextState)
          (fun nextState hNextIncluded hNextState =>
            (ihFn).1 contextSorts nextState hNextIncluded hMaxParts.1
              hScoped.1 hNextState)
          (fun _ nextState hNextIncluded hNextState =>
            (ihArg).1 contextSorts nextState hNextIncluded hMaxParts.2
              hScoped.2 hNextState)
          hState
    constructor
    · exact hTerm
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hScoped hState
  case bool =>
    intro value
    constructor <;>
      intro contextSorts state hIncluded hMax hScoped hState <;>
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
        FirstOrderProjection.introduceTermFormulaArguments, StateT.run_pure] using hState
  case notE =>
    intro body ihBody
    have hTerm :
        ∀ contextSorts state,
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.notE body)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc (Term.notE body) ≤ cutoff →
          Term.wellScopedWith contextSorts (Term.notE body) = true →
          FormulaArgumentDefinitionsSatisfied extendedEnv state →
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.notE body)).run state).2 := by
      intro contextSorts state hIncluded hMax hScoped hState
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts body)
          Term.notE state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun nextState hNextIncluded hNextState =>
            (ihBody).1 contextSorts nextState hNextIncluded
              (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
              (by simpa [Term.wellScopedWith] using hScoped) hNextState)
          hState
    constructor
    · exact hTerm
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hScoped hState
  case andE =>
    intro left right ihLeft ihRight
    constructor
    · intro contextSorts state hIncluded hMax hScoped hState
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMaxParts := Nat.max_le.mp hMax
      simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
          (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
          Term.andE state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun _ nextState =>
            FormulaArgumentState.introduceTermFormulaArguments_includes
              contextSorts right nextState)
          (fun nextState hNextIncluded hNextState =>
            (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
              hScoped.1 hNextState)
          (fun _ nextState hNextIncluded hNextState =>
            (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
              hScoped.2 hNextState)
          hState
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        ((show
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.andE left right)).run state).2 from
            (by
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
                  (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                  Term.andE state finalState
                  (by
                    simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
                      FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
                  (fun _ nextState =>
                    FormulaArgumentState.introduceTermFormulaArguments_includes
                      contextSorts right nextState)
                  (fun nextState hNextIncluded hNextState =>
                    (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
                      hScoped.1 hNextState)
                  (fun _ nextState hNextIncluded hNextState =>
                    (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
                      hScoped.2 hNextState)
                  hState)))
  case orE =>
    intro left right ihLeft ihRight
    constructor
    · intro contextSorts state hIncluded hMax hScoped hState
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMaxParts := Nat.max_le.mp hMax
      simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
          (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
          Term.orE state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun _ nextState =>
            FormulaArgumentState.introduceTermFormulaArguments_includes
              contextSorts right nextState)
          (fun nextState hNextIncluded hNextState =>
            (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
              hScoped.1 hNextState)
          (fun _ nextState hNextIncluded hNextState =>
            (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
              hScoped.2 hNextState)
          hState
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        ((show
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.orE left right)).run state).2 from
            (by
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
                  (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                  Term.orE state finalState
                  (by
                    simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
                      FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
                  (fun _ nextState =>
                    FormulaArgumentState.introduceTermFormulaArguments_includes
                      contextSorts right nextState)
                  (fun nextState hNextIncluded hNextState =>
                    (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
                      hScoped.1 hNextState)
                  (fun _ nextState hNextIncluded hNextState =>
                    (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
                      hScoped.2 hNextState)
                  hState)))
  case impE =>
    intro left right ihLeft ihRight
    constructor
    · intro contextSorts state hIncluded hMax hScoped hState
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMaxParts := Nat.max_le.mp hMax
      simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
          (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
          Term.impE state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun _ nextState =>
            FormulaArgumentState.introduceTermFormulaArguments_includes
              contextSorts right nextState)
          (fun nextState hNextIncluded hNextState =>
            (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
              hScoped.1 hNextState)
          (fun _ nextState hNextIncluded hNextState =>
            (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
              hScoped.2 hNextState)
          hState
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        ((show
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.impE left right)).run state).2 from
            (by
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
                  (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                  Term.impE state finalState
                  (by
                    simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
                      FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
                  (fun _ nextState =>
                    FormulaArgumentState.introduceTermFormulaArguments_includes
                      contextSorts right nextState)
                  (fun nextState hNextIncluded hNextState =>
                    (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
                      hScoped.1 hNextState)
                  (fun _ nextState hNextIncluded hNextState =>
                    (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
                      hScoped.2 hNextState)
                  hState)))
  case iffE =>
    intro left right ihLeft ihRight
    constructor
    · intro contextSorts state hIncluded hMax hScoped hState
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMaxParts := Nat.max_le.mp hMax
      simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
          (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
          Term.iffE state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun _ nextState =>
            FormulaArgumentState.introduceTermFormulaArguments_includes
              contextSorts right nextState)
          (fun nextState hNextIncluded hNextState =>
            (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
              hScoped.1 hNextState)
          (fun _ nextState hNextIncluded hNextState =>
            (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
              hScoped.2 hNextState)
          hState
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        ((show
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.iffE left right)).run state).2 from
            (by
              simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
              have hMaxParts := Nat.max_le.mp hMax
              simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
              simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
                stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
                  (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
                  (fun _ =>
                    FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
                  Term.iffE state finalState
                  (by
                    simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments,
                      FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
                  (fun _ nextState =>
                    FormulaArgumentState.introduceTermFormulaArguments_includes
                      contextSorts right nextState)
                  (fun nextState hNextIncluded hNextState =>
                    (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
                      hScoped.1 hNextState)
                  (fun _ nextState hNextIncluded hNextState =>
                    (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
                      hScoped.2 hNextState)
                  hState)))
  case quote =>
    intro formula ihFormula
    constructor
    · intro contextSorts state hIncluded hMax hScoped hState
      cases hFormula :
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula).run state with
      | mk formula' formulaState =>
          let definition :=
            FormulaArgumentState.introducedDefinition
              formulaState contextSorts formula formula'
          have hQuoteIncluded :
              FormulaArgumentState.DefinitionsIncluded
                ((FirstOrderProjection.introBoolDefinition
                  contextSorts formula formula').run formulaState).2 finalState := by
            simpa [FirstOrderProjection.introduceTermFormulaArguments,
              StateT.run_bind, hFormula] using hIncluded
          have hFormulaIncluded :
              FormulaArgumentState.DefinitionsIncluded formulaState finalState :=
            FormulaArgumentState.definitionsIncluded_trans
              (FormulaArgumentState.freshDefinition_includes
                formulaState contextSorts formula formula')
              hQuoteIncluded
          have hFormulaSatisfied :=
            ihFormula contextSorts state
              (by simpa [hFormula] using hFormulaIncluded)
              (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
              (by simpa [Term.wellScopedWith] using hScoped) hState
          have hDefinition : definition ∈ finalState.definitions.toList := by
            apply hQuoteIncluded
            simpa [definition] using
              FormulaArgumentState.introducedDefinition_mem
                formulaState contextSorts formula formula'
          have hDefinitionSatisfied :
              Formula.Satisfies extendedEnv definition.definitionFormula := by
            simpa [extendedEnv, definition] using
              introducedDefinition_definitionFormula_satisfies
                contract base cutoff finalState hFinalFresh contextSorts formula formula'
                  state formulaState hFormula hFormulaIncluded hDefinition
                  (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
                  (by simpa [Term.wellScopedWith] using hScoped)
          have hAfterIntro :=
            formulaArgumentDefinitionsSatisfied_introBoolDefinition
              formulaState contextSorts formula formula'
                (by simpa [hFormula] using hFormulaSatisfied)
                (by simpa [definition] using hDefinitionSatisfied)
          simpa [FirstOrderProjection.introduceTermFormulaArguments,
            StateT.run_bind, hFormula] using hAfterIntro
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceFormulaArguments contextSorts formula)
          Term.quote state finalState
          (by
            simpa only [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
              hIncluded)
          (fun nextState hNextIncluded hNextState =>
            ihFormula contextSorts nextState hNextIncluded
              (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
              (by simpa [Term.wellScopedWith] using hScoped) hNextState)
          hState
  case lam =>
    intro domain codomain body ihBody
    have hTerm :
        ∀ contextSorts state,
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.lam domain codomain body)).run state).2 finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc
              (Term.lam domain codomain body) ≤ cutoff →
          Term.wellScopedWith contextSorts (Term.lam domain codomain body) = true →
          FormulaArgumentDefinitionsSatisfied extendedEnv state →
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.lam domain codomain body)).run state).2 := by
      intro contextSorts state hIncluded hMax hScoped hState
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceTermFormulaArguments
            (domain :: contextSorts) body)
          (Term.lam domain codomain) state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun nextState hNextIncluded hNextState =>
            (ihBody).1 (domain :: contextSorts) nextState hNextIncluded
              (by simpa [FirstOrderProjection.Term.maxFunctionIdSucc] using hMax)
              (by simpa [Term.wellScopedWith] using hScoped) hNextState)
          hState
    constructor
    · exact hTerm
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hScoped hState
  case ite =>
    intro sort condition thenTerm elseTerm ihCondition ihThen ihElse
    have hTerm :
        ∀ contextSorts state,
          FormulaArgumentState.DefinitionsIncluded
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.ite sort condition thenTerm elseTerm)).run state).2
              finalState →
          FirstOrderProjection.Term.maxFunctionIdSucc
              (Term.ite sort condition thenTerm elseTerm) ≤ cutoff →
          Term.wellScopedWith contextSorts
              (Term.ite sort condition thenTerm elseTerm) = true →
          FormulaArgumentDefinitionsSatisfied extendedEnv state →
          FormulaArgumentDefinitionsSatisfied extendedEnv
            ((FirstOrderProjection.introduceTermFormulaArguments
              contextSorts (Term.ite sort condition thenTerm elseTerm)).run state).2 := by
      intro contextSorts state hIncluded hMax hScoped hState
      simp only [FirstOrderProjection.Term.maxFunctionIdSucc] at hMax
      have hMaxParts := Nat.max_le.mp hMax
      have hBranchMax := Nat.max_le.mp hMaxParts.2
      simp only [Term.wellScopedWith, Bool.and_eq_true] at hScoped
      simpa only [FirstOrderProjection.introduceTermFormulaArguments] using
        stateM_bind3_pure_preserves_formulaArgumentDefinitionsSatisfied
          (FirstOrderProjection.introduceFormulaArguments contextSorts condition)
          (fun _ =>
            FirstOrderProjection.introduceTermFormulaArguments contextSorts thenTerm)
          (fun _ _ =>
            FirstOrderProjection.introduceTermFormulaArguments contextSorts elseTerm)
          (Term.ite sort) state finalState
          (by simpa only [FirstOrderProjection.introduceTermFormulaArguments] using hIncluded)
          (fun _ nextState =>
            FormulaArgumentState.introduceTermFormulaArguments_includes
              contextSorts thenTerm nextState)
          (fun _ _ nextState =>
            FormulaArgumentState.introduceTermFormulaArguments_includes
              contextSorts elseTerm nextState)
          (fun nextState hNextIncluded hNextState =>
            ihCondition contextSorts nextState hNextIncluded hMaxParts.1
              hScoped.1.1 hNextState)
          (fun _ nextState hNextIncluded hNextState =>
            (ihThen).1 contextSorts nextState hNextIncluded hBranchMax.1
              hScoped.1.2 hNextState)
          (fun _ _ nextState hNextIncluded hNextState =>
            (ihElse).1 contextSorts nextState hNextIncluded hBranchMax.2
              hScoped.2 hNextState)
          hState
    constructor
    · exact hTerm
    · intro contextSorts state hIncluded hMax hScoped hState
      simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using
        hTerm contextSorts state
          (by
            simpa [FirstOrderProjection.introduceBoolViewTermFormulaArguments] using hIncluded)
          hMax hScoped hState
  case trueE =>
    intro contextSorts state hIncluded hMax hScoped hState
    simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hState
  case falseE =>
    intro contextSorts state hIncluded hMax hScoped hState
    simpa [FirstOrderProjection.introduceFormulaArguments, StateT.run_pure] using hState
  case atom =>
    intro predicate args ihArgs contextSorts state hIncluded hMax hScoped hState
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceTermListFormulaArguments contextSorts args)
        (Formula.atom predicate) state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun nextState hNextIncluded hNextState =>
          ihArgs contextSorts nextState hNextIncluded
            (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
            (by
              simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
              exact hScoped.2)
            hNextState)
        hState
  case equal =>
    intro sort left right ihLeft ihRight contextSorts state
      hIncluded hMax hScoped hState
    simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
    have hMaxParts := Nat.max_le.mp hMax
    simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceTermFormulaArguments contextSorts left)
        (fun _ => FirstOrderProjection.introduceTermFormulaArguments contextSorts right)
        (Formula.equal sort) state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun _ nextState =>
          FormulaArgumentState.introduceTermFormulaArguments_includes
            contextSorts right nextState)
        (fun nextState hNextIncluded hNextState =>
          (ihLeft).1 contextSorts nextState hNextIncluded hMaxParts.1
            hScoped.1 hNextState)
        (fun _ nextState hNextIncluded hNextState =>
          (ihRight).1 contextSorts nextState hNextIncluded hMaxParts.2
            hScoped.2 hNextState)
        hState
  case boolTerm =>
    intro term ihTerm contextSorts state hIncluded hMax hScoped hState
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceBoolViewTermFormulaArguments contextSorts term)
        Formula.boolTerm state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun nextState hNextIncluded hNextState =>
          (ihTerm).2 contextSorts nextState hNextIncluded
            (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
            (by simpa [Formula.wellScopedWith] using hScoped) hNextState)
        hState
  case neg =>
    intro body ihBody contextSorts state hIncluded hMax hScoped hState
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceFormulaArguments contextSorts body)
        Formula.neg state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun nextState hNextIncluded hNextState =>
          ihBody contextSorts nextState hNextIncluded
            (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
            (by simpa [Formula.wellScopedWith] using hScoped) hNextState)
        hState
  case imp =>
    intro left right ihLeft ihRight contextSorts state
      hIncluded hMax hScoped hState
    simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
    have hMaxParts := Nat.max_le.mp hMax
    simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceFormulaArguments contextSorts left)
        (fun _ => FirstOrderProjection.introduceFormulaArguments contextSorts right)
        Formula.imp state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun _ nextState =>
          FormulaArgumentState.introduceFormulaArguments_includes
            contextSorts right nextState)
        (fun nextState hNextIncluded hNextState =>
          ihLeft contextSorts nextState hNextIncluded hMaxParts.1 hScoped.1 hNextState)
        (fun _ nextState hNextIncluded hNextState =>
          ihRight contextSorts nextState hNextIncluded hMaxParts.2 hScoped.2 hNextState)
        hState
  case conj =>
    intro left right ihLeft ihRight contextSorts state
      hIncluded hMax hScoped hState
    simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
    have hMaxParts := Nat.max_le.mp hMax
    simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceFormulaArguments contextSorts left)
        (fun _ => FirstOrderProjection.introduceFormulaArguments contextSorts right)
        Formula.conj state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun _ nextState =>
          FormulaArgumentState.introduceFormulaArguments_includes
            contextSorts right nextState)
        (fun nextState hNextIncluded hNextState =>
          ihLeft contextSorts nextState hNextIncluded hMaxParts.1 hScoped.1 hNextState)
        (fun _ nextState hNextIncluded hNextState =>
          ihRight contextSorts nextState hNextIncluded hMaxParts.2 hScoped.2 hNextState)
        hState
  case disj =>
    intro left right ihLeft ihRight contextSorts state
      hIncluded hMax hScoped hState
    simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
    have hMaxParts := Nat.max_le.mp hMax
    simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceFormulaArguments contextSorts left)
        (fun _ => FirstOrderProjection.introduceFormulaArguments contextSorts right)
        Formula.disj state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun _ nextState =>
          FormulaArgumentState.introduceFormulaArguments_includes
            contextSorts right nextState)
        (fun nextState hNextIncluded hNextState =>
          ihLeft contextSorts nextState hNextIncluded hMaxParts.1 hScoped.1 hNextState)
        (fun _ nextState hNextIncluded hNextState =>
          ihRight contextSorts nextState hNextIncluded hMaxParts.2 hScoped.2 hNextState)
        hState
  case iffE =>
    intro left right ihLeft ihRight contextSorts state
      hIncluded hMax hScoped hState
    simp only [FirstOrderProjection.Formula.maxFunctionIdSucc] at hMax
    have hMaxParts := Nat.max_le.mp hMax
    simp only [Formula.wellScopedWith, Bool.and_eq_true] at hScoped
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceFormulaArguments contextSorts left)
        (fun _ => FirstOrderProjection.introduceFormulaArguments contextSorts right)
        Formula.iffE state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun _ nextState =>
          FormulaArgumentState.introduceFormulaArguments_includes
            contextSorts right nextState)
        (fun nextState hNextIncluded hNextState =>
          ihLeft contextSorts nextState hNextIncluded hMaxParts.1 hScoped.1 hNextState)
        (fun _ nextState hNextIncluded hNextState =>
          ihRight contextSorts nextState hNextIncluded hMaxParts.2 hScoped.2 hNextState)
        hState
  case forallE =>
    intro sort body ihBody contextSorts state hIncluded hMax hScoped hState
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceFormulaArguments (sort :: contextSorts) body)
        (Formula.forallE sort) state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun nextState hNextIncluded hNextState =>
          ihBody (sort :: contextSorts) nextState hNextIncluded
            (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
            (by simpa [Formula.wellScopedWith] using hScoped) hNextState)
        hState
  case existsE =>
    intro sort body ihBody contextSorts state hIncluded hMax hScoped hState
    simpa only [FirstOrderProjection.introduceFormulaArguments] using
      stateM_bind_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceFormulaArguments (sort :: contextSorts) body)
        (Formula.existsE sort) state finalState
        (by simpa only [FirstOrderProjection.introduceFormulaArguments] using hIncluded)
        (fun nextState hNextIncluded hNextState =>
          ihBody (sort :: contextSorts) nextState hNextIncluded
            (by simpa [FirstOrderProjection.Formula.maxFunctionIdSucc] using hMax)
            (by simpa [Formula.wellScopedWith] using hScoped) hNextState)
        hState
  case nil =>
    intro contextSorts state hIncluded hMax hScoped hState
    simpa [FirstOrderProjection.introduceTermListFormulaArguments, StateT.run_pure] using hState
  case cons =>
    intro head tail ihHead ihTail contextSorts state hIncluded hMax hScoped hState
    simp only [FirstOrderProjection.Term.maxFunctionListIdSucc] at hMax
    have hMaxParts := Nat.max_le.mp hMax
    simp only [Term.wellScopedListWith, Bool.and_eq_true] at hScoped
    simpa only [FirstOrderProjection.introduceTermListFormulaArguments] using
      stateM_bind2_pure_preserves_formulaArgumentDefinitionsSatisfied
        (FirstOrderProjection.introduceTermFormulaArguments contextSorts head)
        (fun _ =>
          FirstOrderProjection.introduceTermListFormulaArguments contextSorts tail)
        List.cons state finalState
        (by
          simpa only [FirstOrderProjection.introduceTermListFormulaArguments] using hIncluded)
        (fun _ nextState =>
          FormulaArgumentState.introduceTermListFormulaArguments_includes
            contextSorts tail nextState)
        (fun nextState hNextIncluded hNextState =>
          (ihHead).1 contextSorts nextState hNextIncluded hMaxParts.1
            hScoped.1 hNextState)
        (fun _ nextState hNextIncluded hNextState =>
          ihTail contextSorts nextState hNextIncluded hMaxParts.2
            hScoped.2 hNextState)
        hState
end Model

namespace Formula

theorem satisfies_conjunctionList_of
    {M : Model} (env : Env M) (formulas : List Formula)
    (hFormulas : ∀ formula ∈ formulas, Formula.Satisfies env formula) :
    Formula.Satisfies env (Formula.conjunctionList formulas) := by
  induction formulas with
  | nil =>
      simp [Formula.conjunctionList, Formula.Satisfies, Formula.eval]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [Formula.conjunctionList] using hFormulas head (by simp)
      | cons next rest =>
          simp only [Formula.conjunctionList,
            Formula.Satisfies, Formula.eval]
          constructor
          · exact hFormulas head (by simp)
          · apply ih
            intro formula hFormula
            exact hFormulas formula (by simp [hFormula])

end Formula

namespace Model

/-- 合法源公式的整条公式参数定义化结果在定义扩张模型中成立。 -/
theorem formulaArgumentTrace_build_target_satisfies
    {M : Model} (contract : FoolLambdaContract M) (base : Env M)
    (source : Formula) (hCheck : Formula.check? source = true)
    (hSource : Formula.Satisfies base source) :
    let trace := FirstOrderProjection.FormulaArgumentTrace.build source
    Formula.Satisfies
      (Env.liftFormulaArgumentDefinitions base base trace.definitions)
      trace.target := by
  let cutoff := FirstOrderProjection.Formula.maxFunctionIdSucc source + 1
  let initial : FirstOrderProjection.FormulaArgumentState := {
    nextDefinition := cutoff
  }
  cases hRun :
      (FirstOrderProjection.introduceFormulaArguments [] source).run initial with
  | mk targetCore finalState =>
      have hFresh : FormulaArgumentState.FreshFrom cutoff finalState := by
        simpa [cutoff, initial, hRun] using
          FormulaArgumentState.build_state_fresh source
      have hScoped : Formula.wellScopedWith [] source = true :=
        Formula.wellScopedWith_of_checkWith [] source hCheck
      have hFinalIncluded :
          FormulaArgumentState.DefinitionsIncluded finalState finalState := by
        intro definition hDefinition
        exact hDefinition
      have hInitialSatisfied :
          FormulaArgumentDefinitionsSatisfied
            (Env.liftFormulaArgumentDefinitions base base finalState.definitions) initial := by
        intro definition hDefinition
        simp [initial] at hDefinition
      have hDefinitions :=
        introduceFormulaArguments_preserves_definitions_satisfied
          contract base cutoff finalState hFresh source [] initial
            (by simpa [hRun] using hFinalIncluded)
            (by simp [cutoff])
            hScoped hInitialSatisfied
      have hDefinitions' :
          FormulaArgumentDefinitionsSatisfied
            (Env.liftFormulaArgumentDefinitions base base finalState.definitions)
            finalState := by
        simpa [hRun] using hDefinitions
      have hCoreSem :=
        introduceFormulaArguments_satisfies
          contract base cutoff finalState hFresh source [] initial base
            (by simpa [hRun] using hFinalIncluded)
            (by simp [cutoff])
            (by intro sort id; rfl)
            hScoped
      have hCore :
          Formula.Satisfies
            (Env.liftFormulaArgumentDefinitions base base finalState.definitions)
            targetCore := by
        have hCoreSem' :
            Formula.Satisfies
                (Env.liftFormulaArgumentDefinitions base base finalState.definitions)
                targetCore ↔
              Formula.Satisfies base source := by
          simpa [hRun] using hCoreSem
        exact hCoreSem'.mpr hSource
      have hTarget :
          Formula.Satisfies
            (Env.liftFormulaArgumentDefinitions base base finalState.definitions)
            (FirstOrderProjection.FormulaArgumentTrace.withDefinitions
              targetCore finalState.definitions) := by
        apply Formula.satisfies_conjunctionList_of
        intro formula hFormula
        simp only [List.mem_cons, List.mem_map] at hFormula
        rcases hFormula with rfl | ⟨definition, hDefinition, rfl⟩
        · exact hCore
        · exact hDefinitions' definition hDefinition
      have hTrace :
          FirstOrderProjection.FormulaArgumentTrace.build source = {
            source := source
            targetCore := targetCore
            target :=
              FirstOrderProjection.FormulaArgumentTrace.withDefinitions
                targetCore finalState.definitions
            intros := finalState.intros
            definitions := finalState.definitions
          } := by
        simp [FirstOrderProjection.FormulaArgumentTrace.build, cutoff, initial, hRun]
      rw [hTrace]
      exact hTarget

theorem formulaArgumentTrace_build_target_foolLambdaSatisfiable
    (source : Formula) (hCheck : Formula.check? source = true)
    (hSource : Formula.FoolLambdaSatisfiable.{x} source) :
    Formula.FoolLambdaSatisfiable.{x}
      (FirstOrderProjection.FormulaArgumentTrace.build source).target := by
  rcases hSource with ⟨M, base, ⟨contract⟩, hFree, hSource⟩
  let trace := FirstOrderProjection.FormulaArgumentTrace.build source
  let extendedEnv :=
    Env.liftFormulaArgumentDefinitions base base trace.definitions
  refine ⟨Model.overrideFormulaArgumentDefinitions M base trace.definitions,
    extendedEnv, ?_, ?_, ?_⟩
  · exact ⟨FoolLambdaContract.overrideFormulaArgumentDefinitions
      contract base trace.definitions⟩
  · intro sort id
    exact hFree sort id
  · simpa [trace, extendedEnv] using
      formulaArgumentTrace_build_target_satisfies
        contract base source hCheck hSource

end Model

end Semantics

namespace FirstOrderProjection

namespace FormulaArgumentTrace

def buildState (source : Formula) : FormulaArgumentState :=
  (introduceFormulaArguments [] source).run
    { nextDefinition := Formula.maxFunctionIdSucc source + 1 } |>.2

@[simp]
theorem buildState_definitions (source : Formula) :
    (buildState source).definitions = (build source).definitions :=
  rfl

@[simp]
theorem buildState_intros (source : Formula) :
    (buildState source).intros = (build source).intros :=
  rfl

end FormulaArgumentTrace

private theorem array_eq_of_toList_eq {α : Type} {left right : Array α}
    (h : left.toList = right.toList) : left = right := by
  exact Array.toList_inj.mp h

namespace BoolDefinition

theorem eq_eq_true {left right : BoolDefinition} :
    BoolDefinition.eq left right = true ↔ left = right := by
  cases left
  cases right
  simp [BoolDefinition.eq, SyntaxEq.formulaEq_eq_true, beq_iff_eq, and_assoc]

theorem listEq_eq_true {left right : List BoolDefinition} :
    BoolDefinition.listEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [BoolDefinition.listEq]
  | cons head tail ih =>
      cases right with
      | nil =>
          simp [BoolDefinition.listEq]
      | cons head' tail' =>
          simp [BoolDefinition.listEq, eq_eq_true, ih]

theorem arrayEq_eq_true {left right : Array BoolDefinition} :
    BoolDefinition.arrayEq left right = true ↔ left = right := by
  unfold BoolDefinition.arrayEq
  constructor
  · exact fun h => array_eq_of_toList_eq (listEq_eq_true.mp h)
  · intro h
    subst right
    exact listEq_eq_true.mpr rfl

end BoolDefinition

namespace FormulaArgumentIntro

theorem eq_eq_true {left right : FormulaArgumentIntro} :
    FormulaArgumentIntro.eq left right = true ↔ left = right := by
  cases left
  cases right
  simp [FormulaArgumentIntro.eq, SyntaxEq.formulaEq_eq_true,
    SyntaxEq.termEq_eq_true, beq_iff_eq, and_assoc]

theorem listEq_eq_true {left right : List FormulaArgumentIntro} :
    FormulaArgumentIntro.listEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [FormulaArgumentIntro.listEq]
  | cons head tail ih =>
      cases right with
      | nil =>
          simp [FormulaArgumentIntro.listEq]
      | cons head' tail' =>
          simp [FormulaArgumentIntro.listEq, eq_eq_true, ih]

theorem arrayEq_eq_true {left right : Array FormulaArgumentIntro} :
    FormulaArgumentIntro.arrayEq left right = true ↔ left = right := by
  unfold FormulaArgumentIntro.arrayEq
  constructor
  · exact fun h => array_eq_of_toList_eq (listEq_eq_true.mp h)
  · intro h
    subst right
    exact listEq_eq_true.mpr rfl

end FormulaArgumentIntro

namespace FormulaArgumentTrace

private theorem eq_of_fields {left right : FormulaArgumentTrace}
    (hSource : left.source = right.source)
    (hTargetCore : left.targetCore = right.targetCore)
    (hTarget : left.target = right.target)
    (hIntros : left.intros = right.intros)
    (hDefinitions : left.definitions = right.definitions) :
    left = right := by
  cases left
  cases right
  simp_all

theorem eq_build_of_check {trace : FormulaArgumentTrace}
    (hCheck : FormulaArgumentTrace.check trace = true) :
    trace = FormulaArgumentTrace.build trace.source := by
  let expected := FormulaArgumentTrace.build trace.source
  have h := hCheck
  simp only [FormulaArgumentTrace.check, Bool.and_eq_true_iff,
    SyntaxEq.formulaEq_eq_true, FormulaArgumentIntro.arrayEq_eq_true,
    BoolDefinition.arrayEq_eq_true] at h
  have hTargetCoreEq := h.1.1.1.1.1.2
  have hTargetEq := h.1.1.1.1.2
  have hIntrosEq := h.1.1.1.2
  have hDefinitionsEq := h.1.1.2
  exact eq_of_fields rfl hTargetCoreEq hTargetEq hIntrosEq hDefinitionsEq

/-- checked 公式参数 trace 把带 FOOL/lambda 合同的源模型保守扩张到目标。 -/
theorem target_foolLambdaSatisfiable_of_check
    {trace : FormulaArgumentTrace}
    (hCheck : FormulaArgumentTrace.check trace = true)
    (hSource : Semantics.Formula.FoolLambdaSatisfiable.{x} trace.source) :
    Semantics.Formula.FoolLambdaSatisfiable.{x} trace.target := by
  have hSourceCheck : trace.source.check? = true := by
    simp only [FormulaArgumentTrace.check, Bool.and_eq_true_iff] at hCheck
    exact hCheck.1.1.1.1.1.1.1.1
  have hTrace := eq_build_of_check hCheck
  rw [hTrace]
  exact Semantics.Model.formulaArgumentTrace_build_target_foolLambdaSatisfiable
    trace.source hSourceCheck hSource

end FormulaArgumentTrace

end FirstOrderProjection

end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
