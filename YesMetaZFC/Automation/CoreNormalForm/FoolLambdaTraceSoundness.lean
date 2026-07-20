import YesMetaZFC.Automation.CoreNormalForm.AntiPrenexSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaSoundness

/-!
# FOOL / lambda normalization trace soundness

本模块证明 `CoreNormalForm` 可计算 trace 的逐步语义保持。项级 FOOL 化简需要先
知道被化简项确实位于布尔 sort，因此这里同时建立 locally nameless 环境与
`inferSortWith` 的类型语义不变量。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm
namespace Semantics

universe x

namespace Env

/-- bound 环境遵守当前 locally nameless sort 上下文。 -/
def RespectsBound {M : Model} (bound : List CoreSort) (env : Env M) : Prop :=
  ∀ index sort, TypeCheck.lookupBound? bound index = some sort →
    M.sortInterp sort (env.boundVal index)

/-- free 环境遵守变量自身携带的 sort 标注。 -/
def RespectsFree {M : Model} (env : Env M) : Prop :=
  ∀ sort id, M.sortInterp sort (env.freeVal sort id)

/-- 向上下文与环境同时压入一个同 sort 值后，bound 不变量保持。 -/
theorem respectsBound_push {M : Model} {bound : List CoreSort} {env : Env M}
    (hBound : RespectsBound bound env) {sort : CoreSort} {value : M.Carrier}
    (hValue : M.sortInterp sort value) :
    RespectsBound (sort :: bound) (env.push value) := by
  intro index target hLookup
  cases index with
  | zero =>
      simp only [TypeCheck.lookupBound?] at hLookup
      cases hLookup
      exact hValue
  | succ previous =>
      simp only [TypeCheck.lookupBound?, Env.push_bound_succ] at hLookup ⊢
      exact hBound previous target hLookup

/-- `push` 不改变 free 环境不变量。 -/
theorem respectsFree_push {M : Model} {env : Env M}
    (hFree : RespectsFree env) (value : M.Carrier) :
    RespectsFree (env.push value) := by
  intro sort id
  simpa only [Env.push_free] using hFree sort id

/-- 在深度零插入值与直接压入 bound stack 逐点一致。 -/
theorem insertAt_zero_eq_push {M : Model} (env : Env M) (value : M.Carrier) :
    env.insertAt 0 value = env.push value := by
  cases env with
  | mk boundValue freeValue =>
      simp only [Env.insertAt, Env.push]
      congr 1
      funext index
      cases index <;> simp

/-- 删除零个 bound 值不改变环境。 -/
theorem drop_zero_eq {M : Model} (env : Env M) :
    env.drop 0 = env := by
  cases env with
  | mk boundValue freeValue =>
      simp only [Env.drop]
      congr 1

end Env

/-- 成功拆出箭头 sort 时，原 sort 就是对应箭头。 -/
theorem coreSort_eq_arrow_of_arrow?_eq_some {sort domain codomain : CoreSort}
    (hArrow :
      _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.CoreSort.arrow? sort =
        some (domain, codomain)) :
    sort = .arrow domain codomain := by
  cases sort with
  | object | bool | prop | named =>
      simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.CoreSort.arrow?] at hArrow
  | arrow actualDomain actualCodomain =>
      simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.CoreSort.arrow?] at hArrow
      rcases hArrow with ⟨rfl, rfl⟩
      rfl

/-- `CoreSort` 的派生布尔相等在 `true` 分支给出真实相等。 -/
theorem coreSort_eq_of_beq_eq_true {left right : CoreSort}
    (hEqual : (left == right) = true) :
    left = right := by
  exact beq_iff_eq.mp hEqual

namespace Term

/-- 通过 `inferSortWith` 的项，其解释落在推断出的 sort 中。 -/
theorem eval_mem_of_inferSortWith {M : Model} (contract : FoolLambdaContract M)
    (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env) :
    ∀ (term : Term) (sort : CoreSort),
      Term.inferSortWith bound term = some sort →
        M.sortInterp sort (Term.eval env term)
  | Term.bvar annotated index, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      cases hLookup : TypeCheck.lookupBound? bound index with
      | none =>
          simp [hLookup] at hSort
      | some expected =>
          simp [hLookup] at hSort
          have hAnnotated : expected = annotated := hSort.1
          have hResult : annotated = sort := hSort.2
          subst expected
          subst sort
          simpa only [Term.eval] using hBound index annotated hLookup
  | Term.fvar annotated id, sort, hSort => by
      simp only [Term.inferSortWith, Option.some.injEq] at hSort
      subst sort
      simpa only [Term.eval] using hFree annotated id
  | Term.app symbol arguments, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      split at hSort <;> try contradiction
      cases hArgumentSorts : Term.inferSortListWith bound arguments with
      | none =>
          simp [hArgumentSorts] at hSort
      | some argumentSorts =>
          simp [hArgumentSorts] at hSort
          have hResult : symbol.outputSort = sort := hSort.2
          subst sort
          simpa only [Term.eval] using
            contract.function_sort symbol (arguments.map (Term.eval env))
  | Term.apply fn argument, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      cases hFnSort : Term.inferSortWith bound fn with
      | none =>
          simp [hFnSort] at hSort
      | some fnSort =>
          simp only [hFnSort] at hSort
          cases hArgumentSort : Term.inferSortWith bound argument with
          | none =>
              simp [hArgumentSort] at hSort
          | some argumentSort =>
              simp only [hArgumentSort] at hSort
              cases hArrow : fnSort.arrow? with
              | none =>
                  simp [hArrow] at hSort
              | some pair =>
                  rcases pair with ⟨domain, codomain⟩
                  simp [hArrow] at hSort
                  have hArgumentDomain : argumentSort = domain := hSort.1
                  have hResult : codomain = sort := hSort.2
                  subst argumentSort
                  subst sort
                  have hFn :
                      M.sortInterp (.arrow domain codomain) (Term.eval env fn) := by
                    have hFnSortShape : fnSort = .arrow domain codomain :=
                      coreSort_eq_arrow_of_arrow?_eq_some hArrow
                    subst fnSort
                    exact eval_mem_of_inferSortWith contract bound env hBound hFree
                      fn (.arrow domain codomain) hFnSort
                  have hArgument :
                      M.sortInterp domain (Term.eval env argument) :=
                    eval_mem_of_inferSortWith contract bound env hBound hFree
                      argument domain hArgumentSort
                  simpa only [Term.eval] using
                    contract.apply_sort domain codomain _ _ hFn hArgument
  | Term.bool value, sort, hSort => by
      simp only [Term.inferSortWith, Option.some.injEq] at hSort
      subst sort
      simpa only [Term.eval] using contract.bool_sort value
  | Term.notE body, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      cases hBodySort : Term.inferSortWith bound body with
      | none =>
          simp [hBodySort] at hSort
      | some bodySort =>
          simp [hBodySort] at hSort
          have hBodyBool : bodySort = .bool := hSort.1
          have hResult : CoreSort.bool = sort := hSort.2
          subst bodySort
          subst sort
          simpa only [Term.eval] using contract.not_sort _ <|
            eval_mem_of_inferSortWith contract bound env hBound hFree body .bool hBodySort
  | Term.andE left right, sort, hSort
  | Term.orE left right, sort, hSort
  | Term.impE left right, sort, hSort
  | Term.iffE left right, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      cases hLeftSort : Term.inferSortWith bound left with
      | none =>
          simp [hLeftSort] at hSort
      | some leftSort =>
          simp only [hLeftSort] at hSort
          cases hRightSort : Term.inferSortWith bound right with
          | none =>
              simp [hRightSort] at hSort
          | some rightSort =>
              simp [hRightSort] at hSort
              have hLeftBool : leftSort = .bool := hSort.1.1
              have hRightBool : rightSort = .bool := hSort.1.2
              have hResult : CoreSort.bool = sort := hSort.2
              subst leftSort
              subst rightSort
              subst sort
              have hLeft :=
                eval_mem_of_inferSortWith contract bound env hBound hFree
                  left .bool hLeftSort
              have hRight :=
                eval_mem_of_inferSortWith contract bound env hBound hFree
                  right .bool hRightSort
              simp only [Term.eval]
              first
              | exact contract.and_sort _ _ hLeft hRight
              | exact contract.or_sort _ _ hLeft hRight
              | exact contract.imp_sort _ _ hLeft hRight
              | exact contract.iff_sort _ _ hLeft hRight
  | Term.quote formula, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      split at hSort
      next =>
        simp only [Option.some.injEq] at hSort
        subst sort
        simpa only [Term.eval] using contract.quote_sort (Formula.eval env formula).holds
      next =>
        simp at hSort
  | Term.lam domain codomain body, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      cases hBodySort : Term.inferSortWith (domain :: bound) body with
      | none =>
          simp [hBodySort] at hSort
      | some bodySort =>
          simp [hBodySort] at hSort
          have hBodyCodomain : bodySort = codomain := hSort.1
          have hResult : CoreSort.arrow domain codomain = sort := hSort.2
          subst bodySort
          subst sort
          simp only [Term.eval]
          apply contract.lambda_sort
          intro value hValue
          exact eval_mem_of_inferSortWith contract (domain :: bound) (env.push value)
            (Env.respectsBound_push hBound hValue) (Env.respectsFree_push hFree value)
            body codomain hBodySort
  | Term.ite targetSort condition thenTerm elseTerm, sort, hSort => by
      simp only [Term.inferSortWith] at hSort
      split at hSort
      next =>
        simp at hSort
      next =>
        cases hThenSort : Term.inferSortWith bound thenTerm with
        | none =>
            simp [hThenSort] at hSort
        | some thenSort =>
            simp only [hThenSort] at hSort
            cases hElseSort : Term.inferSortWith bound elseTerm with
            | none =>
                simp [hElseSort] at hSort
            | some elseSort =>
                simp [hElseSort] at hSort
                have hThenTarget : thenSort = targetSort := hSort.1.1
                have hElseTarget : elseSort = targetSort := hSort.1.2
                have hResult : targetSort = sort := hSort.2
                subst thenSort
                subst elseSort
                subst sort
                simpa only [Term.eval] using
                  contract.ite_sort targetSort _ _ _
                    (eval_mem_of_inferSortWith contract bound env hBound hFree
                      thenTerm targetSort hThenSort)
                    (eval_mem_of_inferSortWith contract bound env hBound hFree
                      elseTerm targetSort hElseSort)

end Term

namespace Term

/-- 两个项在指定模型与环境下解释为同一值。 -/
def SemanticallyEqual {M : Model} (env : Env M) (left right : Term) : Prop :=
  Term.eval env left = Term.eval env right

/-- 两个项列表逐项解释为同一参数列表。 -/
def ListSemanticallyEqual {M : Model} (env : Env M)
    (left right : List Term) : Prop :=
  left.map (Term.eval env) = right.map (Term.eval env)

/-- 布尔 sort 中的两个值只要真值等价，就由合同外延性得到真实相等。 -/
theorem eval_eq_of_bool_holds_iff {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (left right : Term)
    (hLeft : M.sortInterp .bool (Term.eval env left))
    (hRight : M.sortInterp .bool (Term.eval env right))
    (hHolds :
      M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) :
    SemanticallyEqual env left right :=
  (contract.bool_extensionality _ _ hLeft hRight).mpr hHolds

/-- 两端都通过布尔 sort 推断时，真值等价即可回放为项解释相等。 -/
theorem eval_eq_of_inferred_bool_holds_iff {M : Model}
    (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    (left right : Term)
    (hLeft : Term.inferSortWith bound left = some .bool)
    (hRight : Term.inferSortWith bound right = some .bool)
    (hHolds :
      M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) :
    SemanticallyEqual env left right :=
  eval_eq_of_bool_holds_iff contract env left right
    (eval_mem_of_inferSortWith contract bound env hBound hFree left .bool hLeft)
    (eval_mem_of_inferSortWith contract bound env hBound hFree right .bool hRight)
    hHolds

/-- 合法函数应用可反解出定义域、函数 sort 与实参 sort。 -/
theorem inferSortWith_apply_parts {bound : List CoreSort} {fn arg : Term}
    {result : CoreSort}
    (hSort : Term.inferSortWith bound (.apply fn arg) = some result) :
    ∃ domain,
      Term.inferSortWith bound fn = some (.arrow domain result) ∧
      Term.inferSortWith bound arg = some domain := by
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

/-- 顶层 beta 的实例化结果与 lambda application 解释相同。 -/
theorem eval_beta_instantiate {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (domain codomain : CoreSort) (body argument : Term)
    (hBody :
      ∀ value, M.sortInterp domain value →
        M.sortInterp codomain (Term.eval (env.push value) body))
    (hArgument : M.sortInterp domain (Term.eval env argument)) :
    Term.eval env (.apply (.lam domain codomain body) argument) =
      Term.eval env (Term.instantiate argument body) := by
  rw [Term.eval_beta contract env domain codomain body argument hBody hArgument]
  simp only [Term.instantiate, Term.eval_instantiateAt]
  rw [Env.drop_zero_eq]
  rw [Env.insertAt_zero_eq_push]

mutual
  /-- eta checker 的出现性检查与公共 NNF 辅助定义一致。 -/
  theorem etaTerm_occursBVarAt_eq (depth : Nat) (term : Term) :
      Eta.Term.occursBVarAt depth term = Term.occursBVarAt depth term := by
    cases term <;>
      simp [Eta.Term.occursBVarAt, Term.occursBVarAt,
        etaTerm_occursBVarAt_eq, etaFormula_occursBVarAt_eq,
        etaTerm_occursBVarListAt_eq]

  theorem etaFormula_occursBVarAt_eq (depth : Nat) (formula : Formula) :
      Eta.Formula.occursBVarAt depth formula = Formula.occursBVarAt depth formula := by
    cases formula <;>
      simp [Eta.Formula.occursBVarAt, Formula.occursBVarAt,
        etaTerm_occursBVarAt_eq, etaFormula_occursBVarAt_eq,
        etaTerm_occursBVarListAt_eq]

  theorem etaTerm_occursBVarListAt_eq (depth : Nat) (terms : List Term) :
      Eta.Term.occursBVarListAt depth terms = Term.occursBVarListAt depth terms := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp [Eta.Term.occursBVarListAt, Term.occursBVarListAt,
          etaTerm_occursBVarAt_eq, etaTerm_occursBVarListAt_eq]
end

mutual
  /-- eta checker 的 binder 下移与公共 NNF 辅助定义一致。 -/
  theorem etaTerm_lowerAbove_eq (cutoff : Nat) (term : Term) :
      Eta.Term.lowerAbove cutoff term = Term.lowerAbove cutoff term := by
    cases term <;>
      simp [Eta.Term.lowerAbove, Term.lowerAbove,
        etaTerm_lowerAbove_eq, etaFormula_lowerAbove_eq,
        etaTerm_lowerListAbove_eq]

  theorem etaFormula_lowerAbove_eq (cutoff : Nat) (formula : Formula) :
      Eta.Formula.lowerAbove cutoff formula = Formula.lowerAbove cutoff formula := by
    cases formula <;>
      simp [Eta.Formula.lowerAbove, Formula.lowerAbove,
        etaTerm_lowerAbove_eq, etaFormula_lowerAbove_eq,
        etaTerm_lowerListAbove_eq]

  theorem etaTerm_lowerListAbove_eq (cutoff : Nat) (terms : List Term) :
      Eta.Term.lowerListAbove cutoff terms = Term.lowerListAbove cutoff terms := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp [Eta.Term.lowerListAbove, Term.lowerListAbove,
          etaTerm_lowerAbove_eq, etaTerm_lowerListAbove_eq]
end

/-- `Eta.contract?` 成功时，收缩前后的项解释相等。 -/
theorem eval_eta_contract? {M : Model} (contract : FoolLambdaContract M)
    (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    (domain codomain : CoreSort) (body contracted : Term)
    (hBodySort :
      Term.inferSortWith (domain :: bound) body = some codomain)
    (hContract : Eta.contract? domain body = some contracted) :
    Term.eval env (.lam domain codomain body) = Term.eval env contracted := by
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
                have hEtaOccurs : Eta.Term.occursBVarAt 0 fn = false :=
                  (Bool.not_eq_true' _).mp hGuard.2
                have hOccurs : Term.occursBVarAt 0 fn = false := by
                  rw [← etaTerm_occursBVarAt_eq]
                  exact hEtaOccurs
                obtain ⟨functionDomain, hFnSort, hArgumentSort⟩ :=
                  inferSortWith_apply_parts hBodySort
                simp [Term.inferSortWith, TypeCheck.lookupBound?] at hArgumentSort
                have hFunctionDomain : functionDomain = domain := by
                  exact hArgumentSort.symm
                subst functionDomain
                let witness := Classical.choose (M.sortNonempty domain)
                have hWitness : M.sortInterp domain witness :=
                  Classical.choose_spec (M.sortNonempty domain)
                have hFnSemantic :
                    M.sortInterp (.arrow domain codomain)
                      (Term.eval (env.push witness) fn) :=
                  eval_mem_of_inferSortWith contract (domain :: bound)
                    (env.push witness) (Env.respectsBound_push hBound hWitness)
                    (Env.respectsFree_push hFree witness)
                    fn (.arrow domain codomain) hFnSort
                have hFnEval :
                    Term.eval (env.push witness) fn =
                      Term.eval env (Term.lowerAbove 0 fn) := by
                  rw [← Env.insertAt_zero_eq_push env witness]
                  rw [← Term.eval_lowerAbove_of_not_occurs env 0 witness fn hOccurs]
                have hContractedSort :
                    M.sortInterp (.arrow domain codomain)
                      (Term.eval env (Term.lowerAbove 0 fn)) := by
                  rw [← hFnEval]
                  exact hFnSemantic
                simp only [Term.eval]
                have hFunction :
                    (fun value =>
                        M.applyInterp (Term.eval (env.push value) fn) value) =
                      (fun value =>
                        M.applyInterp (Term.eval env (Term.lowerAbove 0 fn)) value) := by
                  funext value
                  rw [← Env.insertAt_zero_eq_push env value]
                  rw [← Term.eval_lowerAbove_of_not_occurs env 0 value fn hOccurs]
                simp only [Env.push_bound_zero]
                rw [hFunction,
                  contract.eta domain codomain _ hContractedSort,
                  etaTerm_lowerAbove_eq]
              next =>
                simp at hContract
          | succ index =>
              simp [Eta.contract?] at hContract
      | _ =>
          simp [Eta.contract?] at hContract
  | _ =>
      simp [Eta.contract?] at hContract

/-- 二元 FOOL 项成功通过 sort 推断时，结果 sort 必为布尔。 -/
theorem inferSortWith_andE_eq_bool {bound : List CoreSort} {left right : Term}
    {sort : CoreSort}
    (hSort : Term.inferSortWith bound (.andE left right) = some sort) :
    sort = .bool := by
  cases hLeft : Term.inferSortWith bound left with
  | none =>
      simp [Term.inferSortWith, hLeft] at hSort
  | some leftSort =>
      cases hRight : Term.inferSortWith bound right with
      | none =>
          simp [Term.inferSortWith, hLeft, hRight] at hSort
      | some rightSort =>
          simp [Term.inferSortWith, hLeft, hRight] at hSort
          exact hSort.2.symm

/-- 其余二元 FOOL connective 与 `andE` 共享同一个 sort 推断结构。 -/
theorem inferSortWith_orE_eq_bool {bound : List CoreSort} {left right : Term}
    {sort : CoreSort}
    (hSort : Term.inferSortWith bound (.orE left right) = some sort) :
    sort = .bool :=
  inferSortWith_andE_eq_bool (by
    simpa only [Term.inferSortWith] using hSort)

theorem inferSortWith_impE_eq_bool {bound : List CoreSort} {left right : Term}
    {sort : CoreSort}
    (hSort : Term.inferSortWith bound (.impE left right) = some sort) :
    sort = .bool :=
  inferSortWith_andE_eq_bool (by
    simpa only [Term.inferSortWith] using hSort)

theorem inferSortWith_iffE_eq_bool {bound : List CoreSort} {left right : Term}
    {sort : CoreSort}
    (hSort : Term.inferSortWith bound (.iffE left right) = some sort) :
    sort = .bool :=
  inferSortWith_andE_eq_bool (by
    simpa only [Term.inferSortWith] using hSort)

/-- 合法 quote 项的推断结果固定为布尔 sort。 -/
theorem inferSortWith_quote_eq_bool {bound : List CoreSort} {formula : Formula}
    {sort : CoreSort}
    (hSort : Term.inferSortWith bound (.quote formula) = some sort) :
    sort = .bool := by
  cases hCheck : Formula.checkWith bound formula <;>
    simp [Term.inferSortWith, hCheck] at hSort
  exact hSort.symm

/-- 合法条件项的推断结果就是语法节点声明的分支 sort。 -/
theorem inferSortWith_ite_eq_declared {bound : List CoreSort} {declared result : CoreSort}
    {condition : Formula} {thenTerm elseTerm : Term}
    (hSort :
      Term.inferSortWith bound (.ite declared condition thenTerm elseTerm) =
        some result) :
    result = declared := by
  cases hCheck : Formula.checkWith bound condition <;>
    simp [Term.inferSortWith, hCheck] at hSort
  cases hThen : Term.inferSortWith bound thenTerm with
  | none =>
      simp [hThen] at hSort
  | some thenSort =>
      cases hElse : Term.inferSortWith bound elseTerm with
      | none =>
          simp [hThen, hElse] at hSort
      | some elseSort =>
          simp [hThen, hElse] at hSort
          exact hSort.2.symm

/-- 合法否定项同时固定结果 sort 与子项 sort。 -/
theorem inferSortWith_notE_parts {bound : List CoreSort} {body : Term}
    {result : CoreSort}
    (hSort : Term.inferSortWith bound (.notE body) = some result) :
    result = .bool ∧ Term.inferSortWith bound body = some .bool := by
  cases hBody : Term.inferSortWith bound body <;>
    simp [Term.inferSortWith, hBody] at hSort
  subst_vars
  simp_all

/-- 合法二元 FOOL 项固定结果与两个子项的布尔 sort。 -/
theorem inferSortWith_andE_parts {bound : List CoreSort} {left right : Term}
    {result : CoreSort}
    (hSort : Term.inferSortWith bound (.andE left right) = some result) :
    result = .bool ∧
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool := by
  cases hLeft : Term.inferSortWith bound left <;>
    cases hRight : Term.inferSortWith bound right <;>
    simp [Term.inferSortWith, hLeft, hRight] at hSort
  subst_vars
  simp_all

/-- 其余二元 FOOL 项与 `andE` 共享同一 typed inversion。 -/
theorem inferSortWith_orE_parts {bound : List CoreSort} {left right : Term}
    {result : CoreSort}
    (hSort : Term.inferSortWith bound (.orE left right) = some result) :
    result = .bool ∧
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool :=
  inferSortWith_andE_parts (by
    simpa only [Term.inferSortWith] using hSort)

theorem inferSortWith_impE_parts {bound : List CoreSort} {left right : Term}
    {result : CoreSort}
    (hSort : Term.inferSortWith bound (.impE left right) = some result) :
    result = .bool ∧
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool :=
  inferSortWith_andE_parts (by
    simpa only [Term.inferSortWith] using hSort)

theorem inferSortWith_iffE_parts {bound : List CoreSort} {left right : Term}
    {result : CoreSort}
    (hSort : Term.inferSortWith bound (.iffE left right) = some result) :
    result = .bool ∧
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool :=
  inferSortWith_andE_parts (by
    simpa only [Term.inferSortWith] using hSort)

/-- 合法 quote 项同时给出被 quote 公式的 checker 事实。 -/
theorem inferSortWith_quote_parts {bound : List CoreSort} {formula : Formula}
    {result : CoreSort}
    (hSort : Term.inferSortWith bound (.quote formula) = some result) :
    result = .bool ∧ Formula.checkWith bound formula = true := by
  cases hCheck : Formula.checkWith bound formula <;>
    simp [Term.inferSortWith, hCheck] at hSort
  subst_vars
  simp_all

/-- 合法 lambda 固定箭头 sort，并给出 binder 下 body 的 sort。 -/
theorem inferSortWith_lam_parts {bound : List CoreSort}
    {domain codomain result : CoreSort} {body : Term}
    (hSort : Term.inferSortWith bound (.lam domain codomain body) = some result) :
    result = .arrow domain codomain ∧
      Term.inferSortWith (domain :: bound) body = some codomain := by
  cases hBody : Term.inferSortWith (domain :: bound) body <;>
    simp [Term.inferSortWith, hBody] at hSort
  subst_vars
  simp_all

/-- 通过整体 application checker 恢复 typed β replay 所需的两个语义前提。 -/
theorem eval_beta_instantiate_of_inferSortWith {M : Model}
    (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    (domain codomain : CoreSort) (body argument : Term) {resultSort : CoreSort}
    (hSource :
      Term.inferSortWith bound
        (.apply (.lam domain codomain body) argument) = some resultSort) :
    Term.eval env (.apply (.lam domain codomain body) argument) =
      Term.eval env (Term.instantiate argument body) := by
  obtain ⟨actualDomain, hLambda, hArgument⟩ :=
    inferSortWith_apply_parts hSource
  obtain ⟨hArrow, hBody⟩ := inferSortWith_lam_parts hLambda
  cases hArrow
  exact eval_beta_instantiate contract env domain codomain body argument
    (by
      intro value hValue
      exact eval_mem_of_inferSortWith contract (domain :: bound)
        (env.push value) (Env.respectsBound_push hBound hValue)
        (Env.respectsFree_push hFree value) body codomain hBody)
    (eval_mem_of_inferSortWith contract bound env hBound hFree
      argument domain hArgument)

/-- 合法条件项固定条件 checker 与两个分支的声明 sort。 -/
theorem inferSortWith_ite_parts {bound : List CoreSort}
    {declared result : CoreSort} {condition : Formula} {thenTerm elseTerm : Term}
    (hSort :
      Term.inferSortWith bound (.ite declared condition thenTerm elseTerm) =
        some result) :
    result = declared ∧
      Formula.checkWith bound condition = true ∧
      Term.inferSortWith bound thenTerm = some declared ∧
      Term.inferSortWith bound elseTerm = some declared := by
  cases hCheck : Formula.checkWith bound condition <;>
    simp [Term.inferSortWith, hCheck] at hSort
  cases hThen : Term.inferSortWith bound thenTerm <;>
    cases hElse : Term.inferSortWith bound elseTerm <;>
    simp [hThen, hElse] at hSort
  subst_vars
  simp_all

/-- 合法函数符号应用至少给出参数 sort 列表的成功推断。 -/
theorem inferSortWith_app_parts {bound : List CoreSort} {symbol : FunctionSymbol}
    {args : List Term} {result : CoreSort}
    (hSort : Term.inferSortWith bound (.app symbol args) = some result) :
    result = symbol.outputSort ∧
      ∃ sorts, Term.inferSortListWith bound args = some sorts := by
  by_cases hArity : !symbol.arityOk || args.length != symbol.arity
  · simp [Term.inferSortWith, hArity] at hSort
  · cases hArgs : Term.inferSortListWith bound args with
    | none =>
        simp [Term.inferSortWith, hArity, hArgs] at hSort
    | some sorts =>
        simp [Term.inferSortWith, hArity, hArgs] at hSort
        exact ⟨hSort.2.symm, sorts, rfl⟩

/-- 成功推断非空项列表时，可反解出头项和尾列表的 sort。 -/
theorem inferSortListWith_cons_parts {bound : List CoreSort} {term : Term}
    {rest : List Term} {sorts : List CoreSort}
    (hSorts : Term.inferSortListWith bound (term :: rest) = some sorts) :
    ∃ sort restSorts,
      sorts = sort :: restSorts ∧
      Term.inferSortWith bound term = some sort ∧
      Term.inferSortListWith bound rest = some restSorts := by
  cases hTerm : Term.inferSortWith bound term <;>
    cases hRest : Term.inferSortListWith bound rest <;>
    simp [Term.inferSortListWith, hTerm, hRest] at hSorts
  subst_vars
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- 同一项的成功 sort 推断具有唯一性。 -/
theorem inferSortWith_unique {bound : List CoreSort} {term : Term}
    {left right : CoreSort}
    (hLeft : Term.inferSortWith bound term = some left)
    (hRight : Term.inferSortWith bound term = some right) :
    left = right := by
  rw [hLeft] at hRight
  exact Option.some.inj hRight

@[simp]
theorem inferSortWith_bool_eq_bool {bound : List CoreSort} {value : Bool} :
    Term.inferSortWith bound (.bool value) = some .bool := rfl

@[simp]
theorem inferSortWith_notE_eq_bool_iff {bound : List CoreSort} {body : Term} :
    Term.inferSortWith bound (.notE body) = some .bool ↔
      Term.inferSortWith bound body = some .bool := by
  cases hBody : Term.inferSortWith bound body <;>
    simp [Term.inferSortWith, hBody]

@[simp]
theorem inferSortWith_andE_eq_bool_iff {bound : List CoreSort}
    {left right : Term} :
    Term.inferSortWith bound (.andE left right) = some .bool ↔
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool := by
  cases hLeft : Term.inferSortWith bound left <;>
    cases hRight : Term.inferSortWith bound right <;>
    simp [Term.inferSortWith, hLeft, hRight]

@[simp]
theorem inferSortWith_orE_eq_bool_iff {bound : List CoreSort}
    {left right : Term} :
    Term.inferSortWith bound (.orE left right) = some .bool ↔
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool := by
  simpa only [Term.inferSortWith] using
    (inferSortWith_andE_eq_bool_iff (bound := bound) (left := left) (right := right))

@[simp]
theorem inferSortWith_impE_eq_bool_iff {bound : List CoreSort}
    {left right : Term} :
    Term.inferSortWith bound (.impE left right) = some .bool ↔
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool := by
  simpa only [Term.inferSortWith] using
    (inferSortWith_andE_eq_bool_iff (bound := bound) (left := left) (right := right))

@[simp]
theorem inferSortWith_iffE_eq_bool_iff {bound : List CoreSort}
    {left right : Term} :
    Term.inferSortWith bound (.iffE left right) = some .bool ↔
      Term.inferSortWith bound left = some .bool ∧
      Term.inferSortWith bound right = some .bool := by
  simpa only [Term.inferSortWith] using
    (inferSortWith_andE_eq_bool_iff (bound := bound) (left := left) (right := right))

@[simp]
theorem inferSortWith_quote_eq_bool_iff {bound : List CoreSort}
    {formula : Formula} :
    Term.inferSortWith bound (.quote formula) = some .bool ↔
      Formula.checkWith bound formula = true := by
  cases hCheck : Formula.checkWith bound formula <;>
    simp [Term.inferSortWith, hCheck]

/-- 项根部重写在 typed 环境中保持解释。 -/
theorem rewriteRootTerm?_sound {M : Model} (contract : FoolLambdaContract M)
    (config : Config) (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    {source target : Term} {rule : StepRule} {resultSort : CoreSort}
    (hSource : Term.inferSortWith bound source = some resultSort)
    (hTarget : Term.inferSortWith bound target = some resultSort)
    (hStep : rewriteRootTerm? config source = some (rule, target)) :
    SemanticallyEqual env source target := by
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
          have hResult : resultSort = .bool :=
            (inferSortWith_notE_parts hSource).1
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
          · simp only [Term.eval, contract.not_holds, contract.quote_holds,
              Formula.eval]
      next =>
        simp at hStep
  | andE left right =>
      have hSort : resultSort = .bool := inferSortWith_andE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree
        (.andE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.and_holds,
            contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;>
            simp_all)
        all_goals
          try (rcases hStep with ⟨_, hTargetEq⟩ <;>
            simp_all)
        all_goals
          grind [Term.eval, Formula.eval, contract.and_holds, contract.bool_holds,
            contract.quote_holds]
      next =>
        simp at hStep
  | orE left right =>
      have hSort : resultSort = .bool := inferSortWith_orE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree
        (.orE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.or_holds,
            contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;>
            simp_all)
        all_goals
          grind [Term.eval, Formula.eval, contract.or_holds, contract.bool_holds,
            contract.quote_holds]
      next =>
        simp at hStep
  | impE left right =>
      have hSort : resultSort = .bool := inferSortWith_impE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree
        (.impE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.imp_holds,
            contract.not_holds, contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;>
            simp_all)
        all_goals
          grind [Term.eval, Formula.eval, contract.imp_holds, contract.not_holds,
            contract.bool_holds, contract.quote_holds]
      next =>
        simp at hStep
  | iffE left right =>
      have hSort : resultSort = .bool := inferSortWith_iffE_eq_bool hSource
      subst resultSort
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree
        (.iffE left right) target hSource hTarget
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases left <;> cases right <;>
          simp_all [SyntaxEq.termEq_eq_true, Term.eval, contract.iff_holds,
            contract.not_holds, contract.bool_holds, contract.quote_holds] <;>
          try cases ‹Bool› <;>
          simp_all <;>
          try (split at hStep <;>
            simp_all [Term.eval, contract.iff_holds, contract.not_holds,
              contract.bool_holds, contract.quote_holds])
        case bool.bool leftValue rightValue =>
          cases leftValue <;> cases rightValue
          all_goals
            rcases hStep with ⟨_, rfl⟩ <;>
              simp [Term.eval, contract.not_holds, contract.bool_holds]
        all_goals
          try simp_all [Term.eval, Formula.eval, contract.iff_holds, contract.not_holds,
            contract.bool_holds, contract.quote_holds]
        all_goals
          try
            rcases hStep with ⟨_, hTargetEq⟩
            rw [← hTargetEq]
            simp [Term.eval, Formula.eval, contract.iff_holds, contract.not_holds,
              contract.quote_holds]
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
      apply eval_eq_of_inferred_bool_holds_iff contract bound env hBound hFree
        (.quote formula) target hSource hTarget
      cases formula <;>
        simp [rewriteRootTerm?] at hStep <;>
        grind [Term.eval, Formula.eval, contract.quote_holds, contract.bool_holds]
  | lam domain codomain body =>
      simp only [rewriteRootTerm?] at hStep
      split at hStep
      next =>
        cases hContract : Eta.contract? domain body with
        | none =>
            simp [hContract] at hStep
        | some contracted =>
            simp [hContract] at hStep
            rcases hStep with ⟨_, hTargetEq⟩
            subst target
            exact eval_eta_contract? contract bound env hBound hFree
              domain codomain body contracted
              (inferSortWith_lam_parts hSource).2 hContract
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
          · by_cases hFool : config.fool = true
            · cases sort with
              | object | prop | named | arrow =>
                  simp [hEqual, hFool] at hStep
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
                        simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition,
                          contract.quote_holds,
                          contract.bool_holds]
                    · subst thenTerm
                      simp [hEqual, hFool] at hStep
                      rcases hStep with ⟨_, hTargetEq⟩
                      subst target
                      by_cases hCondition : Formula.Satisfies env condition <;>
                        simp only [Formula.Satisfies] at hCondition <;>
                        simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition,
                          contract.or_holds,
                          contract.quote_holds, contract.bool_holds]
                  · by_cases hThenFalse : thenTerm = .bool false
                    · by_cases hElseTrue : elseTerm = .bool true
                      · subst thenTerm
                        subst elseTerm
                        simp [hEqual, hFool] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract, Term.eval, Formula.eval,
                            Formula.Satisfies, hCondition, contract.quote_holds,
                            contract.bool_holds]
                      · subst thenTerm
                        simp [hEqual, hFool] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract, Term.eval, Formula.eval,
                            Formula.Satisfies, hCondition, contract.and_holds,
                            contract.quote_holds, contract.bool_holds]
                    · by_cases hElseTrue : elseTerm = .bool true
                      · subst elseTerm
                        simp [hEqual, hFool] at hStep
                        rcases hStep with ⟨_, hTargetEq⟩
                        subst target
                        by_cases hCondition : Formula.Satisfies env condition <;>
                          simp only [Formula.Satisfies] at hCondition <;>
                          simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition,
                            contract.imp_holds,
                            contract.quote_holds, contract.bool_holds]
                      · by_cases hElseFalse : elseTerm = .bool false
                        · subst elseTerm
                          simp [hEqual, hFool] at hStep
                          rcases hStep with ⟨_, hTargetEq⟩
                          subst target
                          by_cases hCondition : Formula.Satisfies env condition <;>
                            simp only [Formula.Satisfies] at hCondition <;>
                            simp [Term.eval_ite contract, Term.eval, Formula.Satisfies, hCondition,
                              contract.and_holds, contract.quote_holds,
                              contract.bool_holds]
                        · simp [hEqual, hFool, hThenTrue,
                            hThenFalse, hElseTrue, hElseFalse] at hStep
            · simp [hEqual, hFool] at hStep
  | bvar =>
      simp [rewriteRootTerm?] at hStep
  | fvar =>
      simp [rewriteRootTerm?] at hStep
  | app =>
      simp [rewriteRootTerm?] at hStep
  | bool =>
      simp [rewriteRootTerm?] at hStep

/-- `andE` 根部规则保持布尔 typed 事实。 -/
theorem rewriteRootAnd_target_bool {config : Config} {bound : List CoreSort}
    {left right target : Term} {rule : StepRule}
    (hLeft : Term.inferSortWith bound left = some .bool)
    (hRight : Term.inferSortWith bound right = some .bool)
    (hStep : rewriteRootTerm? config (.andE left right) = some (rule, target)) :
    Term.inferSortWith bound target = some .bool := by
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

/-- `orE` 根部规则保持布尔 typed 事实。 -/
theorem rewriteRootOr_target_bool {config : Config} {bound : List CoreSort}
    {left right target : Term} {rule : StepRule}
    (hLeft : Term.inferSortWith bound left = some .bool)
    (hRight : Term.inferSortWith bound right = some .bool)
    (hStep : rewriteRootTerm? config (.orE left right) = some (rule, target)) :
    Term.inferSortWith bound target = some .bool := by
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

/-- `impE` 根部规则保持布尔 typed 事实。 -/
theorem rewriteRootImp_target_bool {config : Config} {bound : List CoreSort}
    {left right target : Term} {rule : StepRule}
    (hLeft : Term.inferSortWith bound left = some .bool)
    (hRight : Term.inferSortWith bound right = some .bool)
    (hStep : rewriteRootTerm? config (.impE left right) = some (rule, target)) :
    Term.inferSortWith bound target = some .bool := by
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

/-- `iffE` 根部规则保持布尔 typed 事实。 -/
theorem rewriteRootIff_target_bool {config : Config} {bound : List CoreSort}
    {left right target : Term} {rule : StepRule}
    (hLeft : Term.inferSortWith bound left = some .bool)
    (hRight : Term.inferSortWith bound right = some .bool)
    (hStep : rewriteRootTerm? config (.iffE left right) = some (rule, target)) :
    Term.inferSortWith bound target = some .bool := by
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

/-- `notE` 根部规则保持布尔 typed 事实。 -/
theorem rewriteRootNot_target_bool {config : Config} {bound : List CoreSort}
    {body target : Term} {rule : StepRule}
    (hBody : Term.inferSortWith bound body = some .bool)
    (hStep : rewriteRootTerm? config (.notE body) = some (rule, target)) :
    Term.inferSortWith bound target = some .bool := by
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

/-- `quote` 根部规则保持布尔 typed 事实。 -/
theorem rewriteRootQuote_target_bool {config : Config} {bound : List CoreSort}
    {formula : Formula} {target : Term} {rule : StepRule}
    (hFormula : Formula.checkWith bound formula = true)
    (hStep : rewriteRootTerm? config (.quote formula) = some (rule, target)) :
    Term.inferSortWith bound target = some .bool := by
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

/-- `ite` 根部规则保持语法节点声明的结果 sort。 -/
theorem rewriteRootIte_target_sort {config : Config} {bound : List CoreSort}
    {declared : CoreSort} {condition : Formula} {thenTerm elseTerm target : Term}
    {rule : StepRule}
    (hCondition : Formula.checkWith bound condition = true)
    (hThen : Term.inferSortWith bound thenTerm = some declared)
    (hElse : Term.inferSortWith bound elseTerm = some declared)
    (hStep :
      rewriteRootTerm? config (.ite declared condition thenTerm elseTerm) =
        some (rule, target)) :
    Term.inferSortWith bound target = some declared := by
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

/--
根部项重写的宽接口。beta / eta 直接使用无类型语义定理；其余规则由外层
typed 反演和目标 typed 保持恢复共同结果 sort。
-/
theorem rewriteRootTerm?_sound_of_typed {M : Model}
    (contract : FoolLambdaContract M) (config : Config)
    (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    {source target : Term} {rule : StepRule}
    {sourceSort targetSort : CoreSort}
    (hSource : Term.inferSortWith bound source = some sourceSort)
    (hTarget : Term.inferSortWith bound target = some targetSort)
    (hStep : rewriteRootTerm? config source = some (rule, target)) :
    SemanticallyEqual env source target := by
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
        | none =>
            simp [hContract] at hStep
        | some contracted =>
            simp [hContract] at hStep
            rcases hStep with ⟨_, rfl⟩
            exact eval_eta_contract? contract bound env hBound hFree
              domain codomain body contracted
              (inferSortWith_lam_parts hSource).2 hContract
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
  | bvar =>
      simp [rewriteRootTerm?] at hStep
  | fvar =>
      simp [rewriteRootTerm?] at hStep
  | app =>
      simp [rewriteRootTerm?] at hStep
  | bool =>
      simp [rewriteRootTerm?] at hStep

/-- 在新 binder 下解释整体 shift 后的项，回到原环境中的解释。 -/
theorem eval_shift_under_push {M : Model} (env : Env M) (value : M.Carrier)
    (term : Term) :
    Term.eval (env.push value) (Term.shift 1 term) = Term.eval env term := by
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

/-- 两个公式在指定模型与环境下满足性等价。 -/
def SemanticallyEquivalent {M : Model} (env : Env M)
    (left right : Formula) : Prop :=
  Formula.Satisfies env left ↔ Formula.Satisfies env right

/-- 带 FOOL/lambda 模型合同的公式可满足性。 -/
def FoolLambdaSatisfiable (formula : Formula) : Prop :=
  ∃ (M : Model.{x}) (env : Env M), Nonempty (FoolLambdaContract M) ∧
    Env.RespectsFree env ∧ Formula.Satisfies env formula

/-- 合法原子公式至少给出参数 sort 列表的成功推断。 -/
theorem inferSortListWith_of_check_atom {bound : List CoreSort}
    {predicate : PredicateSymbol} {args : List Term}
    (hCheck : Formula.checkWith bound (.atom predicate args) = true) :
    ∃ sorts, Term.inferSortListWith bound args = some sorts := by
  by_cases hArity : !predicate.arityOk || args.length != predicate.arity
  · simp [Formula.checkWith, hArity] at hCheck
  · cases hArgs : Term.inferSortListWith bound args with
    | none =>
        simp [Formula.checkWith, hArity, hArgs] at hCheck
    | some sorts =>
        exact ⟨sorts, rfl⟩

/-- 合法 equality 公式的两端都推断为节点声明的 sort。 -/
theorem inferSortWith_of_check_equal {bound : List CoreSort} {sort : CoreSort}
    {left right : Term}
    (hCheck : Formula.checkWith bound (.equal sort left right) = true) :
    Term.inferSortWith bound left = some sort ∧
      Term.inferSortWith bound right = some sort := by
  simp only [Formula.checkWith] at hCheck
  cases hLeft : Term.inferSortWith bound left <;>
    cases hRight : Term.inferSortWith bound right <;>
    simp_all [coreSort_eq_of_beq_eq_true]

/-- 合法布尔项公式的内部项推断为布尔 sort。 -/
theorem inferSortWith_of_check_boolTerm {bound : List CoreSort} {term : Term}
    (hCheck : Formula.checkWith bound (.boolTerm term) = true) :
    Term.inferSortWith bound term = some .bool := by
  simp only [Formula.checkWith] at hCheck
  cases hSort : Term.inferSortWith bound term <;> simp_all

/-- 合法否定公式把 checker 事实直接传给子公式。 -/
theorem checkWith_of_check_neg {bound : List CoreSort} {body : Formula}
    (hCheck : Formula.checkWith bound (.neg body) = true) :
    Formula.checkWith bound body = true := by
  simpa only [Formula.checkWith] using hCheck

/-- 四种二元公式 connective 共享同一 checker 反演。 -/
theorem checkWith_of_check_imp {bound : List CoreSort} {left right : Formula}
    (hCheck : Formula.checkWith bound (.imp left right) = true) :
    Formula.checkWith bound left = true ∧
      Formula.checkWith bound right = true := by
  simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

theorem checkWith_of_check_conj {bound : List CoreSort} {left right : Formula}
    (hCheck : Formula.checkWith bound (.conj left right) = true) :
    Formula.checkWith bound left = true ∧
      Formula.checkWith bound right = true := by
  simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

theorem checkWith_of_check_disj {bound : List CoreSort} {left right : Formula}
    (hCheck : Formula.checkWith bound (.disj left right) = true) :
    Formula.checkWith bound left = true ∧
      Formula.checkWith bound right = true := by
  simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

theorem checkWith_of_check_iffE {bound : List CoreSort} {left right : Formula}
    (hCheck : Formula.checkWith bound (.iffE left right) = true) :
    Formula.checkWith bound left = true ∧
      Formula.checkWith bound right = true := by
  simpa only [Formula.checkWith, Bool.and_eq_true] using hCheck

/-- 合法量词公式把 checker 事实传给扩展 binder 上下文中的 body。 -/
theorem checkWith_of_check_forallE {bound : List CoreSort} {sort : CoreSort}
    {body : Formula}
    (hCheck : Formula.checkWith bound (.forallE sort body) = true) :
    Formula.checkWith (sort :: bound) body = true := by
  simpa only [Formula.checkWith] using hCheck

theorem checkWith_of_check_existsE {bound : List CoreSort} {sort : CoreSort}
    {body : Formula}
    (hCheck : Formula.checkWith bound (.existsE sort body) = true) :
    Formula.checkWith (sort :: bound) body = true := by
  simpa only [Formula.checkWith] using hCheck

/-- 函数 sort 的 equality 可由合同外延性展开为逐点 equality。 -/
theorem satisfies_functionExtensionality_iff {M : Model}
    (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    (domain codomain : CoreSort) (left right : Term)
    (hLeft : Term.inferSortWith bound left = some (.arrow domain codomain))
    (hRight : Term.inferSortWith bound right = some (.arrow domain codomain)) :
    Formula.Satisfies env (.equal (.arrow domain codomain) left right) ↔
      Formula.Satisfies env
        (.forallE domain
          (.equal codomain
            (.apply (Term.shift 1 left) (.bvar domain 0))
            (.apply (Term.shift 1 right) (.bvar domain 0)))) := by
  have hLeftMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    left (.arrow domain codomain) hLeft
  have hRightMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    right (.arrow domain codomain) hRight
  simp only [Formula.Satisfies, Formula.eval, Term.eval, Term.eval_shift_under_push]
  exact contract.function_extensionality domain codomain _ _ hLeftMem hRightMem

/-- 布尔 sort 的 equality 由两端真值等价刻画。 -/
theorem satisfies_boolEquality_iff {M : Model}
    (contract : FoolLambdaContract M) (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    (left right : Term)
    (hLeft : Term.inferSortWith bound left = some .bool)
    (hRight : Term.inferSortWith bound right = some .bool) :
    Formula.Satisfies env (.equal .bool left right) ↔
      (M.boolHolds (Term.eval env left) ↔ M.boolHolds (Term.eval env right)) := by
  have hLeftMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    left .bool hLeft
  have hRightMem := Term.eval_mem_of_inferSortWith contract bound env hBound hFree
    right .bool hRight
  simpa only [Formula.Satisfies, Formula.eval] using
    contract.bool_extensionality _ _ hLeftMem hRightMem

/-- 公式根部重写在 typed 环境中保持满足性。 -/
theorem rewriteRootFormula?_sound {M : Model} (contract : FoolLambdaContract M)
    (config : Config) (bound : List CoreSort) (env : Env M)
    (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
    {source target : Formula} {rule : StepRule}
    (hSource : Formula.checkWith bound source = true)
    (_hTarget : Formula.checkWith bound target = true)
    (hStep : rewriteRootFormula? config source = some (rule, target)) :
    SemanticallyEquivalent env source target := by
  cases source with
  | trueE =>
      simp [rewriteRootFormula?] at hStep
  | falseE =>
      simp [rewriteRootFormula?] at hStep
  | atom =>
      simp [rewriteRootFormula?] at hStep
  | equal sort left right =>
      have hSorts := inferSortWith_of_check_equal hSource
      simp only [rewriteRootFormula?] at hStep
      by_cases hRefl :
          (config.connectiveSimp && SyntaxEq.termEq left right) = true
      · have hEqual : SyntaxEq.termEq left right = true :=
          (Bool.and_eq_true_iff.mp hRefl).2
        have hTerms : left = right := SyntaxEq.termEq_eq_true.mp hEqual
        subst right
        simp only [hRefl] at hStep
        rcases hStep with ⟨_, rfl⟩
        simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
      · have hReflFalse :
            (config.connectiveSimp && SyntaxEq.termEq left right) = false :=
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
                simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
                  Term.eval, contract.bool_holds, contract.quote_holds] at hBool ⊢
              all_goals exact hBool
            · simp [hFool] at hStep
        | object =>
            simp at hStep
        | prop =>
            simp at hStep
        | named =>
            simp at hStep
  | boolTerm term =>
      simp only [rewriteRootFormula?] at hStep
      by_cases hFool : config.fool = true
      · simp [hFool] at hStep
        cases term with
        | bool value =>
            cases value <;>
              simp at hStep <;>
              rcases hStep with ⟨_, rfl⟩ <;>
              simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
                Term.eval, contract.bool_holds]
        | notE body =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
              Term.eval, contract.not_holds]
        | andE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
              Term.eval, contract.and_holds]
        | orE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
              Term.eval, contract.or_holds]
        | impE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
              Term.eval, contract.imp_holds]
        | iffE left right =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
              Term.eval, contract.iff_holds]
        | quote formula =>
            rcases hStep with ⟨_, rfl⟩
            simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
              Term.eval, contract.quote_holds]
        | ite sort condition thenTerm elseTerm =>
            cases sort <;> simp at hStep
            next =>
              rcases hStep with ⟨_, rfl⟩
              by_cases hCondition : Formula.Satisfies env condition <;>
                simp only [Formula.Satisfies] at hCondition <;>
                simp [SemanticallyEquivalent, Formula.Satisfies, Formula.eval,
                  Term.eval_ite contract, hCondition]
        | bvar =>
            simp at hStep
        | fvar =>
            simp at hStep
        | app =>
            simp at hStep
        | apply =>
            simp at hStep
        | lam =>
            simp at hStep
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
  | imp left right =>
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
  | conj left right =>
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
  | disj left right =>
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

open Formula Term

mutual

  /-- 公式优先的一次 rewrite 保持满足性。 -/
  theorem Formula.rewriteOnceFormula?_sound {M : Model}
      (contract : FoolLambdaContract M) (config : Config)
      (bound : List CoreSort) (env : Env M)
      (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
      {source target : Formula} {rule : StepRule}
      (hSource : Formula.checkWith bound source = true)
      (hTarget : Formula.checkWith bound target = true)
      (hStep : rewriteOnceFormula? config source = some (rule, target)) :
      SemanticallyEquivalent env source target := by
    cases source with
    | trueE =>
        simp [rewriteOnceFormula?] at hStep
    | falseE =>
        simp [rewriteOnceFormula?] at hStep
    | atom predicate args =>
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceTermList? config args with
        | none =>
            simp [hRewrite, rewriteRootFormula?] at hStep
        | some value =>
            rcases value with ⟨childRule, args'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            obtain ⟨sourceSorts, hSourceArgs⟩ :=
              inferSortListWith_of_check_atom hSource
            obtain ⟨targetSorts, hTargetArgs⟩ :=
              inferSortListWith_of_check_atom hTarget
            have hArgs :=
              Term.rewriteOnceTermList?_sound contract config bound env hBound hFree
                hSourceArgs hTargetArgs hRewrite
            change
              SemanticallyEquivalent env (Formula.atom predicate args)
                (Formula.atom predicate args')
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change
              (M.predicateInterp predicate (args.map (Term.eval env)) ↔
                M.predicateInterp predicate (args'.map (Term.eval env)))
            rw [hArgs]
    | equal sort left right =>
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceSorts := inferSortWith_of_check_equal hSource
            have hTargetSorts := inferSortWith_of_check_equal hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceSorts.1 hTargetSorts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change
              (Term.eval env left = Term.eval env right ↔
                Term.eval env left' = Term.eval env right)
            change Term.eval env left = Term.eval env left' at hLeftSem
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceSorts := inferSortWith_of_check_equal hSource
                have hTargetSorts := inferSortWith_of_check_equal hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                    hSourceSorts.2 hTargetSorts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                change
                  (Term.eval env left = Term.eval env right ↔
                    Term.eval env left = Term.eval env right')
                change Term.eval env right = Term.eval env right' at hRightSem
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_sound contract config bound env
                  hBound hFree hSource hTarget hStep
    | boolTerm term =>
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceTerm? config term with
        | some value =>
            rcases value with ⟨childRule, term'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceSort := inferSortWith_of_check_boolTerm hSource
            have hTargetSort := inferSortWith_of_check_boolTerm hTarget
            have hTermSem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceSort hTargetSort hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            change
              (M.boolHolds (Term.eval env term) ↔
                M.boolHolds (Term.eval env term'))
            change Term.eval env term = Term.eval env term' at hTermSem
            rw [hTermSem]
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_sound contract config bound env
              hBound hFree hSource hTarget hStep
    | neg body =>
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceBody := checkWith_of_check_neg hSource
            have hTargetBody := checkWith_of_check_neg hTarget
            have hBodySem :=
              Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                hSourceBody hTargetBody hRewrite
            simpa only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval] using
              not_congr hBodySem
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_sound contract config bound env
              hBound hFree hSource hTarget hStep
    | imp left right =>
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := checkWith_of_check_imp hSource
            have hTargetParts := checkWith_of_check_imp hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h hLeft'
              exact h (hLeftSem.mpr hLeft')
            · intro h hLeft
              exact h (hLeftSem.mp hLeft)
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := checkWith_of_check_imp hSource
                have hTargetParts := checkWith_of_check_imp hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h hLeft
                  exact hRightSem.mp (h hLeft)
                · intro h hLeft
                  exact hRightSem.mpr (h hLeft)
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_sound contract config bound env
                  hBound hFree hSource hTarget hStep
    | conj left right =>
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := checkWith_of_check_conj hSource
            have hTargetParts := checkWith_of_check_conj hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h
              exact ⟨hLeftSem.mp h.1, h.2⟩
            · intro h
              exact ⟨hLeftSem.mpr h.1, h.2⟩
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := checkWith_of_check_conj hSource
                have hTargetParts := checkWith_of_check_conj hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h
                  exact ⟨h.1, hRightSem.mp h.2⟩
                · intro h
                  exact ⟨h.1, hRightSem.mpr h.2⟩
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_sound contract config bound env
                  hBound hFree hSource hTarget hStep
    | disj left right =>
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := checkWith_of_check_disj hSource
            have hTargetParts := checkWith_of_check_disj hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h
              cases h with
              | inl hLeft => exact Or.inl (hLeftSem.mp hLeft)
              | inr hRight => exact Or.inr hRight
            · intro h
              cases h with
              | inl hLeft => exact Or.inl (hLeftSem.mpr hLeft)
              | inr hRight => exact Or.inr hRight
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := checkWith_of_check_disj hSource
                have hTargetParts := checkWith_of_check_disj hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h
                  cases h with
                  | inl hLeft => exact Or.inl hLeft
                  | inr hRight => exact Or.inr (hRightSem.mp hRight)
                · intro h
                  cases h with
                  | inl hLeft => exact Or.inl hLeft
                  | inr hRight => exact Or.inr (hRightSem.mpr hRight)
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_sound contract config bound env
                  hBound hFree hSource hTarget hStep
    | iffE left right =>
        simp only [rewriteOnceFormula?] at hStep
        cases hLeftRewrite : rewriteOnceFormula? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := checkWith_of_check_iffE hSource
            have hTargetParts := checkWith_of_check_iffE hTarget
            have hLeftSem :=
              Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                hSourceParts.1 hTargetParts.1 hLeftRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h
              exact ⟨fun hLeft' => h.mp (hLeftSem.mpr hLeft'),
                fun hRight => hLeftSem.mp (h.mpr hRight)⟩
            · intro h
              exact ⟨fun hLeft => h.mp (hLeftSem.mp hLeft),
                fun hRight => hLeftSem.mpr (h.mpr hRight)⟩
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceFormula? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := checkWith_of_check_iffE hSource
                have hTargetParts := checkWith_of_check_iffE hTarget
                have hRightSem :=
                  Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                    hSourceParts.2 hTargetParts.2 hRightRewrite
                simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
                constructor
                · intro h
                  exact ⟨fun hLeft => hRightSem.mp (h.mp hLeft),
                    fun hRight' => h.mpr (hRightSem.mpr hRight')⟩
                · intro h
                  exact ⟨fun hLeft => hRightSem.mpr (h.mp hLeft),
                    fun hRight => h.mpr (hRightSem.mp hRight)⟩
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootFormula?_sound contract config bound env
                  hBound hFree hSource hTarget hStep
    | forallE sort body =>
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceBody := checkWith_of_check_forallE hSource
            have hTargetBody := checkWith_of_check_forallE hTarget
            have hBodySem (value : M.Carrier) (hValue : M.sortInterp sort value) :=
              Formula.rewriteOnceFormula?_sound contract config (sort :: bound)
                (env.push value) (Env.respectsBound_push hBound hValue)
                (Env.respectsFree_push hFree value) hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · intro h value hValue
              exact (hBodySem value hValue).mp (h value hValue)
            · intro h value hValue
              exact (hBodySem value hValue).mpr (h value hValue)
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_sound contract config bound env
              hBound hFree hSource hTarget hStep
    | existsE sort body =>
        simp only [rewriteOnceFormula?] at hStep
        cases hRewrite : rewriteOnceFormula? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceBody := checkWith_of_check_existsE hSource
            have hTargetBody := checkWith_of_check_existsE hTarget
            have hBodySem (value : M.Carrier) (hValue : M.sortInterp sort value) :=
              Formula.rewriteOnceFormula?_sound contract config (sort :: bound)
                (env.push value) (Env.respectsBound_push hBound hValue)
                (Env.respectsFree_push hFree value) hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEquivalent, Formula.Satisfies, Formula.eval]
            constructor
            · rintro ⟨value, hValue, hBody⟩
              exact ⟨value, hValue, (hBodySem value hValue).mp hBody⟩
            · rintro ⟨value, hValue, hBody⟩
              exact ⟨value, hValue, (hBodySem value hValue).mpr hBody⟩
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootFormula?_sound contract config bound env
              hBound hFree hSource hTarget hStep

  /-- 项优先的一次 rewrite 保持解释相等。 -/
  theorem Term.rewriteOnceTerm?_sound {M : Model}
      (contract : FoolLambdaContract M) (config : Config)
      (bound : List CoreSort) (env : Env M)
      (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
      {source target : Term} {rule : StepRule}
      {sourceSort targetSort : CoreSort}
      (hSource : Term.inferSortWith bound source = some sourceSort)
      (hTarget : Term.inferSortWith bound target = some targetSort)
      (hStep : rewriteOnceTerm? config source = some (rule, target)) :
      SemanticallyEqual env source target := by
    cases source with
    | bvar =>
        simp [rewriteOnceTerm?] at hStep
    | fvar =>
        simp [rewriteOnceTerm?] at hStep
    | bool =>
        simp [rewriteOnceTerm?] at hStep
    | app symbol args =>
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceTermList? config args with
        | none =>
            simp [hRewrite, rewriteRootTerm?] at hStep
        | some value =>
            rcases value with ⟨childRule, args'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            obtain ⟨_, sourceSorts, hSourceArgs⟩ :=
              inferSortWith_app_parts hSource
            obtain ⟨_, targetSorts, hTargetArgs⟩ :=
              inferSortWith_app_parts hTarget
            have hArgsSem :=
              Term.rewriteOnceTermList?_sound contract config bound env hBound hFree
                hSourceArgs hTargetArgs hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.functionInterp symbol (args.map (Term.eval env)) =
                M.functionInterp symbol (args'.map (Term.eval env))
            rw [hArgsSem]
    | apply fn arg =>
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
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
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
                  Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                    hSourceArg hTargetArg hArgRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.applyInterp (Term.eval env fn) (Term.eval env arg) =
                    M.applyInterp (Term.eval env fn) (Term.eval env arg')
                rw [hArgSem]
            | none =>
                simp [hArgRewrite] at hStep
                exact rewriteRootTerm?_sound_of_typed contract config bound env
                  hBound hFree hSource hTarget hStep
    | notE body =>
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceTerm? config body with
        | some value =>
            rcases value with ⟨childRule, body'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceBody := (inferSortWith_notE_parts hSource).2
            have hTargetBody := (inferSortWith_notE_parts hTarget).2
            have hBodySem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceBody hTargetBody hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change M.notValue (Term.eval env body) = M.notValue (Term.eval env body')
            rw [hBodySem]
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootTerm?_sound_of_typed contract config bound env
              hBound hFree hSource hTarget hStep
    | andE left right =>
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := inferSortWith_andE_parts hSource
            have hTargetParts := inferSortWith_andE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.andValue (Term.eval env left) (Term.eval env right) =
                M.andValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := inferSortWith_andE_parts hSource
                have hTargetParts := inferSortWith_andE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.andValue (Term.eval env left) (Term.eval env right) =
                    M.andValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_sound_of_typed contract config bound env
                  hBound hFree hSource hTarget hStep
    | orE left right =>
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := inferSortWith_orE_parts hSource
            have hTargetParts := inferSortWith_orE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.orValue (Term.eval env left) (Term.eval env right) =
                M.orValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := inferSortWith_orE_parts hSource
                have hTargetParts := inferSortWith_orE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.orValue (Term.eval env left) (Term.eval env right) =
                    M.orValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_sound_of_typed contract config bound env
                  hBound hFree hSource hTarget hStep
    | impE left right =>
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := inferSortWith_impE_parts hSource
            have hTargetParts := inferSortWith_impE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.impValue (Term.eval env left) (Term.eval env right) =
                M.impValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := inferSortWith_impE_parts hSource
                have hTargetParts := inferSortWith_impE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.impValue (Term.eval env left) (Term.eval env right) =
                    M.impValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_sound_of_typed contract config bound env
                  hBound hFree hSource hTarget hStep
    | iffE left right =>
        simp only [rewriteOnceTerm?] at hStep
        cases hLeftRewrite : rewriteOnceTerm? config left with
        | some value =>
            rcases value with ⟨childRule, left'⟩
            simp [hLeftRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := inferSortWith_iffE_parts hSource
            have hTargetParts := inferSortWith_iffE_parts hTarget
            have hLeftSem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceParts.2.1 hTargetParts.2.1 hLeftRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.iffValue (Term.eval env left) (Term.eval env right) =
                M.iffValue (Term.eval env left') (Term.eval env right)
            rw [hLeftSem]
        | none =>
            simp [hLeftRewrite] at hStep
            cases hRightRewrite : rewriteOnceTerm? config right with
            | some value =>
                rcases value with ⟨childRule, right'⟩
                simp [hRightRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := inferSortWith_iffE_parts hSource
                have hTargetParts := inferSortWith_iffE_parts hTarget
                have hRightSem :=
                  Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                    hSourceParts.2.2 hTargetParts.2.2 hRightRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.iffValue (Term.eval env left) (Term.eval env right) =
                    M.iffValue (Term.eval env left) (Term.eval env right')
                rw [hRightSem]
            | none =>
                simp [hRightRewrite] at hStep
                exact rewriteRootTerm?_sound_of_typed contract config bound env
                  hBound hFree hSource hTarget hStep
    | quote formula =>
        simp only [rewriteOnceTerm?] at hStep
        cases hRewrite : rewriteOnceFormula? config formula with
        | some value =>
            rcases value with ⟨childRule, formula'⟩
            simp [hRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceFormula := (inferSortWith_quote_parts hSource).2
            have hTargetFormula := (inferSortWith_quote_parts hTarget).2
            have hFormulaSem :=
              Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                hSourceFormula hTargetFormula hRewrite
            simp only [SemanticallyEqual, Term.eval]
            change
              M.quoteValue (Formula.eval env formula).holds =
                M.quoteValue (Formula.eval env formula').holds
            exact (contract.quote_eq_iff _ _).2 hFormulaSem
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootTerm?_sound_of_typed contract config bound env
              hBound hFree hSource hTarget hStep
    | lam domain codomain body =>
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
              M.lambdaValue domain codomain
                  (fun value => Term.eval (env.push value) body) =
                M.lambdaValue domain codomain
                  (fun value => Term.eval (env.push value) body')
            apply contract.lambda_congr
            intro value hValue
            exact
              Term.rewriteOnceTerm?_sound contract config (domain :: bound)
                (env.push value) (Env.respectsBound_push hBound hValue)
                (Env.respectsFree_push hFree value) hSourceBody hTargetBody hRewrite
        | none =>
            simp [hRewrite] at hStep
            exact rewriteRootTerm?_sound_of_typed contract config bound env
              hBound hFree hSource hTarget hStep
    | ite declared condition thenTerm elseTerm =>
        simp only [rewriteOnceTerm?] at hStep
        cases hConditionRewrite : rewriteOnceFormula? config condition with
        | some value =>
            rcases value with ⟨childRule, condition'⟩
            simp [hConditionRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            have hSourceParts := inferSortWith_ite_parts hSource
            have hTargetParts := inferSortWith_ite_parts hTarget
            have hConditionSem :=
              Formula.rewriteOnceFormula?_sound contract config bound env hBound hFree
                hSourceParts.2.1 hTargetParts.2.1 hConditionRewrite
            have hConditionEq :
                (Formula.eval env condition).holds =
                  (Formula.eval env condition').holds :=
              propext hConditionSem
            simp only [SemanticallyEqual, Term.eval]
            change
              M.iteValue (Formula.eval env condition).holds
                  (Term.eval env thenTerm) (Term.eval env elseTerm) =
                M.iteValue (Formula.eval env condition').holds
                  (Term.eval env thenTerm) (Term.eval env elseTerm)
            rw [hConditionEq]
        | none =>
            simp [hConditionRewrite] at hStep
            cases hThenRewrite : rewriteOnceTerm? config thenTerm with
            | some value =>
                rcases value with ⟨childRule, thenTerm'⟩
                simp [hThenRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                have hSourceParts := inferSortWith_ite_parts hSource
                have hTargetParts := inferSortWith_ite_parts hTarget
                have hThenSem :=
                  Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                    hSourceParts.2.2.1 hTargetParts.2.2.1 hThenRewrite
                simp only [SemanticallyEqual, Term.eval]
                change
                  M.iteValue (Formula.eval env condition).holds
                      (Term.eval env thenTerm) (Term.eval env elseTerm) =
                    M.iteValue (Formula.eval env condition).holds
                      (Term.eval env thenTerm') (Term.eval env elseTerm)
                rw [hThenSem]
            | none =>
                simp [hThenRewrite] at hStep
                cases hElseRewrite : rewriteOnceTerm? config elseTerm with
                | some value =>
                    rcases value with ⟨childRule, elseTerm'⟩
                    simp [hElseRewrite] at hStep
                    rcases hStep with ⟨rfl, rfl⟩
                    have hSourceParts := inferSortWith_ite_parts hSource
                    have hTargetParts := inferSortWith_ite_parts hTarget
                    have hElseSem :=
                      Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                        hSourceParts.2.2.2 hTargetParts.2.2.2 hElseRewrite
                    simp only [SemanticallyEqual, Term.eval]
                    change
                      M.iteValue (Formula.eval env condition).holds
                          (Term.eval env thenTerm) (Term.eval env elseTerm) =
                        M.iteValue (Formula.eval env condition).holds
                          (Term.eval env thenTerm) (Term.eval env elseTerm')
                    rw [hElseSem]
                | none =>
                    simp [hElseRewrite] at hStep
                    exact rewriteRootTerm?_sound_of_typed contract config bound env
                      hBound hFree hSource hTarget hStep

  /-- 项列表的一次 rewrite 保持逐项解释相等。 -/
  theorem Term.rewriteOnceTermList?_sound {M : Model}
      (contract : FoolLambdaContract M) (config : Config)
      (bound : List CoreSort) (env : Env M)
      (hBound : Env.RespectsBound bound env) (hFree : Env.RespectsFree env)
      {source target : List Term} {rule : StepRule}
      {sourceSorts targetSorts : List CoreSort}
      (hSource : Term.inferSortListWith bound source = some sourceSorts)
      (hTarget : Term.inferSortListWith bound target = some targetSorts)
      (hStep : rewriteOnceTermList? config source = some (rule, target)) :
      ListSemanticallyEqual env source target := by
    cases source with
    | nil =>
        simp [rewriteOnceTermList?] at hStep
    | cons term rest =>
        obtain ⟨sourceSort, sourceRestSorts, rfl, hSourceTerm, hSourceRest⟩ :=
          inferSortListWith_cons_parts hSource
        simp only [rewriteOnceTermList?] at hStep
        cases hTermRewrite : rewriteOnceTerm? config term with
        | some value =>
            rcases value with ⟨childRule, term'⟩
            simp [hTermRewrite] at hStep
            rcases hStep with ⟨rfl, rfl⟩
            obtain ⟨targetSort, targetRestSorts, rfl, hTargetTerm, hTargetRest⟩ :=
              inferSortListWith_cons_parts hTarget
            have hTermSem :=
              Term.rewriteOnceTerm?_sound contract config bound env hBound hFree
                hSourceTerm hTargetTerm hTermRewrite
            change
              Term.eval env term :: rest.map (Term.eval env) =
                Term.eval env term' :: rest.map (Term.eval env)
            rw [hTermSem]
        | none =>
            simp [hTermRewrite] at hStep
            cases hRestRewrite : rewriteOnceTermList? config rest with
            | none =>
                simp [hRestRewrite] at hStep
            | some value =>
                rcases value with ⟨childRule, rest'⟩
                simp [hRestRewrite] at hStep
                rcases hStep with ⟨rfl, rfl⟩
                obtain ⟨targetSort, targetRestSorts, rfl, hTargetTerm, hTargetRest⟩ :=
                  inferSortListWith_cons_parts hTarget
                have hRestSem :=
                  Term.rewriteOnceTermList?_sound contract config bound env hBound hFree
                    hSourceRest hTargetRest hRestRewrite
                change
                  Term.eval env term :: rest.map (Term.eval env) =
                    Term.eval env term :: rest'.map (Term.eval env)
                rw [hRestSem]

end

namespace TraceExpr

/-- trace 表达式只在载体种类一致时比较对应语义。 -/
def SemanticallyEquivalent {M : Model} (env : Env M) :
    TraceExpr → TraceExpr → Prop
  | .term left, .term right => Term.SemanticallyEqual env left right
  | .formula left, .formula right => Formula.SemanticallyEquivalent env left right
  | _, _ => False

/-- trace 表达式的可计算相等恰好刻画语法相等。 -/
theorem eq_eq_true {left right : TraceExpr} :
    TraceExpr.eq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [TraceExpr.eq, SyntaxEq.termEq_eq_true, SyntaxEq.formulaEq_eq_true]

/-- trace 语义等价是自反的。 -/
theorem semanticallyEquivalent_refl {M : Model} (env : Env M)
    (expr : TraceExpr) :
    SemanticallyEquivalent env expr expr := by
  cases expr <;>
    simp [SemanticallyEquivalent, Term.SemanticallyEqual,
      Formula.SemanticallyEquivalent]

/-- trace 语义等价可以沿中间表达式传递。 -/
theorem semanticallyEquivalent_trans {M : Model} {env : Env M}
    {left middle right : TraceExpr}
    (hLeft : SemanticallyEquivalent env left middle)
    (hRight : SemanticallyEquivalent env middle right) :
    SemanticallyEquivalent env left right := by
  cases left <;> cases middle <;> cases right <;>
    simp [SemanticallyEquivalent, Term.SemanticallyEqual,
      Formula.SemanticallyEquivalent] at hLeft hRight ⊢
  · exact hLeft.trans hRight
  · exact hLeft.trans hRight

end TraceExpr

namespace Env

/-- 空 bound 上下文不对环境附加约束。 -/
theorem respectsBound_nil {M : Model} (env : Env M) :
    RespectsBound [] env := by
  intro index sort hLookup
  cases index <;> simp [TypeCheck.lookupBound?] at hLookup

end Env

namespace Step

/--
通过单步 checker 的 trace 节点保持语义。

checker 两端独立复核类型，避免旧无类型符号的空 `inputSorts` 把不同参数 sort
列表误当作同一类型证据。
-/
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M)
    (config : Config) (env : Env M) (hFree : Env.RespectsFree env)
    (step : Step) (hCheck : step.check config = true) :
    TraceExpr.SemanticallyEquivalent env step.before step.after := by
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
          | none =>
              simp [TraceExpr.check?, Term.inferSort?, hSourceSort] at hBefore
          | some sourceSort =>
              cases hTargetSort : Term.inferSortWith [] target with
              | none =>
                  simp [TraceExpr.check?, Term.inferSort?, hTargetSort] at hAfter
              | some targetSort =>
                  cases hStep : rewriteOnceTerm? config source with
                  | none =>
                      simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
                  | some value =>
                      rcases value with ⟨rule, rewritten⟩
                      simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq,
                        SyntaxEq.termEq_eq_true] at hRewrite
                      rcases hRewrite with ⟨_, hTarget⟩
                      subst target
                      simpa [TraceExpr.SemanticallyEquivalent] using
                        Term.rewriteOnceTerm?_sound contract config [] env
                          hBound hFree hSourceSort hTargetSort hStep
      | formula target =>
          cases hStep : rewriteOnceTerm? config source <;>
            simp [TraceExpr.rewriteOnce?,
              hStep, TraceExpr.eq] at hRewrite
  | formula source =>
      cases after with
      | term target =>
          cases hStep : rewriteOnceFormula? config source <;>
            simp [TraceExpr.rewriteOnce?,
              hStep, TraceExpr.eq] at hRewrite
      | formula target =>
          cases hStep : rewriteOnceFormula? config source with
          | none =>
              simp [TraceExpr.rewriteOnce?, hStep] at hRewrite
          | some value =>
              rcases value with ⟨rule, rewritten⟩
              simp [TraceExpr.rewriteOnce?, hStep, TraceExpr.eq,
                SyntaxEq.formulaEq_eq_true] at hRewrite
              rcases hRewrite with ⟨_, hTarget⟩
              subst target
              simpa [TraceExpr.check?, Formula.check?] using
                Formula.rewriteOnceFormula?_sound contract config [] env
                  hBound hFree
                    (by simpa [TraceExpr.check?, Formula.check?] using hBefore)
                    (by simpa [TraceExpr.check?, Formula.check?] using hAfter)
                    hStep

end Step

namespace Trace

/-- 成功 replay 的整条 step 列表保持起点与终点语义等价。 -/
theorem replay?_sound {M : Model} (contract : FoolLambdaContract M)
    (config : Config) (env : Env M) (hFree : Env.RespectsFree env)
    (steps : List Step) (source target : TraceExpr)
    (hReplay :
      _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?
        config source steps = some target) :
    TraceExpr.SemanticallyEquivalent env source target := by
  induction steps generalizing source with
  | nil =>
      simp [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      subst target
      exact TraceExpr.semanticallyEquivalent_refl env source
  | cons step rest ih =>
      simp only
        [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?] at hReplay
      by_cases hLink :
          (TraceExpr.eq source step.before && step.check config) = true
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

/-- 通过总 trace checker 的 source 与 target 语义等价。 -/
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M)
    (config : Config) (env : Env M) (hFree : Env.RespectsFree env)
    (trace : Trace) (hCheck : trace.check config = true) :
    TraceExpr.SemanticallyEquivalent env trace.source trace.target := by
  unfold _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_, hReplayCheck⟩
  cases hReplay :
      _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?
        config trace.source trace.steps.toList with
  | none =>
      simp [hReplay] at hReplayCheck
  | some replayTarget =>
      have hEndpoints := Bool.and_eq_true_iff.mp (by
        simpa [hReplay] using hReplayCheck)
      have hTarget : replayTarget = trace.target :=
        TraceExpr.eq_eq_true.mp hEndpoints.1
      subst replayTarget
      exact replay?_sound contract config env hFree trace.steps.toList
        trace.source trace.target hReplay

/-- 通过总 trace checker 的 source 与当前 normalizer 复算结果语义等价。 -/
theorem normalize_sound_of_check {M : Model} (contract : FoolLambdaContract M)
    (config : Config) (env : Env M) (hFree : Env.RespectsFree env)
    (trace : Trace) (hCheck : trace.check config = true) :
    TraceExpr.SemanticallyEquivalent env trace.source
      (TraceExpr.normalize config trace.source) := by
  unfold _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_, hReplayCheck⟩
  cases hReplay :
      _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.replay?
        config trace.source trace.steps.toList with
  | none =>
      simp [hReplay] at hReplayCheck
  | some replayTarget =>
      have hEndpoints := Bool.and_eq_true_iff.mp (by
        simpa [hReplay] using hReplayCheck)
      have hNormal :
          replayTarget = TraceExpr.normalize config trace.source :=
        TraceExpr.eq_eq_true.mp hEndpoints.2
      subst replayTarget
      exact replay?_sound contract config env hFree trace.steps.toList
        trace.source (TraceExpr.normalize config trace.source) hReplay

namespace SoundnessPayload

/-- checked 公共 trace payload 的对象语义回放。 -/
theorem sound {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (hFree : Env.RespectsFree env)
    (checked :
      Certificate.Checked
        _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.SoundnessPayload
        _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Trace.SoundnessPayload.check) :
    TraceExpr.SemanticallyEquivalent env checked.payload.trace.source
      checked.payload.trace.target := by
  exact Trace.sound_of_check contract checked.payload.config env hFree
    checked.payload.trace checked.checked

end SoundnessPayload

end Trace

namespace TermPayload

/-- 通过项 normalization payload checker 后，源项与 normal form 解释相等。 -/
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (hFree : Env.RespectsFree env)
    (payload : TermPayload) (hCheck : payload.check = true) :
    Term.SemanticallyEqual env payload.source payload.normal := by
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.TermPayload.check,
      Bool.and_eq_true_iff] at hCheck
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

/-- 通过公式 normalization payload checker 后，源公式与 normal form 满足性等价。 -/
theorem sound_of_check {M : Model} (contract : FoolLambdaContract M)
    (env : Env M) (hFree : Env.RespectsFree env)
    (payload : FormulaPayload) (hCheck : payload.check = true) :
    Formula.SemanticallyEquivalent env payload.source payload.normal := by
  simp only
    [_root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.FormulaPayload.check,
      Bool.and_eq_true_iff] at hCheck
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
theorem bool_true_holds {M : Model} (contract : FoolLambdaContract M) :
    M.boolHolds (M.boolValue true) := by
  exact (contract.bool_holds true).mpr rfl

@[simp]
theorem bool_false_not_holds {M : Model} (contract : FoolLambdaContract M) :
    ¬ M.boolHolds (M.boolValue false) := by
  intro hFalse
  have : false = true := (contract.bool_holds false).mp hFalse
  contradiction

/-- quote 值的相等由被 quote 命题的等价刻画。 -/
theorem quoteValue_eq_iff {M : Model} (contract : FoolLambdaContract M)
    (left right : Prop) :
    M.quoteValue left = M.quoteValue right ↔ (left ↔ right) :=
  contract.quote_eq_iff left right

end FoolLambdaContract

end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
