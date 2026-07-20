import YesMetaZFC.Logic.HigherOrder.Syntax

/-!
# 简单类型高阶语义

语义采用单 carrier 与 sort 谓词，保持与一阶 DAG 和 FOOL 前端一致。函数值由
`applyInterp` 消费，lambda 由 `lambdaInterp` 构造；βη 与函数外延性作为独立合同，
便于后续证书规则逐项声明所需可信假设。
-/

namespace YesMetaZFC
namespace Logic
namespace HigherOrder

universe u v w x

/-- 参数值逐项落在签名声明的简单类型中。 -/
def ArgsSatisfy {S : Type u} {α : Type x}
    (sortInterp : S → α → Prop) : List α → List S → Prop
  | [], [] => True
  | value :: values, sort :: sorts =>
      sortInterp sort value ∧ ArgsSatisfy sortInterp values sorts
  | _, _ => False

/-- 支持原生 `apply/lam` 的单 carrier 高阶结构。 -/
structure Structure (σ : Signature.{u, v, w}) where
  Domain : Type x
  nonempty : Nonempty Domain
  sortInterp : SimpleType σ.BaseSort → Domain → Prop
  sortNonempty : ∀ sort, ∃ value, sortInterp sort value
  funcInterp : σ.FuncSymbol → List Domain → Domain
  funcSort :
    ∀ symbol arguments,
      ArgsSatisfy sortInterp arguments (σ.funcDomain symbol) →
        sortInterp (σ.funcCodomain symbol) (funcInterp symbol arguments)
  relInterp : σ.RelSymbol → List Domain → Prop
  applyInterp : Domain → Domain → Domain
  applySort :
    ∀ domain codomain functionValue argumentValue,
      sortInterp (.arrow domain codomain) functionValue →
        sortInterp domain argumentValue →
          sortInterp codomain (applyInterp functionValue argumentValue)
  lambdaInterp :
    SimpleType σ.BaseSort → SimpleType σ.BaseSort → (Domain → Domain) → Domain
  lambdaSort :
    ∀ domain codomain body,
      (∀ value, sortInterp domain value → sortInterp codomain (body value)) →
        sortInterp (.arrow domain codomain) (lambdaInterp domain codomain body)

/-- βη 与函数外延性规则需要的模型合同。 -/
structure ExtensionalContract {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ) where
  lambdaCongr :
    ∀ domain codomain left right,
      (∀ value, M.sortInterp domain value → left value = right value) →
        M.lambdaInterp domain codomain left = M.lambdaInterp domain codomain right
  beta :
    ∀ domain codomain body argument,
      (∀ value, M.sortInterp domain value → M.sortInterp codomain (body value)) →
      M.sortInterp domain argument →
      M.applyInterp (M.lambdaInterp domain codomain body) argument = body argument
  eta :
    ∀ domain codomain functionValue,
      M.sortInterp (.arrow domain codomain) functionValue →
      M.lambdaInterp domain codomain
          (fun argument => M.applyInterp functionValue argument) =
        functionValue
  functionExtensionality :
    ∀ domain codomain left right,
      M.sortInterp (.arrow domain codomain) left →
        M.sortInterp (.arrow domain codomain) right →
          (left = right ↔
            ∀ argument, M.sortInterp domain argument →
              M.applyInterp left argument = M.applyInterp right argument)

/--
函数外延负规则使用的显式差异见证合同。

证书必须给出签名中标记为外延见证的二元符号；合同只约束这些符号，不会把同类型的
普通参数函数误认成 `diff`。
-/
structure ExtensionalWitnessContract {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) where
  distinguishes :
    ∀ symbol domain codomain left right,
      σ.isFunctionExtensionalityWitness symbol = true →
        σ.funcDomain symbol =
          [.arrow domain codomain, .arrow domain codomain] →
          σ.funcCodomain symbol = domain →
            M.sortInterp (.arrow domain codomain) left →
              M.sortInterp (.arrow domain codomain) right →
                left ≠ right →
                  M.applyInterp left (M.funcInterp symbol [left, right]) ≠
                    M.applyInterp right (M.funcInterp symbol [left, right])

/-- 全局 de Bruijn 栈与 typed 自由变量赋值。 -/
structure Env {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ) where
  boundVal : Nat → M.Domain
  freeVal : SimpleType σ.BaseSort → FreeVarId → M.Domain

namespace Env

/-- 在统一的 bound 栈顶部压入一个值。 -/
def push {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) (value : M.Domain) : Env M where
  boundVal
    | 0 => value
    | index + 1 => env.boundVal index
  freeVal := env.freeVal

/-- 删除 bound 栈前面的若干值。 -/
def drop {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (amount : Nat) (env : Env M) : Env M where
  boundVal := fun index => env.boundVal (index + amount)
  freeVal := env.freeVal

/-- 解释 `shiftAbove amount cutoff` 时跳过环境中的同一段。 -/
def skip {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (amount cutoff : Nat) (env : Env M) : Env M where
  boundVal := fun index =>
    if index < cutoff then env.boundVal index else env.boundVal (index + amount)
  freeVal := env.freeVal

/-- 在 bound 栈的指定深度插入一个值。 -/
def insertAt {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (depth : Nat) (value : M.Domain) (env : Env M) : Env M where
  boundVal := fun index =>
    if index < depth then
      env.boundVal index
    else if index = depth then
      value
    else
      env.boundVal (index - 1)
  freeVal := env.freeVal

@[simp]
theorem push_bound_zero {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) (value : M.Domain) :
    (env.push value).boundVal 0 = value :=
  rfl

@[simp]
theorem push_bound_succ {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) (value : M.Domain) (index : Nat) :
    (env.push value).boundVal (index + 1) = env.boundVal index :=
  rfl

@[simp]
theorem push_free {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) (value : M.Domain) (sort : SimpleType σ.BaseSort) (id : FreeVarId) :
    (env.push value).freeVal sort id = env.freeVal sort id :=
  rfl

@[simp]
theorem drop_bound {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (amount : Nat) (env : Env M) (index : Nat) :
    (env.drop amount).boundVal index = env.boundVal (index + amount) :=
  rfl

@[simp]
theorem drop_free {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (amount : Nat) (env : Env M) (sort : SimpleType σ.BaseSort) (id : FreeVarId) :
    (env.drop amount).freeVal sort id = env.freeVal sort id :=
  rfl

theorem skip_zero_bound {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (amount : Nat) (env : Env M) (index : Nat) :
    (env.skip amount 0).boundVal index = (env.drop amount).boundVal index := by
  simp [skip, drop]

theorem skip_push_bound {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (amount cutoff : Nat) (env : Env M) (value : M.Domain) (index : Nat) :
    ((env.push value).skip amount (cutoff + 1)).boundVal index =
      ((env.skip amount cutoff).push value).boundVal index := by
  cases index with
  | zero =>
      rfl
  | succ previous =>
      simp only [push_bound_succ]
      simp [skip, Nat.succ_lt_succ_iff, Nat.succ_add]

theorem drop_push_bound {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (amount : Nat) (env : Env M) (value : M.Domain) (index : Nat) :
    ((env.push value).drop (amount + 1)).boundVal index =
      (env.drop amount).boundVal index := by
  have hIndex : index + (amount + 1) = (index + amount) + 1 := by omega
  simp only [drop_bound, hIndex, push_bound_succ]

theorem insertAt_push_bound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (depth : Nat) (env : Env M)
    (inserted value : M.Domain) (index : Nat) :
    ((env.push value).insertAt (depth + 1) inserted).boundVal index =
      ((env.insertAt depth inserted).push value).boundVal index := by
  cases index with
  | zero =>
      rfl
  | succ previous =>
      simp only [push_bound_succ]
      by_cases hLt : previous < depth
      · simp [insertAt, Nat.succ_lt_succ_iff, hLt]
      · by_cases hEq : previous = depth
        · simp [insertAt, hEq]
        · have hPositive : 0 < previous := by omega
          cases previous with
          | zero =>
              omega
          | succ index =>
              simp [insertAt, Nat.succ_lt_succ_iff, hLt, hEq]

/-- 环境逐项尊重当前绑定上下文和自由变量标注。 -/
def WellSorted {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (context : Context σ) (env : Env M) : Prop :=
  (∀ index sort, Context.lookup? context index = some sort →
    M.sortInterp sort (env.boundVal index)) ∧
  (∀ sort id, M.sortInterp sort (env.freeVal sort id))

/-- 压入一个对应 sort 的值后，环境仍尊重扩展后的上下文。 -/
theorem wellSorted_push {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {context : Context σ} {env : Env M} {sort : SimpleType σ.BaseSort}
    (hEnv : WellSorted context env) {value : M.Domain}
    (hValue : M.sortInterp sort value) :
    WellSorted (sort :: context) (env.push value) := by
  constructor
  · intro index target hLookup
    cases index with
    | zero =>
        simp [Context.lookup?] at hLookup
        subst target
        exact hValue
    | succ previous =>
        exact hEnv.1 previous target hLookup
  · exact hEnv.2

/-- 从每个 simple type 的非空性选择一个规范 typed 环境。 -/
noncomputable def canonical {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) : Env M where
  boundVal := fun _ => Classical.choice M.nonempty
  freeVal := fun sort _ => Classical.choose (M.sortNonempty sort)

/-- 规范环境在空 bound 上下文下类型正确。 -/
theorem canonical_wellSorted {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) :
    (canonical M).WellSorted [] := by
  constructor
  · intro index sort hLookup
    simp [Context.lookup?] at hLookup
  · intro sort id
    exact Classical.choose_spec (M.sortNonempty sort)

end Env

namespace Term

/-- 原生高阶项解释。 -/
def eval {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) : Term σ → M.Domain
  | .var (.bvar _ index) => env.boundVal index
  | .var (.fvar sort id) => env.freeVal sort id
  | .app symbol arguments => M.funcInterp symbol (arguments.map (eval env))
  | .apply function argument => M.applyInterp (eval env function) (eval env argument)
  | .lam domain codomain body =>
      M.lambdaInterp domain codomain (fun value => eval (env.push value) body)

end Term

namespace Formula

/-- 高阶公式满足关系。高阶量词遍历相应箭头 sort 的语义对象。 -/
def Satisfies {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) : Formula σ → Prop
  | .falsum => False
  | .truth => True
  | .rel symbol arguments => M.relInterp symbol (arguments.map (Term.eval env))
  | .equal _ left right => Term.eval env left = Term.eval env right
  | .neg body => ¬ Satisfies env body
  | .conj left right => Satisfies env left ∧ Satisfies env right
  | .disj left right => Satisfies env left ∨ Satisfies env right
  | .imp left right => Satisfies env left → Satisfies env right
  | .iff left right => Satisfies env left ↔ Satisfies env right
  | .forallE sort body =>
      ∀ value, M.sortInterp sort value → Satisfies (env.push value) body
  | .existsE sort body =>
      ∃ value, M.sortInterp sort value ∧ Satisfies (env.push value) body

end Formula

mutual
  /-- 项解释只依赖环境的逐点取值。 -/
  theorem Term.eval_eq_of_env_eq {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} (env₁ env₂ : Env M)
      (hBound : ∀ index, env₁.boundVal index = env₂.boundVal index)
      (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id)
      (term : Term σ) : Term.eval env₁ term = Term.eval env₂ term := by
    cases term with
    | var value =>
        cases value with
        | bvar _ index =>
            simpa only [Term.eval] using hBound index
        | fvar sort id =>
            simpa only [Term.eval] using hFree sort id
    | app symbol arguments =>
        simp only [Term.eval]
        congr 1
        exact Term.evalList_eq_of_env_eq env₁ env₂ hBound hFree arguments
    | apply function argument =>
        simp only [Term.eval]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree function,
          Term.eval_eq_of_env_eq env₁ env₂ hBound hFree argument]
    | lam domain codomain body =>
        simp only [Term.eval]
        congr 1
        funext value
        apply Term.eval_eq_of_env_eq
        · intro index
          cases index <;> simp [Env.push, hBound]
        · intro sort id
          simp [Env.push, hFree]

  /-- 项列表解释只依赖环境的逐点取值。 -/
  theorem Term.evalList_eq_of_env_eq {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} (env₁ env₂ : Env M)
      (hBound : ∀ index, env₁.boundVal index = env₂.boundVal index)
      (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id)
      (terms : List (Term σ)) :
      terms.map (Term.eval env₁) = terms.map (Term.eval env₂) := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp only [List.map_cons]
        rw [Term.eval_eq_of_env_eq env₁ env₂ hBound hFree head,
          Term.evalList_eq_of_env_eq env₁ env₂ hBound hFree tail]
end

mutual
  /--
  类型正确项的解释只依赖当前上下文实际可见的 bound 值和全部 free 值。

  这个版本允许空上下文闭项忽略环境中不可见的 bound 尾部，是 substitution 穿过
  `lam` 时排除变量捕获的基础。
  -/
  theorem Term.eval_eq_of_wellSorted_env {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} {context : Context σ}
      {env₁ env₂ : Env M} {term : Term σ} {sort : SimpleType σ.BaseSort}
      (hTerm : TermWellSorted context term sort)
      (hBound :
        ∀ index target,
          Context.lookup? context index = some target →
            env₁.boundVal index = env₂.boundVal index)
      (hFree : ∀ target id, env₁.freeVal target id = env₂.freeVal target id) :
      Term.eval env₁ term = Term.eval env₂ term := by
    cases hTerm with
    | bvar hLookup =>
        simpa [Term.eval] using hBound _ _ hLookup
    | fvar sort id =>
        simpa [Term.eval] using hFree sort id
    | app symbol hArguments =>
        simp only [Term.eval]
        congr 1
        exact Term.evalList_eq_of_argsWellSorted_env hArguments hBound hFree
    | apply hFunction hArgument =>
        simp only [Term.eval]
        rw [Term.eval_eq_of_wellSorted_env hFunction hBound hFree,
          Term.eval_eq_of_wellSorted_env hArgument hBound hFree]
    | lam hBody =>
        simp only [Term.eval]
        congr 1
        funext value
        apply Term.eval_eq_of_wellSorted_env hBody
        · intro index target hLookup
          cases index with
          | zero =>
              rfl
          | succ previous =>
              exact hBound previous target hLookup
        · intro target id
          exact hFree target id

  /-- 类型正确参数列表的解释逐项满足同一环境外延原则。 -/
  theorem Term.evalList_eq_of_argsWellSorted_env {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} {context : Context σ}
      {env₁ env₂ : Env M} {terms : List (Term σ)}
      {sorts : List (SimpleType σ.BaseSort)}
      (hTerms : ArgsWellSorted context terms sorts)
      (hBound :
        ∀ index target,
          Context.lookup? context index = some target →
            env₁.boundVal index = env₂.boundVal index)
      (hFree : ∀ target id, env₁.freeVal target id = env₂.freeVal target id) :
      terms.map (Term.eval env₁) = terms.map (Term.eval env₂) := by
    cases hTerms with
    | nil =>
        rfl
    | cons hTerm hRest =>
        simp only [List.map_cons]
        rw [Term.eval_eq_of_wellSorted_env hTerm hBound hFree,
          Term.evalList_eq_of_argsWellSorted_env hRest hBound hFree]
end

/--
良构公式的满足关系只依赖当前上下文可见的 bound 值和全部 typed free 值。

空上下文公式因此可以忽略环境中不可见的 bound 尾部；这正是把预处理后的闭字句
搬到任意 HO 自由变量环境时需要的环境外延原则。
-/
theorem Formula.satisfies_iff_of_wellFormed_env
    {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {context : Context σ} {env₁ env₂ : Env M} {formula : Formula σ}
    (hFormula : FormulaWellFormed context formula)
    (hBound :
      ∀ index target,
        Context.lookup? context index = some target →
          env₁.boundVal index = env₂.boundVal index)
    (hFree : ∀ target id, env₁.freeVal target id = env₂.freeVal target id) :
    Formula.Satisfies env₁ formula ↔ Formula.Satisfies env₂ formula := by
  induction hFormula generalizing env₁ env₂ with
  | falsum | truth =>
      simp [Formula.Satisfies]
  | rel symbol hArguments =>
      simp only [Formula.Satisfies]
      rw [Term.evalList_eq_of_argsWellSorted_env hArguments hBound hFree]
  | equal hLeft hRight =>
      simp only [Formula.Satisfies]
      rw [Term.eval_eq_of_wellSorted_env hLeft hBound hFree,
        Term.eval_eq_of_wellSorted_env hRight hBound hFree]
  | neg hBody ih =>
      simp only [Formula.Satisfies]
      exact not_congr (ih hBound hFree)
  | conj hLeft hRight ihLeft ihRight =>
      simp only [Formula.Satisfies]
      exact and_congr (ihLeft hBound hFree) (ihRight hBound hFree)
  | disj hLeft hRight ihLeft ihRight =>
      simp only [Formula.Satisfies]
      exact or_congr (ihLeft hBound hFree) (ihRight hBound hFree)
  | imp hLeft hRight ihLeft ihRight =>
      simp only [Formula.Satisfies]
      exact imp_congr (ihLeft hBound hFree) (ihRight hBound hFree)
  | iff hLeft hRight ihLeft ihRight =>
      simp only [Formula.Satisfies]
      exact iff_congr (ihLeft hBound hFree) (ihRight hBound hFree)
  | forallE hBody ih =>
      simp only [Formula.Satisfies]
      constructor
      · intro h value hValue
        apply (ih
          (env₁ := env₁.push value) (env₂ := env₂.push value)
          (by
            intro index target hLookup
            cases index with
            | zero => rfl
            | succ previous => exact hBound previous target hLookup)
          (by
            intro target id
            exact hFree target id)).mp
        exact h value hValue
      · intro h value hValue
        apply (ih
          (env₁ := env₁.push value) (env₂ := env₂.push value)
          (by
            intro index target hLookup
            cases index with
            | zero => rfl
            | succ previous => exact hBound previous target hLookup)
          (by
            intro target id
            exact hFree target id)).mpr
        exact h value hValue
  | existsE hBody ih =>
      simp only [Formula.Satisfies]
      constructor
      · rintro ⟨value, hValue, hBodySat⟩
        refine ⟨value, hValue, ?_⟩
        exact (ih
          (env₁ := env₁.push value) (env₂ := env₂.push value)
          (by
            intro index target hLookup
            cases index with
            | zero => rfl
            | succ previous => exact hBound previous target hLookup)
          (by
            intro target id
            exact hFree target id)).mp hBodySat
      · rintro ⟨value, hValue, hBodySat⟩
        refine ⟨value, hValue, ?_⟩
        exact (ih
          (env₁ := env₁.push value) (env₂ := env₂.push value)
          (by
            intro index target hLookup
            cases index with
            | zero => rfl
            | succ previous => exact hBound previous target hLookup)
          (by
            intro target id
            exact hFree target id)).mpr hBodySat

namespace TermSubstitution

/--
`targetEnv` 是从 `sourceEnv` 按 substitution 更新自由变量得到的环境。

bound 栈保持一致；命中的 free variable 在目标环境中解释为 replacement 在源环境中的值。
-/
def EnvMatches {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (substitution : TermSubstitution σ)
    (sourceEnv targetEnv : Env M) : Prop :=
  (∀ index, targetEnv.boundVal index = sourceEnv.boundVal index) ∧
    ∀ sort id,
      targetEnv.freeVal sort id =
        match substitution.lookup sort id with
        | some replacement => Term.eval sourceEnv replacement
        | none => sourceEnv.freeVal sort id

/-- 从可采纳 substitution 与源环境构造目标环境。 -/
def semanticEnv {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (substitution : TermSubstitution σ)
    (sourceEnv : Env M) : Env M where
  boundVal := sourceEnv.boundVal
  freeVal := fun sort id =>
    match substitution.lookup sort id with
    | some replacement => Term.eval sourceEnv replacement
    | none => sourceEnv.freeVal sort id

/-- `semanticEnv` 满足 substitution 的环境关系。 -/
theorem semanticEnv_matches {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv : Env M} :
    EnvMatches substitution sourceEnv (semanticEnv substitution sourceEnv) := by
  constructor
  · intro index
    rfl
  · intro sort id
    rfl

namespace EnvMatches

/-- substitution 环境关系在两侧压入同一个 bound 值后保持。 -/
theorem push {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv targetEnv : Env M} (hAdmissible : substitution.Admissible)
    (hEnv : EnvMatches substitution sourceEnv targetEnv) (value : M.Domain) :
    EnvMatches substitution (sourceEnv.push value) (targetEnv.push value) := by
  constructor
  · intro index
    cases index with
    | zero =>
        rfl
    | succ previous =>
        simpa using hEnv.1 previous
  · intro sort id
    cases hLookup : substitution.lookup sort id with
    | none =>
        simpa [Env.push, hLookup] using hEnv.2 sort id
    | some replacement =>
        have hSort : replacement.inferSort? = some sort :=
          hAdmissible sort id replacement hLookup
        have hCurrent :
            targetEnv.freeVal sort id = Term.eval sourceEnv replacement := by
          simpa [hLookup] using hEnv.2 sort id
        have hStable :
            Term.eval (sourceEnv.push value) replacement =
              Term.eval sourceEnv replacement := by
          apply Term.eval_eq_of_wellSorted_env
            (Term.inferSortWith_sound (by simpa [Term.inferSort?] using hSort))
          · intro index target hContext
            simp [Context.lookup?] at hContext
          · intro target freeId
            rfl
        simpa [Env.push, hLookup] using hCurrent.trans hStable.symm

end EnvMatches

end TermSubstitution

namespace FreeVarRenaming

/-- 自由变量平移对应的环境投影关系。 -/
def EnvMatches {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (offset : Nat) (sourceEnv targetEnv : Env M) : Prop :=
  (∀ index, targetEnv.boundVal index = sourceEnv.boundVal index) ∧
    ∀ sort id, targetEnv.freeVal sort id = sourceEnv.freeVal sort (id + offset)

/-- 从平移后的源环境构造原编号可消费的目标环境。 -/
def semanticEnv {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (offset : Nat) (sourceEnv : Env M) : Env M where
  boundVal := sourceEnv.boundVal
  freeVal := fun sort id => sourceEnv.freeVal sort (id + offset)

/-- 自由变量投影环境保持空上下文类型正确性。 -/
theorem semanticEnv_wellSorted {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {offset : Nat} {sourceEnv : Env M}
    (hSource : sourceEnv.WellSorted []) :
    (semanticEnv offset sourceEnv).WellSorted [] := by
  constructor
  · intro index sort hLookup
    simp [Context.lookup?] at hLookup
  · intro sort id
    exact hSource.2 sort (id + offset)

/-- `semanticEnv` 满足自由变量平移的环境关系。 -/
theorem semanticEnv_matches {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {offset : Nat} {sourceEnv : Env M} :
    EnvMatches offset sourceEnv (semanticEnv offset sourceEnv) := by
  constructor
  · intro index
    rfl
  · intro sort id
    rfl

namespace EnvMatches

/-- 自由变量平移环境关系在两侧压入同一个 bound 值后保持。 -/
theorem push {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {offset : Nat} {sourceEnv targetEnv : Env M}
    (hEnv : EnvMatches offset sourceEnv targetEnv) (value : M.Domain) :
    EnvMatches offset (sourceEnv.push value) (targetEnv.push value) := by
  constructor
  · intro index
    cases index with
    | zero =>
        rfl
    | succ previous =>
        simpa using hEnv.1 previous
  · intro sort id
    simpa [Env.push] using hEnv.2 sort id

end EnvMatches

end FreeVarRenaming

mutual
  /-- typed substitution 的项语义。 -/
  theorem Term.eval_applySubstitution_eq_of_envMatches
      {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
      {sourceEnv targetEnv : Env M} (hAdmissible : substitution.Admissible)
      (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv) :
      ∀ term : Term σ,
        Term.eval sourceEnv (term.applySubstitution substitution) =
          Term.eval targetEnv term
    | .var (.bvar sort index) => by
        simpa [Term.applySubstitution, Term.eval] using (hEnv.1 index).symm
    | .var (.fvar sort id) => by
        cases hLookup : substitution.lookup sort id with
        | none =>
            simpa [Term.applySubstitution, Term.eval, hLookup] using
              (hEnv.2 sort id).symm
        | some replacement =>
            simpa [Term.applySubstitution, Term.eval, hLookup] using
              (hEnv.2 sort id).symm
    | .app symbol arguments => by
        simp only [Term.applySubstitution, Term.eval]
        congr 1
        exact Term.evalList_applySubstitution_eq_of_envMatches
          hAdmissible hEnv arguments
    | .apply function argument => by
        simp only [Term.applySubstitution, Term.eval]
        rw [Term.eval_applySubstitution_eq_of_envMatches hAdmissible hEnv function,
          Term.eval_applySubstitution_eq_of_envMatches hAdmissible hEnv argument]
    | .lam domain codomain body => by
        simp only [Term.applySubstitution, Term.eval]
        congr 1
        funext value
        exact Term.eval_applySubstitution_eq_of_envMatches hAdmissible
          (TermSubstitution.EnvMatches.push hAdmissible hEnv value) body

  /-- typed substitution 的项列表语义。 -/
  theorem Term.evalList_applySubstitution_eq_of_envMatches
      {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
      {sourceEnv targetEnv : Env M} (hAdmissible : substitution.Admissible)
      (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv) :
      ∀ terms : List (Term σ),
        (Term.applySubstitutionList substitution terms).map (Term.eval sourceEnv) =
          terms.map (Term.eval targetEnv)
    | [] => by
        rfl
    | term :: rest => by
        simp only [Term.applySubstitutionList, List.map_cons]
        rw [Term.eval_applySubstitution_eq_of_envMatches hAdmissible hEnv term,
          Term.evalList_applySubstitution_eq_of_envMatches hAdmissible hEnv rest]
end

mutual
  /-- 自由变量平移的项语义。 -/
  theorem Term.eval_renameFreeVars_eq_of_envMatches
      {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
      {offset : Nat} {sourceEnv targetEnv : Env M}
      (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
      ∀ term : Term σ,
        Term.eval sourceEnv (term.renameFreeVars offset) = Term.eval targetEnv term
    | .var (.bvar sort index) => by
        simpa [Term.renameFreeVars, Term.eval] using (hEnv.1 index).symm
    | .var (.fvar sort id) => by
        simpa [Term.renameFreeVars, Term.eval] using (hEnv.2 sort id).symm
    | .app symbol arguments => by
        simp only [Term.renameFreeVars, Term.eval]
        congr 1
        exact Term.evalList_renameFreeVars_eq_of_envMatches hEnv arguments
    | .apply function argument => by
        simp only [Term.renameFreeVars, Term.eval]
        rw [Term.eval_renameFreeVars_eq_of_envMatches hEnv function,
          Term.eval_renameFreeVars_eq_of_envMatches hEnv argument]
    | .lam domain codomain body => by
        simp only [Term.renameFreeVars, Term.eval]
        congr 1
        funext value
        exact Term.eval_renameFreeVars_eq_of_envMatches
          (FreeVarRenaming.EnvMatches.push hEnv value) body

  /-- 自由变量平移的项列表语义。 -/
  theorem Term.evalList_renameFreeVars_eq_of_envMatches
      {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
      {offset : Nat} {sourceEnv targetEnv : Env M}
      (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
      ∀ terms : List (Term σ),
        (Term.renameFreeVarsList offset terms).map (Term.eval sourceEnv) =
          terms.map (Term.eval targetEnv)
    | [] => by
        rfl
    | term :: rest => by
        simp only [Term.renameFreeVarsList, List.map_cons]
        rw [Term.eval_renameFreeVars_eq_of_envMatches hEnv term,
          Term.evalList_renameFreeVars_eq_of_envMatches hEnv rest]
end

mutual
  /-- `shiftAbove` 的语义是跳过环境中的对应区段。 -/
  theorem Term.eval_shiftAbove {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} (env : Env M) (amount cutoff : Nat)
      (term : Term σ) :
      Term.eval env (Term.shiftAbove amount cutoff term) =
        Term.eval (env.skip amount cutoff) term := by
    cases term with
    | var value =>
        cases value with
        | bvar sort index =>
            by_cases hIndex : index < cutoff
            · simp [Term.shiftAbove, Term.eval, Env.skip, hIndex]
            · simp [Term.shiftAbove, Term.eval, Env.skip, hIndex]
        | fvar sort id =>
            simp [Term.shiftAbove, Term.eval, Env.skip]
    | app symbol arguments =>
        simp only [Term.shiftAbove, Term.eval]
        congr 1
        exact Term.evalList_shiftAbove env amount cutoff arguments
    | apply function argument =>
        simp [Term.shiftAbove, Term.eval, Term.eval_shiftAbove]
    | lam domain codomain body =>
        simp only [Term.shiftAbove, Term.eval]
        congr 1
        funext value
        rw [Term.eval_shiftAbove]
        apply Term.eval_eq_of_env_eq
        · exact Env.skip_push_bound amount cutoff env value
        · intro sort id
          rfl

  /-- `shiftAbove` 对项列表的语义。 -/
  theorem Term.evalList_shiftAbove {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} (env : Env M) (amount cutoff : Nat)
      (terms : List (Term σ)) :
      (Term.shiftListAbove amount cutoff terms).map (Term.eval env) =
        terms.map (Term.eval (env.skip amount cutoff)) := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp only [Term.shiftListAbove, List.map_cons]
        rw [Term.eval_shiftAbove env amount cutoff head,
          Term.evalList_shiftAbove env amount cutoff tail]
end

mutual
  /-- locally nameless 实例化的项语义。 -/
  theorem Term.eval_instantiateAt {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} (env : Env M) (depth : Nat)
      (replacement term : Term σ) :
      Term.eval env (Term.instantiateAt depth replacement term) =
        Term.eval
          (env.insertAt depth (Term.eval (env.drop depth) replacement)) term := by
    cases term with
    | var value =>
        cases value with
        | bvar sort index =>
            by_cases hLt : index < depth
            · simp [Term.instantiateAt, Term.eval, Env.insertAt, hLt]
            · by_cases hEq : index = depth
              · subst index
                calc
                  Term.eval env
                      (Term.instantiateAt depth replacement (.var (.bvar sort depth))) =
                      Term.eval env (Term.shiftAbove depth 0 replacement) := by
                        simp [Term.instantiateAt]
                  _ = Term.eval (env.skip depth 0) replacement :=
                    Term.eval_shiftAbove env depth 0 replacement
                  _ = Term.eval (env.drop depth) replacement := by
                    apply Term.eval_eq_of_env_eq
                    · exact Env.skip_zero_bound depth env
                    · intro target id
                      rfl
                  _ = Term.eval
                      (env.insertAt depth (Term.eval (env.drop depth) replacement))
                      (.var (.bvar sort depth)) := by
                        simp [Term.eval, Env.insertAt]
              · simp [Term.instantiateAt, Term.eval, Env.insertAt, hLt, hEq]
        | fvar sort id =>
            simp [Term.instantiateAt, Term.eval, Env.insertAt]
    | app symbol arguments =>
        simp only [Term.instantiateAt, Term.eval]
        congr 1
        exact Term.evalList_instantiateAt env depth replacement arguments
    | apply function argument =>
        simp [Term.instantiateAt, Term.eval, Term.eval_instantiateAt]
    | lam domain codomain body =>
        simp only [Term.instantiateAt, Term.eval]
        congr 1
        funext value
        rw [Term.eval_instantiateAt]
        apply Term.eval_eq_of_env_eq
        · intro index
          rw [Term.eval_eq_of_env_eq ((env.push value).drop (depth + 1))
            (env.drop depth) (Env.drop_push_bound depth env value)
            (by intro target id; rfl) replacement]
          exact Env.insertAt_push_bound depth env _ value index
        · intro target id
          rfl

  /-- locally nameless 实例化对项列表的语义。 -/
  theorem Term.evalList_instantiateAt {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} (env : Env M) (depth : Nat)
      (replacement : Term σ) (terms : List (Term σ)) :
      (Term.instantiateListAt depth replacement terms).map (Term.eval env) =
        terms.map
          (Term.eval
            (env.insertAt depth (Term.eval (env.drop depth) replacement))) := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp only [Term.instantiateListAt, List.map_cons]
        rw [Term.eval_instantiateAt env depth replacement head,
          Term.evalList_instantiateAt env depth replacement tail]
end

namespace Term

/-- 最外层 lambda 实例化与向环境压入实参具有相同语义。 -/
theorem eval_instantiate {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (env : Env M)
    (replacement body : Term σ) :
    Term.eval env (Term.instantiate replacement body) =
      Term.eval (env.push (Term.eval env replacement)) body := by
  rw [Term.instantiate, Term.eval_instantiateAt]
  apply Term.eval_eq_of_env_eq
  · intro index
    cases index with
    | zero =>
        simp [Env.insertAt, Env.drop, Env.push]
    | succ previous =>
        simp [Env.insertAt, Env.drop, Env.push]
  · intro sort id
    rfl

end Term

mutual
  /-- 类型正确项的解释落在声明的 simple sort 中。 -/
  theorem Term.eval_sort_of_wellSorted {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} {context : Context σ} {env : Env M}
      {term : Term σ} {sort : SimpleType σ.BaseSort}
      (hEnv : Env.WellSorted context env)
      (hTerm : TermWellSorted context term sort) :
      M.sortInterp sort (Term.eval env term) := by
    cases hTerm with
    | bvar hLookup =>
        simpa [Term.eval] using hEnv.1 _ _ hLookup
    | fvar sort id =>
        simpa [Term.eval] using hEnv.2 sort id
    | app symbol hArguments =>
        simpa [Term.eval] using
          M.funcSort symbol _ (args_satisfy_of_wellSorted hEnv hArguments)
    | apply hFunction hArgument =>
        simpa [Term.eval] using
          M.applySort _ _ _ _
            (Term.eval_sort_of_wellSorted hEnv hFunction)
            (Term.eval_sort_of_wellSorted hEnv hArgument)
    | lam hBody =>
        simp only [Term.eval]
        apply M.lambdaSort
        intro value hValue
        exact Term.eval_sort_of_wellSorted (Env.wellSorted_push hEnv hValue) hBody

  /-- 类型正确参数列表的解释逐项满足符号签名。 -/
  theorem args_satisfy_of_wellSorted {σ : Signature.{u, v, w}}
      {M : Structure.{u, v, w, x} σ} {context : Context σ} {env : Env M}
      {terms : List (Term σ)} {sorts : List (SimpleType σ.BaseSort)}
      (hEnv : Env.WellSorted context env)
      (hTerms : ArgsWellSorted context terms sorts) :
      ArgsSatisfy M.sortInterp (terms.map (Term.eval env)) sorts := by
    cases hTerms with
    | nil =>
        simp [ArgsSatisfy]
    | cons hTerm hRest =>
        exact ⟨Term.eval_sort_of_wellSorted hEnv hTerm,
          args_satisfy_of_wellSorted (hEnv := hEnv) hRest⟩
end

namespace Term

/-- checker 成功的项在任意类型正确环境中都保持其推断 sort。 -/
theorem eval_sort_of_inferSortWith {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {context : Context σ} {env : Env M} {term : Term σ}
    {sort : SimpleType σ.BaseSort}
    (hEnv : Env.WellSorted context env)
    (hCheck : term.inferSortWith context = some sort) :
    M.sortInterp sort (term.eval env) :=
  Term.eval_sort_of_wellSorted hEnv (Term.inferSortWith_sound hCheck)

end Term

namespace TermSubstitution

/-- 可采纳 substitution 诱导的环境仍满足空上下文的 typed 合同。 -/
theorem semanticEnv_wellSorted {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv : Env M} (hAdmissible : substitution.Admissible)
    (hSource : sourceEnv.WellSorted []) :
    (semanticEnv substitution sourceEnv).WellSorted [] := by
  constructor
  · intro index sort hLookup
    simp [Context.lookup?] at hLookup
  · intro sort id
    cases hLookup : substitution.lookup sort id with
    | none =>
        simpa [semanticEnv, hLookup] using hSource.2 sort id
    | some replacement =>
        have hSort : replacement.inferSort? = some sort :=
          hAdmissible sort id replacement hLookup
        simpa [semanticEnv, hLookup] using
          Term.eval_sort_of_inferSortWith hSource
            (by simpa [Term.inferSort?] using hSort)

end TermSubstitution

namespace ExtensionalContract

/-- β 规则的对象层语义。 -/
theorem eval_beta {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (contract : ExtensionalContract M) (env : Env M)
    (domain codomain : SimpleType σ.BaseSort) (body argument : Term σ)
    (hBody :
      ∀ value, M.sortInterp domain value →
        M.sortInterp codomain (Term.eval (env.push value) body))
    (hArgument : M.sortInterp domain (Term.eval env argument)) :
    Term.eval env (.apply (.lam domain codomain body) argument) =
      Term.eval (env.push (Term.eval env argument)) body := by
  simpa [Term.eval] using contract.beta domain codomain
    (fun value => Term.eval (env.push value) body) (Term.eval env argument)
    hBody hArgument

/-- 规范 η 展开形在外延模型中与原函数项相等。 -/
theorem eval_eta {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (contract : ExtensionalContract M) (env : Env M)
    (domain codomain : SimpleType σ.BaseSort) (function : Term σ)
    (hFunction :
      M.sortInterp (.arrow domain codomain) (Term.eval env function)) :
    Term.eval env
        (.lam domain codomain
          (.apply (Term.shiftAbove 1 0 function) (.var (.bvar domain 0)))) =
      Term.eval env function := by
  simp only [Term.eval]
  have hPointwise :
      (fun value =>
          M.applyInterp
            (Term.eval (env.push value) (Term.shiftAbove 1 0 function))
            ((env.push value).boundVal 0)) =
        (fun value => M.applyInterp (Term.eval env function) value) := by
    funext value
    simp only [Env.push_bound_zero]
    rw [Term.eval_shiftAbove]
    congr 1
  rw [hPointwise, contract.eta domain codomain _ hFunction]

end ExtensionalContract

namespace ExtensionalWitnessContract

/-- 显式 `diff left right` 项在函数不等时确实给出区分实参。 -/
theorem eval_distinguishes {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (contract : ExtensionalWitnessContract M)
    (env : Env M) (hEnv : env.WellSorted [])
    (symbol : σ.FuncSymbol) (domain codomain : SimpleType σ.BaseSort)
    (left right : Term σ)
    (hWitness : σ.isFunctionExtensionalityWitness symbol = true)
    (hDomain :
      σ.funcDomain symbol = [.arrow domain codomain, .arrow domain codomain])
    (hCodomain : σ.funcCodomain symbol = domain)
    (hLeft : left.inferSort? = some (.arrow domain codomain))
    (hRight : right.inferSort? = some (.arrow domain codomain))
    (hNe : left.eval env ≠ right.eval env) :
    Term.eval env (.apply left (.app symbol [left, right])) ≠
      Term.eval env (.apply right (.app symbol [left, right])) := by
  simp only [Term.eval]
  exact contract.distinguishes symbol domain codomain _ _
    hWitness hDomain hCodomain
    (Term.eval_sort_of_inferSortWith hEnv (by simpa [Term.inferSort?] using hLeft))
    (Term.eval_sort_of_inferSortWith hEnv (by simpa [Term.inferSort?] using hRight))
    hNe

end ExtensionalWitnessContract

end HigherOrder
end Logic
end YesMetaZFC
