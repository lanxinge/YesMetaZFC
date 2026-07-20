import YesMetaZFC.Logic.HigherOrder.Signature

/-!
# 简单类型高阶局部无名语法

bound 变量使用统一的 de Bruijn 栈，因此 lambda 与高阶量词可以自然交错。
每个变量仍携带 sort，checker 会复核该标注与绑定上下文完全一致。
-/

namespace YesMetaZFC
namespace Logic
namespace HigherOrder

universe u v w

abbrev FreeVarId := Nat

/-- 高阶变量。 -/
inductive Var (σ : Signature.{u, v, w}) where
  | bvar (sort : SimpleType σ.BaseSort) (index : Nat)
  | fvar (sort : SimpleType σ.BaseSort) (id : FreeVarId)

namespace Var

/-- 变量携带的简单类型。 -/
def sort {σ : Signature.{u, v, w}} : Var σ → SimpleType σ.BaseSort
  | .bvar sort _ => sort
  | .fvar sort _ => sort

end Var

/-- 原生高阶项。`app` 保存签名中的未柯里化应用，`apply` 与 `lam` 保存 HO 结构。 -/
inductive Term (σ : Signature.{u, v, w}) where
  | var (value : Var σ)
  | app (symbol : σ.FuncSymbol) (arguments : List (Term σ))
  | apply (function argument : Term σ)
  | lam (domain codomain : SimpleType σ.BaseSort) (body : Term σ)

/-- 高阶公式；量词允许绑定任意简单类型。 -/
inductive Formula (σ : Signature.{u, v, w}) where
  | falsum
  | truth
  | rel (symbol : σ.RelSymbol) (arguments : List (Term σ))
  | equal (sort : SimpleType σ.BaseSort) (left right : Term σ)
  | neg (body : Formula σ)
  | conj (left right : Formula σ)
  | disj (left right : Formula σ)
  | imp (left right : Formula σ)
  | iff (left right : Formula σ)
  | forallE (sort : SimpleType σ.BaseSort) (body : Formula σ)
  | existsE (sort : SimpleType σ.BaseSort) (body : Formula σ)

/-- 本地绑定上下文按 de Bruijn 索引从近到远排列。 -/
abbrev Context (σ : Signature.{u, v, w}) := List (SimpleType σ.BaseSort)

namespace Context

/-- 透明的 de Bruijn 上下文查找。 -/
def lookup? {σ : Signature.{u, v, w}} :
    Context σ → Nat → Option (SimpleType σ.BaseSort)
  | [], _ => none
  | sort :: _, 0 => some sort
  | _ :: rest, index + 1 => lookup? rest index

end Context

mutual
  /-- 项在上下文中的类型正确性。 -/
  inductive TermWellSorted {σ : Signature.{u, v, w}} :
      Context σ → Term σ → SimpleType σ.BaseSort → Prop where
    | bvar {context : Context σ} {sort : SimpleType σ.BaseSort} {index : Nat}
        (hLookup : Context.lookup? context index = some sort) :
        TermWellSorted context (.var (.bvar sort index)) sort
    | fvar {context : Context σ} (sort : SimpleType σ.BaseSort) (id : FreeVarId) :
        TermWellSorted context (.var (.fvar sort id)) sort
    | app {context : Context σ} (symbol : σ.FuncSymbol) {arguments : List (Term σ)}
        (hArguments : ArgsWellSorted context arguments (σ.funcDomain symbol)) :
        TermWellSorted context (.app symbol arguments) (σ.funcCodomain symbol)
    | apply {context : Context σ} {function argument : Term σ}
        {domain codomain : SimpleType σ.BaseSort}
        (hFunction : TermWellSorted context function (.arrow domain codomain))
        (hArgument : TermWellSorted context argument domain) :
        TermWellSorted context (.apply function argument) codomain
    | lam {context : Context σ} {domain codomain : SimpleType σ.BaseSort} {body : Term σ}
        (hBody : TermWellSorted (domain :: context) body codomain) :
        TermWellSorted context (.lam domain codomain body) (.arrow domain codomain)

  /-- 参数列表逐项匹配符号签名。 -/
  inductive ArgsWellSorted {σ : Signature.{u, v, w}} :
      Context σ → List (Term σ) → List (SimpleType σ.BaseSort) → Prop where
    | nil {context : Context σ} : ArgsWellSorted context [] []
    | cons {context : Context σ} {term : Term σ} {terms : List (Term σ)}
        {sort : SimpleType σ.BaseSort} {sorts : List (SimpleType σ.BaseSort)}
        (hTerm : TermWellSorted context term sort)
        (hRest : ArgsWellSorted context terms sorts) :
        ArgsWellSorted context (term :: terms) (sort :: sorts)
end

/-- 公式在上下文中的类型正确性。 -/
inductive FormulaWellFormed {σ : Signature.{u, v, w}} :
    Context σ → Formula σ → Prop where
  | falsum {context : Context σ} : FormulaWellFormed context .falsum
  | truth {context : Context σ} : FormulaWellFormed context .truth
  | rel {context : Context σ} (symbol : σ.RelSymbol) {arguments : List (Term σ)}
      (hArguments : ArgsWellSorted context arguments (σ.relDomain symbol)) :
      FormulaWellFormed context (.rel symbol arguments)
  | equal {context : Context σ} {sort : SimpleType σ.BaseSort} {left right : Term σ}
      (hLeft : TermWellSorted context left sort)
      (hRight : TermWellSorted context right sort) :
      FormulaWellFormed context (.equal sort left right)
  | neg {context : Context σ} {body : Formula σ}
      (hBody : FormulaWellFormed context body) :
      FormulaWellFormed context (.neg body)
  | conj {context : Context σ} {left right : Formula σ}
      (hLeft : FormulaWellFormed context left)
      (hRight : FormulaWellFormed context right) :
      FormulaWellFormed context (.conj left right)
  | disj {context : Context σ} {left right : Formula σ}
      (hLeft : FormulaWellFormed context left)
      (hRight : FormulaWellFormed context right) :
      FormulaWellFormed context (.disj left right)
  | imp {context : Context σ} {left right : Formula σ}
      (hLeft : FormulaWellFormed context left)
      (hRight : FormulaWellFormed context right) :
      FormulaWellFormed context (.imp left right)
  | iff {context : Context σ} {left right : Formula σ}
      (hLeft : FormulaWellFormed context left)
      (hRight : FormulaWellFormed context right) :
      FormulaWellFormed context (.iff left right)
  | forallE {context : Context σ} {sort : SimpleType σ.BaseSort} {body : Formula σ}
      (hBody : FormulaWellFormed (sort :: context) body) :
      FormulaWellFormed context (.forallE sort body)
  | existsE {context : Context σ} {sort : SimpleType σ.BaseSort} {body : Formula σ}
      (hBody : FormulaWellFormed (sort :: context) body) :
      FormulaWellFormed context (.existsE sort body)

mutual
  /-- 在绑定上下文中推断项的简单类型。失败同时表示 scope 或 sort 错误。 -/
  def Term.inferSortWith {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      (context : Context σ) : Term σ → Option (SimpleType σ.BaseSort)
    | .var (.bvar sort index) =>
        if Context.lookup? context index = some sort then some sort else none
    | .var (.fvar sort _) => some sort
    | .app symbol arguments => do
        let sorts ← Term.inferSortListWith context arguments
        if sorts = σ.funcDomain symbol then some (σ.funcCodomain symbol) else none
    | .apply function argument => do
        let functionSort ← Term.inferSortWith context function
        let argumentSort ← Term.inferSortWith context argument
        match functionSort with
        | .arrow domain codomain =>
            if argumentSort = domain then some codomain else none
        | .base _ => none
    | .lam domain codomain body => do
        let bodySort ← Term.inferSortWith (domain :: context) body
        if bodySort = codomain then some (.arrow domain codomain) else none

  /-- 推断参数列表的逐项类型。 -/
  def Term.inferSortListWith {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      (context : Context σ) : List (Term σ) → Option (List (SimpleType σ.BaseSort))
    | [] => some []
    | term :: rest => do
        let sort ← Term.inferSortWith context term
        let sorts ← Term.inferSortListWith context rest
        some (sort :: sorts)
end

namespace Term

/-- 在空绑定上下文中检查闭项并返回其类型。 -/
def inferSort? {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (term : Term σ) : Option (SimpleType σ.BaseSort) :=
  term.inferSortWith []

/-- 闭项的可计算类型检查。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort] (term : Term σ) : Bool :=
  term.inferSort?.isSome

end Term

mutual
  /-- 项 checker 成功时生成对应的归纳类型证据。 -/
  theorem Term.inferSortWith_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      {context : Context σ} {term : Term σ} {sort : SimpleType σ.BaseSort}
      (hCheck : term.inferSortWith context = some sort) :
      TermWellSorted context term sort := by
    cases term with
    | var value =>
        cases value with
        | bvar annotated index =>
            by_cases hLookup : Context.lookup? context index = some annotated
            · simp [Term.inferSortWith, hLookup] at hCheck
              subst sort
              exact .bvar hLookup
            · simp [Term.inferSortWith, hLookup] at hCheck
        | fvar annotated id =>
            simp [Term.inferSortWith] at hCheck
            subst sort
            exact .fvar annotated id
    | app symbol arguments =>
        cases hArguments : Term.inferSortListWith context arguments with
        | none =>
            simp [Term.inferSortWith, hArguments] at hCheck
        | some argumentSorts =>
            by_cases hSorts : argumentSorts = σ.funcDomain symbol
            · subst argumentSorts
              simp [Term.inferSortWith, hArguments] at hCheck
              subst sort
              exact .app symbol (Term.inferSortListWith_sound hArguments)
            · simp [Term.inferSortWith, hArguments, hSorts] at hCheck
    | apply function argument =>
        cases hFunction : Term.inferSortWith context function with
        | none =>
            simp [Term.inferSortWith, hFunction] at hCheck
        | some functionSort =>
            cases hArgument : Term.inferSortWith context argument with
            | none =>
                simp [Term.inferSortWith, hFunction, hArgument] at hCheck
            | some argumentSort =>
                cases functionSort with
                | base symbol =>
                    simp [Term.inferSortWith, hFunction, hArgument] at hCheck
                | arrow domain codomain =>
                    by_cases hDomain : argumentSort = domain
                    · simp [Term.inferSortWith, hFunction, hArgument, hDomain] at hCheck
                      subst argumentSort
                      subst sort
                      exact .apply (Term.inferSortWith_sound hFunction)
                        (Term.inferSortWith_sound hArgument)
                    · simp [Term.inferSortWith, hFunction, hArgument, hDomain] at hCheck
    | lam domain codomain body =>
        cases hBody : Term.inferSortWith (domain :: context) body with
        | none =>
            simp [Term.inferSortWith, hBody] at hCheck
        | some bodySort =>
            by_cases hCodomain : bodySort = codomain
            · simp [Term.inferSortWith, hBody, hCodomain] at hCheck
              subst bodySort
              subst sort
              exact .lam (Term.inferSortWith_sound hBody)
            · simp [Term.inferSortWith, hBody, hCodomain] at hCheck

  /-- 参数列表 checker 成功时生成逐项类型证据。 -/
  theorem Term.inferSortListWith_sound {σ : Signature.{u, v, w}}
      [DecidableEq σ.BaseSort] {context : Context σ} {terms : List (Term σ)}
      {sorts : List (SimpleType σ.BaseSort)}
      (hCheck : Term.inferSortListWith context terms = some sorts) :
      ArgsWellSorted context terms sorts := by
    cases terms with
    | nil =>
        simp [Term.inferSortListWith] at hCheck
        subst sorts
        exact .nil
    | cons term rest =>
        cases hTerm : Term.inferSortWith context term with
        | none =>
            simp [Term.inferSortListWith, hTerm] at hCheck
        | some sort =>
            cases hRest : Term.inferSortListWith context rest with
            | none =>
                simp [Term.inferSortListWith, hTerm, hRest] at hCheck
            | some restSorts =>
                simp [Term.inferSortListWith, hTerm, hRest] at hCheck
                subst sorts
                exact .cons (Term.inferSortWith_sound hTerm)
                  (Term.inferSortListWith_sound hRest)
end

namespace Formula

/-- 公式的可计算 scope 与 sort 检查。 -/
def checkWith {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (context : Context σ) : Formula σ → Bool
  | .falsum | .truth => true
  | .rel symbol arguments =>
      Term.inferSortListWith context arguments == some (σ.relDomain symbol)
  | .equal sort left right =>
      left.inferSortWith context == some sort && right.inferSortWith context == some sort
  | .neg body => body.checkWith context
  | .conj left right | .disj left right | .imp left right | .iff left right =>
      left.checkWith context && right.checkWith context
  | .forallE sort body | .existsE sort body => body.checkWith (sort :: context)

/-- 闭公式的可计算检查。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (formula : Formula σ) : Bool :=
  formula.checkWith []

/-- 公式 checker 的正确性。 -/
theorem checkWith_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {context : Context σ} {formula : Formula σ}
    (hCheck : formula.checkWith context = true) :
    FormulaWellFormed context formula := by
  induction formula generalizing context with
  | falsum => exact .falsum
  | truth => exact .truth
  | rel symbol arguments =>
      simp [checkWith] at hCheck
      exact .rel symbol (Term.inferSortListWith_sound hCheck)
  | equal sort left right =>
      simp [checkWith] at hCheck
      exact .equal (Term.inferSortWith_sound hCheck.1)
        (Term.inferSortWith_sound hCheck.2)
  | neg body ih =>
      exact .neg (ih hCheck)
  | conj left right ihLeft ihRight =>
      simp [checkWith] at hCheck
      exact .conj (ihLeft hCheck.1) (ihRight hCheck.2)
  | disj left right ihLeft ihRight =>
      simp [checkWith] at hCheck
      exact .disj (ihLeft hCheck.1) (ihRight hCheck.2)
  | imp left right ihLeft ihRight =>
      simp [checkWith] at hCheck
      exact .imp (ihLeft hCheck.1) (ihRight hCheck.2)
  | iff left right ihLeft ihRight =>
      simp [checkWith] at hCheck
      exact .iff (ihLeft hCheck.1) (ihRight hCheck.2)
  | forallE sort body ih =>
      exact .forallE (ih hCheck)
  | existsE sort body ih =>
      exact .existsE (ih hCheck)

end Formula

mutual
  /-- 大于等于 cutoff 的 de Bruijn 索引整体上移。 -/
  def Term.shiftAbove {σ : Signature.{u, v, w}} (amount cutoff : Nat) : Term σ → Term σ
    | .var (.bvar sort index) =>
        if index < cutoff then .var (.bvar sort index) else .var (.bvar sort (index + amount))
    | .var (.fvar sort id) => .var (.fvar sort id)
    | .app symbol arguments => .app symbol (Term.shiftListAbove amount cutoff arguments)
    | .apply function argument =>
        .apply (function.shiftAbove amount cutoff) (argument.shiftAbove amount cutoff)
    | .lam domain codomain body =>
        .lam domain codomain (body.shiftAbove amount (cutoff + 1))

  /-- 对项列表执行 de Bruijn 上移。 -/
  def Term.shiftListAbove {σ : Signature.{u, v, w}} (amount cutoff : Nat) :
      List (Term σ) → List (Term σ)
    | [] => []
    | term :: rest =>
        term.shiftAbove amount cutoff :: Term.shiftListAbove amount cutoff rest
end

mutual
  /-- 用项替换指定深度的 de Bruijn 变量。 -/
  def Term.instantiateAt {σ : Signature.{u, v, w}} (depth : Nat)
      (replacement : Term σ) : Term σ → Term σ
    | .var (.bvar sort index) =>
        if index < depth then
          .var (.bvar sort index)
        else if index = depth then
          replacement.shiftAbove depth 0
        else
          .var (.bvar sort (index - 1))
    | .var (.fvar sort id) => .var (.fvar sort id)
    | .app symbol arguments =>
        .app symbol (Term.instantiateListAt depth replacement arguments)
    | .apply function argument =>
        .apply (Term.instantiateAt depth replacement function)
          (Term.instantiateAt depth replacement argument)
    | .lam domain codomain body =>
        .lam domain codomain (Term.instantiateAt (depth + 1) replacement body)

  /-- 对项列表执行局部无名替换。 -/
  def Term.instantiateListAt {σ : Signature.{u, v, w}} (depth : Nat)
      (replacement : Term σ) : List (Term σ) → List (Term σ)
    | [] => []
    | term :: rest =>
        Term.instantiateAt depth replacement term ::
          Term.instantiateListAt depth replacement rest
end

/-- 替换最外层 lambda 绑定变量。 -/
def Term.instantiate {σ : Signature.{u, v, w}} (replacement body : Term σ) : Term σ :=
  Term.instantiateAt 0 replacement body

/-- 原生 HO substitution 的带类型 binding。 -/
structure TermBinding (σ : Signature.{u, v, w}) where
  sort : SimpleType σ.BaseSort
  id : FreeVarId
  replacement : Term σ

/-- 原生 HO 有限 substitution；靠前 binding 优先。 -/
abbrev TermSubstitution (σ : Signature.{u, v, w}) := List (TermBinding σ)

namespace TermSubstitution

/-- 查找一个带 simple type 的自由变量 binding。 -/
def lookup {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (substitution : TermSubstitution σ) (sort : SimpleType σ.BaseSort)
    (id : FreeVarId) : Option (Term σ) :=
  match substitution with
  | [] => none
  | binding :: rest =>
      if binding.sort = sort ∧ binding.id = id then
        some binding.replacement
      else
        lookup rest sort id

/-- 指定 key 没有出现在 substitution 中。 -/
def keyAbsent {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (sort : SimpleType σ.BaseSort) (id : FreeVarId) : TermSubstitution σ → Bool
  | [] => true
  | binding :: rest =>
      decide (binding.sort ≠ sort ∨ binding.id ≠ id) && keyAbsent sort id rest

/-- substitution 中每个 replacement 都闭合、类型正确，并且 key 唯一。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort] :
    TermSubstitution σ → Bool
  | [] => true
  | binding :: rest =>
      decide (binding.replacement.inferSort? = some binding.sort) &&
        keyAbsent binding.sort binding.id rest && check rest

/-- substitution 的语义可采纳性。 -/
def Admissible {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (substitution : TermSubstitution σ) : Prop :=
  ∀ sort id replacement,
    lookup substitution sort id = some replacement →
      replacement.inferSort? = some sort

/-- substitution checker 成功时，每个可查得 replacement 都具有 key 声明的类型。 -/
theorem check_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort] :
    ∀ {substitution : TermSubstitution σ},
      check substitution = true → Admissible substitution
  | [], _hCheck => by
      intro sort id replacement hLookup
      simp [lookup] at hLookup
  | binding :: rest, hCheck => by
      have hFields :
          (decide (binding.replacement.inferSort? = some binding.sort) = true ∧
            keyAbsent binding.sort binding.id rest = true) ∧
            check rest = true := by
        simpa [check] using hCheck
      have hBinding :
          binding.replacement.inferSort? = some binding.sort :=
        of_decide_eq_true hFields.1.1
      have hRest : Admissible rest := check_sound hFields.2
      intro sort id replacement hLookup
      by_cases hKey : binding.sort = sort ∧ binding.id = id
      · rcases hKey with ⟨rfl, rfl⟩
        have hReplacement : replacement = binding.replacement := by
          have hSome :
              some binding.replacement = some replacement := by
            simpa [lookup] using hLookup
          exact (Option.some.inj hSome).symm
        simpa [hReplacement] using hBinding
      · have hLookupRest : lookup rest sort id = some replacement := by
          simpa [lookup, hKey] using hLookup
        exact hRest sort id replacement hLookupRest

end TermSubstitution

mutual
  /-- 将 typed substitution 作用到原生 HO 项。 -/
  def Term.applySubstitution {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
      (substitution : TermSubstitution σ) : Term σ → Term σ
    | .var (.bvar sort index) => .var (.bvar sort index)
    | .var (.fvar sort id) =>
        match substitution.lookup sort id with
        | some replacement => replacement
        | none => .var (.fvar sort id)
    | .app symbol arguments =>
        .app symbol (Term.applySubstitutionList substitution arguments)
    | .apply function argument =>
        .apply (function.applySubstitution substitution)
          (argument.applySubstitution substitution)
    | .lam domain codomain body =>
        .lam domain codomain (body.applySubstitution substitution)

  /-- 将 typed substitution 作用到项列表。 -/
  def Term.applySubstitutionList {σ : Signature.{u, v, w}}
      [DecidableEq σ.BaseSort] (substitution : TermSubstitution σ) :
      List (Term σ) → List (Term σ)
    | [] => []
    | term :: rest =>
        term.applySubstitution substitution ::
          Term.applySubstitutionList substitution rest
end

mutual
  /-- 将原生 HO 项中的自由变量编号整体平移。 -/
  def Term.renameFreeVars {σ : Signature.{u, v, w}} (offset : Nat) :
      Term σ → Term σ
    | .var (.bvar sort index) => .var (.bvar sort index)
    | .var (.fvar sort id) => .var (.fvar sort (id + offset))
    | .app symbol arguments =>
        .app symbol (Term.renameFreeVarsList offset arguments)
    | .apply function argument =>
        .apply (function.renameFreeVars offset) (argument.renameFreeVars offset)
    | .lam domain codomain body =>
        .lam domain codomain (body.renameFreeVars offset)

  /-- 将项列表中的自由变量编号整体平移。 -/
  def Term.renameFreeVarsList {σ : Signature.{u, v, w}} (offset : Nat) :
      List (Term σ) → List (Term σ)
    | [] => []
    | term :: rest =>
        term.renameFreeVars offset :: Term.renameFreeVarsList offset rest
end

end HigherOrder
end Logic
end YesMetaZFC
