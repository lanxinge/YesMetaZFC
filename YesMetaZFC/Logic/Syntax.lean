import YesMetaZFC.Logic.Syntax.Core

/-!
# 内在语法的替换、结构合同与新鲜性

逐点映射合同沿有限 AST 递归；仅真正断言函数相等的兼容接口使用函数外延。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w

mutual

/--
尝试删除 free 上下文顶部变量。成功时返回处于较小上下文中的同一项；失败表示该
变量确实在项中出现。
-/
def Term.strengthenFreeTop? {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sort : σ.SortSymbol} →
      Term σ bound (introduced :: free) sort →
        Option (Term σ bound free sort)
  | _, .bvar entry => some (.bvar entry)
  | _, .fvar .here => none
  | _, .fvar (.there previous) => some (.fvar previous)
  | _, .app function arguments =>
      match Arguments.strengthenFreeTop? introduced arguments with
      | some strengthened => some (.app function strengthened)
      | none => none

/-- 参数列的可计算 free-context strengthening。 -/
def Arguments.strengthenFreeTop? {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sorts : List σ.SortSymbol} →
      Arguments σ bound (introduced :: free) sorts →
        Option (Arguments σ bound free sorts)
  | _, .nil => some .nil
  | _, .cons term rest =>
      match term.strengthenFreeTop? introduced with
      | none => none
      | some strengthenedTerm =>
          match Arguments.strengthenFreeTop? introduced rest with
          | none => none
          | some strengthenedRest => some (.cons strengthenedTerm strengthenedRest)

end


/-- 对任意源上下文结构递归，随后核对待删除的头变量。 -/
private def Formula.strengthenFreeTopAux {σ : Signature.{u, v, w}}
    {bound sourceFree : SortContext σ} :
    (formula : Formula σ bound sourceFree) → ∀ {introduced free},
    sourceFree = introduced :: free → Option (Formula σ bound free)
  | .falsum, _, _, _ => some .falsum
  | .truth, _, _, _ => some .truth
  | .rel relation arguments, introduced, _, h => by
      cases h
      exact (arguments.strengthenFreeTop? introduced).map (Formula.rel relation)
  | .equal left right, introduced, _, h => by
      cases h
      exact (left.strengthenFreeTop? introduced).bind
        (fun reduced => (right.strengthenFreeTop? introduced).map (Formula.equal reduced))
  | .neg f, _, _, h => (Formula.strengthenFreeTopAux f h).map Formula.neg
  | .conj left right, _, _, h =>
      (Formula.strengthenFreeTopAux left h).bind
        (fun reduced => (Formula.strengthenFreeTopAux right h).map (Formula.conj reduced))
  | .disj left right, _, _, h =>
      (Formula.strengthenFreeTopAux left h).bind
        (fun reduced => (Formula.strengthenFreeTopAux right h).map (Formula.disj reduced))
  | .imp left right, _, _, h =>
      (Formula.strengthenFreeTopAux left h).bind
        (fun reduced => (Formula.strengthenFreeTopAux right h).map (Formula.imp reduced))
  | .iff left right, _, _, h =>
      (Formula.strengthenFreeTopAux left h).bind
        (fun reduced => (Formula.strengthenFreeTopAux right h).map (Formula.iff reduced))
  | .forallE s f, _, _, h => (Formula.strengthenFreeTopAux f h).map (Formula.forallE s)
  | .existsE s f, _, _, h => (Formula.strengthenFreeTopAux f h).map (Formula.existsE s)
termination_by structural formula => formula

/-- 公式的可计算 free-context strengthening。 -/
def Formula.strengthenFreeTop? {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    Formula σ bound (introduced :: free) → Option (Formula σ bound free) :=
  fun formula => Formula.strengthenFreeTopAux formula rfl

/-- 将一个变量上下文解释为目标上下文中的同排序项。 -/
abbrev VariableSubstitution (σ : Signature.{u, v, w})
    (source targetBound targetFree : SortContext σ) :=
  {sort : σ.SortSymbol} →
    Variable source sort → Term σ targetBound targetFree sort

namespace VariableSubstitution

/-- 从空变量上下文到任意项上下文的唯一替换。 -/
def empty {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    VariableSubstitution σ [] bound free :=
  fun entry => nomatch entry

/-- 在变量替换头部指定一个项像，其余变量沿用既有替换。 -/
def cons {σ : Signature.{u, v, w}}
    {source bound free : SortContext σ} {sort : σ.SortSymbol}
    (head : Term σ bound free sort)
    (tail : VariableSubstitution σ source bound free) :
    VariableSubstitution σ (sort :: source) bound free :=
  fun entry =>
    match entry with
    | .here => head
    | .there previous => tail previous

/-- free 替换穿过同一个规范新变量。 -/
def liftFree {σ : Signature.{u, v, w}}
    {source bound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source bound targetFree) :
    VariableSubstitution σ (introduced :: source) bound
      (introduced :: targetFree) :=
  fun entry =>
    match entry with
    | .here => .fvar .here
    | .there previous =>
        (substitution previous).weakenFree introduced

/-- bound 变量的恒等替换。 -/
def boundId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    VariableSubstitution σ bound bound free :=
  fun entry => .bvar entry

/-- free 变量的恒等替换。 -/
def freeId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    VariableSubstitution σ free bound free :=
  fun entry => .fvar entry

/-- 替换结果整体穿过一个新 binder。 -/
def weakenBound {σ : Signature.{u, v, w}}
    {source targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source targetBound targetFree) :
    VariableSubstitution σ source (introduced :: targetBound) targetFree :=
  fun entry => (substitution entry).weakenBound introduced

/-- bound-closed 的替换像整体嵌入任意 binder 上下文。 -/
def embedBoundClosed {σ : Signature.{u, v, w}}
    {source targetFree : SortContext σ}
    (targetBound : SortContext σ)
    (substitution : VariableSubstitution σ source [] targetFree) :
    VariableSubstitution σ source targetBound targetFree :=
  fun entry => (substitution entry).embedBoundClosed targetBound

@[simp] theorem embedBoundClosed_nil {σ : Signature.{u, v, w}}
    {source targetFree : SortContext σ}
    (substitution : VariableSubstitution σ source [] targetFree) :
    @embedBoundClosed σ source targetFree [] substitution =
      (fun {sort} (entry : Variable source sort) => substitution entry) :=
  rfl

@[simp] theorem embedBoundClosed_cons {σ : Signature.{u, v, w}}
    {source targetFree : SortContext σ}
    (introduced : σ.SortSymbol) (rest : SortContext σ)
    (substitution : VariableSubstitution σ source [] targetFree) :
    @embedBoundClosed σ source targetFree (introduced :: rest) substitution =
      @weakenBound σ source rest targetFree introduced
        (@embedBoundClosed σ source targetFree rest substitution) :=
  rfl

/-- bound 替换穿过同一个新 binder。 -/
def liftBound {σ : Signature.{u, v, w}}
    {source targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source targetBound targetFree) :
    VariableSubstitution σ (introduced :: source)
      (introduced :: targetBound) targetFree :=
  fun entry =>
    match entry with
    | .here => .bvar .here
    | .there previous =>
        (substitution previous).weakenBound introduced

/-- 用一个项实例化上下文顶部的 bound 变量。 -/
def instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    VariableSubstitution σ (sort :: bound) bound free :=
  fun entry =>
    match entry with
    | .here => replacement
    | .there previous => .bvar previous

/-- 用一个项实例化 free 上下文顶部变量。 -/
def instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    VariableSubstitution σ (sort :: free) bound free
  | _, .here => replacement
  | _, .there previous => .fvar previous

/-- 原 bound 变量在引入新 binder 后整体后移。 -/
def abstractBound {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    VariableSubstitution σ bound (introduced :: bound) free
  | _, entry => .bvar (.there entry)

/-- free 上下文顶部变量转为最新 binder，其余 free 变量保持不变。 -/
def abstractFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    VariableSubstitution σ (sort :: free) (sort :: bound) free
  | _, .here => .bvar .here
  | _, .there previous => .fvar previous

end VariableSubstitution

/--
同时作用于 bound/free 变量的替换。`.id` 使恒等替换无需检查语法树根节点以下内容。
-/
inductive Substitution (σ : Signature.{u, v, w}) :
    SortContext σ → SortContext σ → SortContext σ → SortContext σ →
      Type (max u v w) where
  | id {bound free : SortContext σ} :
      Substitution σ bound free bound free
  | map {sourceBound sourceFree targetBound targetFree : SortContext σ} :
      VariableSubstitution σ sourceBound targetBound targetFree →
      VariableSubstitution σ sourceFree targetBound targetFree →
      Substitution σ sourceBound sourceFree targetBound targetFree

namespace Substitution

/-- 替换穿过同一个新 binder；恒等替换保持 `.id`。 -/
def liftBound {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol) :
    Substitution σ sourceBound sourceFree targetBound targetFree →
      Substitution σ (introduced :: sourceBound) sourceFree
        (introduced :: targetBound) targetFree
  | .id => .id
  | .map boundSubstitution freeSubstitution =>
      .map (VariableSubstitution.liftBound introduced boundSubstitution)
        (VariableSubstitution.weakenBound introduced freeSubstitution)

/-- 用一个项实例化上下文顶部的 bound 变量。 -/
def instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Substitution σ (sort :: bound) free bound free :=
  .map (VariableSubstitution.instantiateTop replacement)
    VariableSubstitution.freeId

/-- 用一个项实例化 free 上下文顶部变量。 -/
def instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Substitution σ bound (sort :: free) bound free :=
  .map VariableSubstitution.boundId
    (VariableSubstitution.instantiateFreeTop replacement)

/-- free 上下文顶部变量转为最新 binder。 -/
def abstractFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    Substitution σ bound (sort :: free) (sort :: bound) free :=
  .map (VariableSubstitution.abstractBound sort)
    VariableSubstitution.abstractFreeTop

end Substitution

mutual

/-- 执行非恒等项替换。公共入口 `Term.substitute` 负责恒等快路径。 -/
def Term.substituteMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sort : σ.SortSymbol} →
      Term σ sourceBound sourceFree sort → Term σ targetBound targetFree sort
  | _, .bvar entry => boundSubstitution entry
  | _, .fvar entry => freeSubstitution entry
  | _, .app function arguments =>
      .app function
        (Arguments.substituteMapped boundSubstitution freeSubstitution arguments)

/-- 执行非恒等参数列替换。 -/
def Arguments.substituteMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sorts : List σ.SortSymbol} →
      Arguments σ sourceBound sourceFree sorts →
        Arguments σ targetBound targetFree sorts
  | _, .nil => .nil
  | _, .cons term rest =>
      .cons (term.substituteMapped boundSubstitution freeSubstitution)
        (Arguments.substituteMapped boundSubstitution freeSubstitution rest)

end

/-- 同时替换项的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def Term.substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    Term σ targetBound targetFree sort :=
  match τ with
  | .id => term
  | .map boundSubstitution freeSubstitution =>
      term.substituteMapped boundSubstitution freeSubstitution

/-- 同时替换参数列的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def Arguments.substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    Arguments σ targetBound targetFree sorts :=
  match τ with
  | .id => arguments
  | .map boundSubstitution freeSubstitution =>
      arguments.substituteMapped boundSubstitution freeSubstitution

/-- 用同排序项实例化项最外层的 binder。 -/
def Term.instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (body : Term σ (sort :: bound) free resultSort)
    (replacement : Term σ bound free sort) :
    Term σ bound free resultSort :=
  body.substitute (Substitution.instantiateTop replacement)

/-- 用同排序项实例化异质参数列最外层的 binder。 -/
def Arguments.instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (sort :: bound) free sorts)
    (replacement : Term σ bound free sort) :
    Arguments σ bound free sorts :=
  arguments.substitute (Substitution.instantiateTop replacement)

/-- 用同排序项实例化项 free 上下文顶部变量。 -/
def Term.instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (body : Term σ bound (sort :: free) resultSort)
    (replacement : Term σ bound free sort) :
    Term σ bound free resultSort :=
  body.substitute (Substitution.instantiateFreeTop replacement)

/-- 用同排序项实例化参数列 free 上下文顶部变量。 -/
def Arguments.instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound (sort :: free) sorts)
    (replacement : Term σ bound free sort) :
    Arguments σ bound free sorts :=
  arguments.substitute (Substitution.instantiateFreeTop replacement)

namespace Substitution

/--
替换的 Kleisli 复合。恒等情形直接返回原对象；两个非恒等替换只复合变量像，不在
此处遍历待替换 AST。
-/
def comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree) :
    Substitution σ sourceBound sourceFree targetBound targetFree :=
  match outer, inner with
  | .id, inner => inner
  | outer, .id => outer
  | .map outerBound outerFree, .map innerBound innerFree =>
      .map
        (fun entry => (innerBound entry).substituteMapped
          outerBound outerFree)
        (fun entry => (innerFree entry).substituteMapped
          outerBound outerFree)

end Substitution

namespace Formula

/-- 执行非恒等公式替换。公共入口 `Formula.substitute` 负责恒等快路径。 -/
def substituteMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    Formula σ sourceBound sourceFree → Formula σ targetBound targetFree
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments =>
      .rel relation
        (Arguments.substituteMapped boundSubstitution freeSubstitution arguments)
  | .equal left right =>
      .equal (left.substituteMapped boundSubstitution freeSubstitution)
        (right.substituteMapped boundSubstitution freeSubstitution)
  | .neg body =>
      .neg (substituteMapped boundSubstitution freeSubstitution body)
  | .conj left right =>
      .conj (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .disj left right =>
      .disj (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .imp left right =>
      .imp (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .iff left right =>
      .iff (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .forallE sort body =>
      .forallE sort
        (substituteMapped
          (VariableSubstitution.liftBound sort boundSubstitution)
          (VariableSubstitution.weakenBound sort freeSubstitution)
          body)
  | .existsE sort body =>
      .existsE sort
        (substituteMapped
          (VariableSubstitution.liftBound sort boundSubstitution)
          (VariableSubstitution.weakenBound sort freeSubstitution)
          body)

/-- 同时替换公式的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    Formula σ targetBound targetFree :=
  match τ with
  | .id => formula
  | .map boundSubstitution freeSubstitution =>
      substituteMapped boundSubstitution freeSubstitution formula

/-- 用同排序项实例化公式体最外层的 binder。 -/
def instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (sort :: bound) free) :
    Formula σ bound free :=
  body.substitute (Substitution.instantiateTop replacement)

/-- 用同排序项实例化公式 free 上下文顶部变量。 -/
def instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ bound (sort :: free)) :
    Formula σ bound free :=
  body.substitute (Substitution.instantiateFreeTop replacement)

/--
把 free 上下文顶部变量转为最新 binder。该操作不需要 freshness 或自然数避让证明。
-/
def abstractFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (body : Formula σ bound (sort :: free)) :
    Formula σ (sort :: bound) free :=
  body.substitute Substitution.abstractFreeTop

/-- 量化 free 上下文顶部变量。 -/
def forallFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ bound (sort :: free)) :
    Formula σ bound free :=
  .forallE sort body.abstractFreeTop

/-- 存在量化 free 上下文顶部变量。 -/
def existsFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ bound (sort :: free)) :
    Formula σ bound free :=
  .existsE sort body.abstractFreeTop

end Formula

mutual

/-- 项的结构节点数。 -/
def Term.size {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    Term σ bound free sort → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .app _ arguments => arguments.size + 1

/-- 参数列中所有项的结构节点数。 -/
def Arguments.size {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} → Arguments σ bound free sorts → Nat
  | _, .nil => 0
  | _, .cons term rest => term.size + rest.size

end

namespace Formula

/-- 公式及其项参数的结构节点数。 -/
def size {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} : Formula σ bound free → Nat
  | .falsum => 1
  | .truth => 1
  | .rel _ arguments => arguments.size + 1
  | .equal left right => left.size + right.size + 1
  | .neg body => body.size + 1
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right => left.size + right.size + 1
  | .forallE _ body
  | .existsE _ body => body.size + 1

end Formula

private theorem congrArg₂ {α : Sort u} {β : Sort v} {γ : Sort w}
    (f : α → β → γ) {left₁ left₂ : α} {right₁ right₂ : β}
    (hLeft : left₁ = left₂) (hRight : right₁ = right₂) :
    f left₁ right₁ = f left₂ right₂ :=
  congr (congrArg f hLeft) hRight

mutual

/-- 逐变量相等的映射在有限项上给出相同结果，无需映射函数外延。 -/
theorem Term.renameMapped_congr {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {leftBound rightBound : VariableRenaming sourceBound targetBound}
    {leftFree rightFree : VariableRenaming sourceFree targetFree}
    (hBound : ∀ {sort} (entry : Variable sourceBound sort),
      leftBound entry = rightBound entry)
    (hFree : ∀ {sort} (entry : Variable sourceFree sort),
      leftFree entry = rightFree entry) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      term.renameMapped leftBound leftFree = term.renameMapped rightBound rightFree
  | _, .bvar entry => congrArg Term.bvar (hBound entry)
  | _, .fvar entry => congrArg Term.fvar (hFree entry)
  | _, .app function arguments =>
      congrArg (Term.app function) (Arguments.renameMapped_congr hBound hFree arguments)

/-- 逐变量相等的映射在异质参数列上给出相同结果。 -/
theorem Arguments.renameMapped_congr {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {leftBound rightBound : VariableRenaming sourceBound targetBound}
    {leftFree rightFree : VariableRenaming sourceFree targetFree}
    (hBound : ∀ {sort} (entry : Variable sourceBound sort),
      leftBound entry = rightBound entry)
    (hFree : ∀ {sort} (entry : Variable sourceFree sort),
      leftFree entry = rightFree entry) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
      arguments.renameMapped leftBound leftFree = arguments.renameMapped rightBound rightFree
  | _, .nil => rfl
  | _, .cons term rest =>
      congrArg₂ Arguments.cons (Term.renameMapped_congr hBound hFree term)
        (Arguments.renameMapped_congr hBound hFree rest)

end

/-- 逐变量相等的映射在公式上给出相同结果；量词只提升逐点证书。 -/
theorem Formula.renameMapped_congr {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {leftBound rightBound : VariableRenaming sourceBound targetBound}
    {leftFree rightFree : VariableRenaming sourceFree targetFree}
    (hBound : ∀ {sort} (entry : Variable sourceBound sort),
      leftBound entry = rightBound entry)
    (hFree : ∀ {sort} (entry : Variable sourceFree sort),
      leftFree entry = rightFree entry) :
    (formula : Formula σ sourceBound sourceFree) →
      formula.renameMapped leftBound leftFree = formula.renameMapped rightBound rightFree
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments =>
      congrArg (Formula.rel relation) (Arguments.renameMapped_congr hBound hFree arguments)
  | .equal left right =>
      congrArg₂ Formula.equal (Term.renameMapped_congr hBound hFree left)
        (Term.renameMapped_congr hBound hFree right)
  | .neg body => congrArg Formula.neg (Formula.renameMapped_congr hBound hFree body)
  | .conj left right =>
      congrArg₂ Formula.conj (Formula.renameMapped_congr hBound hFree left)
        (Formula.renameMapped_congr hBound hFree right)
  | .disj left right =>
      congrArg₂ Formula.disj (Formula.renameMapped_congr hBound hFree left)
        (Formula.renameMapped_congr hBound hFree right)
  | .imp left right =>
      congrArg₂ Formula.imp (Formula.renameMapped_congr hBound hFree left)
        (Formula.renameMapped_congr hBound hFree right)
  | .iff left right =>
      congrArg₂ Formula.iff (Formula.renameMapped_congr hBound hFree left)
        (Formula.renameMapped_congr hBound hFree right)
  | .forallE sort body => by
      apply congrArg (Formula.forallE sort)
      apply Formula.renameMapped_congr (hFree := hFree)
      intro resultSort entry
      cases entry with
      | here => rfl
      | there previous => exact congrArg Variable.there (hBound previous)
  | .existsE sort body => by
      apply congrArg (Formula.existsE sort)
      apply Formula.renameMapped_congr (hFree := hFree)
      intro resultSort entry
      cases entry with
      | here => rfl
      | there previous => exact congrArg Variable.there (hBound previous)
mutual

/-- 逐变量相等的映射在有限项上给出相同结果，无需映射函数外延。 -/
theorem Term.substituteMapped_congr {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {leftBound rightBound : VariableSubstitution σ sourceBound targetBound targetFree}
    {leftFree rightFree : VariableSubstitution σ sourceFree targetBound targetFree}
    (hBound : ∀ {sort} (entry : Variable sourceBound sort),
      leftBound entry = rightBound entry)
    (hFree : ∀ {sort} (entry : Variable sourceFree sort),
      leftFree entry = rightFree entry) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      term.substituteMapped leftBound leftFree = term.substituteMapped rightBound rightFree
  | _, .bvar entry => hBound entry
  | _, .fvar entry => hFree entry
  | _, .app function arguments =>
      congrArg (Term.app function) (Arguments.substituteMapped_congr hBound hFree arguments)

/-- 逐变量相等的映射在异质参数列上给出相同结果。 -/
theorem Arguments.substituteMapped_congr {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {leftBound rightBound : VariableSubstitution σ sourceBound targetBound targetFree}
    {leftFree rightFree : VariableSubstitution σ sourceFree targetBound targetFree}
    (hBound : ∀ {sort} (entry : Variable sourceBound sort),
      leftBound entry = rightBound entry)
    (hFree : ∀ {sort} (entry : Variable sourceFree sort),
      leftFree entry = rightFree entry) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
      arguments.substituteMapped leftBound leftFree = arguments.substituteMapped rightBound rightFree
  | _, .nil => rfl
  | _, .cons term rest =>
      congrArg₂ Arguments.cons (Term.substituteMapped_congr hBound hFree term)
        (Arguments.substituteMapped_congr hBound hFree rest)

end

/-- 逐变量相等的映射在公式上给出相同结果；量词只提升逐点证书。 -/
theorem Formula.substituteMapped_congr {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    {leftBound rightBound : VariableSubstitution σ sourceBound targetBound targetFree}
    {leftFree rightFree : VariableSubstitution σ sourceFree targetBound targetFree}
    (hBound : ∀ {sort} (entry : Variable sourceBound sort),
      leftBound entry = rightBound entry)
    (hFree : ∀ {sort} (entry : Variable sourceFree sort),
      leftFree entry = rightFree entry) :
    (formula : Formula σ sourceBound sourceFree) →
      formula.substituteMapped leftBound leftFree = formula.substituteMapped rightBound rightFree
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments =>
      congrArg (Formula.rel relation) (Arguments.substituteMapped_congr hBound hFree arguments)
  | .equal left right =>
      congrArg₂ Formula.equal (Term.substituteMapped_congr hBound hFree left)
        (Term.substituteMapped_congr hBound hFree right)
  | .neg body => congrArg Formula.neg (Formula.substituteMapped_congr hBound hFree body)
  | .conj left right =>
      congrArg₂ Formula.conj (Formula.substituteMapped_congr hBound hFree left)
        (Formula.substituteMapped_congr hBound hFree right)
  | .disj left right =>
      congrArg₂ Formula.disj (Formula.substituteMapped_congr hBound hFree left)
        (Formula.substituteMapped_congr hBound hFree right)
  | .imp left right =>
      congrArg₂ Formula.imp (Formula.substituteMapped_congr hBound hFree left)
        (Formula.substituteMapped_congr hBound hFree right)
  | .iff left right =>
      congrArg₂ Formula.iff (Formula.substituteMapped_congr hBound hFree left)
        (Formula.substituteMapped_congr hBound hFree right)
  | .forallE sort body => by
      apply congrArg (Formula.forallE sort)
      apply Formula.substituteMapped_congr (hFree := (fun entry => congrArg (Term.weakenBound sort) (hFree entry)))
      intro resultSort entry
      cases entry with
      | here => rfl
      | there previous => exact congrArg (Term.weakenBound sort) (hBound previous)
  | .existsE sort body => by
      apply congrArg (Formula.existsE sort)
      apply Formula.substituteMapped_congr (hFree := (fun entry => congrArg (Term.weakenBound sort) (hFree entry)))
      intro resultSort entry
      cases entry with
      | here => rfl
      | there previous => exact congrArg (Term.weakenBound sort) (hBound previous)

namespace VariableRenaming

/-- 顶部交换是自身的逆。 -/
@[simp] theorem swapTop_swapTop {S : Type u} {Γ : List S}
    {first second resultSort : S}
    (entry : Variable (first :: second :: Γ) resultSort) :
    (swapTop : VariableRenaming (second :: first :: Γ)
      (first :: second :: Γ))
      ((swapTop : VariableRenaming (first :: second :: Γ)
        (second :: first :: Γ)) entry) = entry := by
  cases entry with
  | here => rfl
  | there previous =>
      cases previous <;> rfl

/-- 恒等变量映射穿过 binder 后仍与恒等映射外延相等。 -/
@[simp] theorem lift_id {S : Type u} {Γ : List S} {introduced : S} :
    (lift (introduced := introduced) (id (Γ := Γ)) :
      VariableRenaming (introduced :: Γ) (introduced :: Γ)) =
      (id : VariableRenaming (introduced :: Γ) (introduced :: Γ)) := by
  funext sort entry
  cases entry <;> rfl

/-- 提升保持变量映射复合。 -/
@[simp] theorem lift_comp {S : Type u}
    {source middle target : List S} {introduced : S}
    (outer : VariableRenaming middle target)
    (inner : VariableRenaming source middle) :
    (lift (introduced := introduced) (comp outer inner) :
      VariableRenaming (introduced :: source) (introduced :: target)) =
      (comp (lift outer) (lift inner) :
        VariableRenaming (introduced :: source) (introduced :: target)) := by
  funext sort entry
  cases entry <;> rfl

end VariableRenaming

/-!
## 局部归约方程

这些方程只展开一个语法构造子。后续证明使用它们，而不把完整重命名执行器加入
`simp` 展开集。
-/

@[simp] theorem Term.weakenBound_bvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable bound sort) :
    (Term.bvar entry : Term σ bound free sort).weakenBound introduced =
      .bvar (.there entry) :=
  rfl

@[simp] theorem Term.weakenBound_fvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable free sort) :
    (Term.fvar entry : Term σ bound free sort).weakenBound introduced =
      .fvar entry :=
  rfl

@[simp] theorem Term.weakenBound_app {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (function : σ.FuncSymbol)
    (arguments : Arguments σ bound free (σ.funcDomain function)) :
    (Term.app function arguments).weakenBound introduced =
      .app function (arguments.weakenBound introduced) :=
  rfl

@[simp] theorem Arguments.weakenBound_nil {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Arguments.nil : Arguments σ bound free []).weakenBound introduced =
      .nil :=
  rfl

@[simp] theorem Arguments.weakenBound_cons {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    {sorts : List σ.SortSymbol} (term : Term σ bound free sort)
    (rest : Arguments σ bound free sorts) :
    (Arguments.cons term rest).weakenBound introduced =
      .cons (term.weakenBound introduced) (rest.weakenBound introduced) :=
  rfl

@[simp] theorem Term.embedBoundClosed_fvar {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sort : σ.SortSymbol}
    (targetBound : SortContext σ) (entry : Variable free sort) :
    (Term.fvar entry : Term σ [] free sort).embedBoundClosed targetBound =
      .fvar entry := by
  induction targetBound with
  | nil => rfl
  | cons introduced rest ih =>
      exact congrArg (Term.weakenBound introduced) ih

@[simp] theorem Term.embedBoundClosed_app {σ : Signature.{u, v, w}}
    {free : SortContext σ} (targetBound : SortContext σ)
    (function : σ.FuncSymbol)
    (arguments : Arguments σ [] free (σ.funcDomain function)) :
    (Term.app function arguments).embedBoundClosed targetBound =
      .app function (arguments.embedBoundClosed targetBound) := by
  induction targetBound with
  | nil => rfl
  | cons introduced rest ih =>
      exact congrArg (Term.weakenBound introduced) ih

@[simp] theorem Arguments.embedBoundClosed_nil {σ : Signature.{u, v, w}}
    {free : SortContext σ} (targetBound : SortContext σ) :
    (Arguments.nil : Arguments σ [] free []).embedBoundClosed targetBound =
      .nil := by
  induction targetBound with
  | nil => rfl
  | cons introduced rest ih =>
      exact congrArg (Arguments.weakenBound introduced) ih

@[simp] theorem Arguments.embedBoundClosed_cons {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol} (targetBound : SortContext σ)
    (term : Term σ [] free sort) (rest : Arguments σ [] free sorts) :
    (Arguments.cons term rest).embedBoundClosed targetBound =
      .cons (term.embedBoundClosed targetBound)
        (rest.embedBoundClosed targetBound) := by
  induction targetBound with
  | nil => rfl
  | cons introduced targetBound ih =>
      exact congrArg (Arguments.weakenBound introduced) ih

/-- bound 变量不受 free weakening 影响。 -/
@[simp] theorem Term.weakenFree_bvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable bound sort) :
    (Term.bvar entry : Term σ bound free sort).weakenFree introduced =
      .bvar entry :=
  rfl

/-- 旧 free 变量在扩展后后移一位。 -/
@[simp] theorem Term.weakenFree_fvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable free sort) :
    (Term.fvar entry : Term σ bound free sort).weakenFree introduced =
      .fvar (.there entry) :=
  rfl

/-- free weakening 在函数应用上只递归一层。 -/
@[simp] theorem Term.weakenFree_app {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (function : σ.FuncSymbol)
    (arguments : Arguments σ bound free (σ.funcDomain function)) :
    (Term.app function arguments).weakenFree introduced =
      .app function (arguments.weakenFree introduced) :=
  rfl

/-- 显式 free 弱化重命名直接恢复专用快路径。 -/
theorem Term.renameMapped_id_weaken {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    term.renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced) =
      term.weakenFree introduced :=
  rfl

@[simp] theorem Arguments.weakenFree_nil {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Arguments.nil : Arguments σ bound free []).weakenFree introduced =
      .nil :=
  rfl

@[simp] theorem Arguments.weakenFree_cons {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    {sorts : List σ.SortSymbol} (term : Term σ bound free sort)
    (rest : Arguments σ bound free sorts) :
    (Arguments.cons term rest).weakenFree introduced =
      .cons (term.weakenFree introduced) (rest.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_falsum {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Formula.falsum : Formula σ bound free).weakenFree introduced = .falsum :=
  rfl

@[simp] theorem Formula.weakenFree_truth {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Formula.truth : Formula σ bound free).weakenFree introduced = .truth :=
  rfl

@[simp] theorem Formula.weakenFree_rel {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation)) :
    (Formula.rel relation arguments).weakenFree introduced =
      .rel relation (arguments.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_equal {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (left right : Term σ bound free sort) :
    (Formula.equal left right).weakenFree introduced =
      .equal (left.weakenFree introduced) (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_neg {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (body : Formula σ bound free) :
    body.neg.weakenFree introduced = (body.weakenFree introduced).neg :=
  rfl

@[simp] theorem Formula.weakenFree_conj {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.conj right).weakenFree introduced =
      (left.weakenFree introduced).conj (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_disj {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.disj right).weakenFree introduced =
      (left.weakenFree introduced).disj (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_imp {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.imp right).weakenFree introduced =
      (left.weakenFree introduced).imp (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_iff {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.iff right).weakenFree introduced =
      (left.weakenFree introduced).iff (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_forallE {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (body : Formula σ (sort :: bound) free) :
    (Formula.forallE sort body).weakenFree introduced =
      .forallE sort (body.weakenFree introduced) :=
  by
    apply congrArg (Formula.forallE sort)
    apply Formula.renameMapped_congr (hFree := fun _ => rfl)
    intro resultSort entry
    cases entry <;> rfl

@[simp] theorem Formula.weakenFree_existsE {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (body : Formula σ (sort :: bound) free) :
    (Formula.existsE sort body).weakenFree introduced =
      .existsE sort (body.weakenFree introduced) :=
  by
    apply congrArg (Formula.existsE sort)
    apply Formula.renameMapped_congr (hFree := fun _ => rfl)
    intro resultSort entry
    cases entry <;> rfl

/-!
## 基础代数律

这些定律只依赖语法结构，在内核中统一证明；下游不再为每一种对象公式重复恢复
重命名与替换的恒等性。
-/

namespace Renaming

/-- 恒等重命名穿过 binder 后仍由同一个 `.id` 构造子表示。 -/
@[simp] theorem liftBound_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    liftBound introduced
        (Renaming.id : Renaming σ bound free bound free) =
      (Renaming.id :
        Renaming σ (introduced :: bound) free (introduced :: bound) free) :=
  rfl

end Renaming

/-- 项上的恒等重命名在根节点命中快路径。 -/
@[simp] theorem Term.rename_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    term.rename Renaming.id = term :=
  rfl

/-- 参数列上的恒等重命名在根节点命中快路径。 -/
@[simp] theorem Arguments.rename_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    arguments.rename Renaming.id = arguments :=
  rfl

/-- 公式上的恒等重命名在根节点命中快路径。 -/
@[simp] theorem Formula.rename_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (formula : Formula σ bound free) :
    formula.rename Renaming.id = formula :=
  rfl

mutual

/-- 两次非恒等项重命名可合并为一次遍历。 -/
@[simp] theorem Term.renameMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableRenaming middleBound targetBound)
    (outerFree : VariableRenaming middleFree targetFree)
    (innerBound : VariableRenaming sourceBound middleBound)
    (innerFree : VariableRenaming sourceFree middleFree) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      (term.renameMapped innerBound innerFree).renameMapped
          outerBound outerFree =
        term.renameMapped
          (VariableRenaming.comp outerBound innerBound)
          (VariableRenaming.comp outerFree innerFree)
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments =>
      congrArg (Term.app function)
        (Arguments.renameMapped_comp outerBound outerFree innerBound innerFree arguments)

/-- 两次非恒等参数列重命名可合并为一次遍历。 -/
@[simp] theorem Arguments.renameMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableRenaming middleBound targetBound)
    (outerFree : VariableRenaming middleFree targetFree)
    (innerBound : VariableRenaming sourceBound middleBound)
    (innerFree : VariableRenaming sourceFree middleFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
        (arguments.renameMapped innerBound innerFree).renameMapped
            outerBound outerFree =
          arguments.renameMapped
            (VariableRenaming.comp outerBound innerBound)
            (VariableRenaming.comp outerFree innerFree)
  | _, .nil => rfl
  | _, .cons term rest =>
      congrArg₂ Arguments.cons
        (Term.renameMapped_comp outerBound outerFree innerBound innerFree term)
        (Arguments.renameMapped_comp outerBound outerFree innerBound innerFree rest)

end

/-- 两次非恒等公式重命名可合并为一次遍历。 -/
@[simp] theorem Formula.renameMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableRenaming middleBound targetBound)
    (outerFree : VariableRenaming middleFree targetFree)
    (innerBound : VariableRenaming sourceBound middleBound)
    (innerFree : VariableRenaming sourceFree middleFree) :
    (formula : Formula σ sourceBound sourceFree) →
      (formula.renameMapped innerBound innerFree).renameMapped
          outerBound outerFree =
        formula.renameMapped
          (VariableRenaming.comp outerBound innerBound)
          (VariableRenaming.comp outerFree innerFree)
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments =>
      congrArg (Formula.rel relation)
        (Arguments.renameMapped_comp outerBound outerFree innerBound innerFree arguments)
  | .equal left right =>
      congrArg₂ Formula.equal
        (Term.renameMapped_comp outerBound outerFree innerBound innerFree left)
        (Term.renameMapped_comp outerBound outerFree innerBound innerFree right)
  | .neg body => congrArg Formula.neg
      (Formula.renameMapped_comp outerBound outerFree innerBound innerFree body)
  | .conj left right =>
      congrArg₂ Formula.conj
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree right)
  | .disj left right =>
      congrArg₂ Formula.disj
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree right)
  | .imp left right =>
      congrArg₂ Formula.imp
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree right)
  | .iff left right =>
      congrArg₂ Formula.iff
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.renameMapped_comp outerBound outerFree innerBound innerFree right)
  | .forallE sort body => by
      apply congrArg (Formula.forallE sort)
      refine (Formula.renameMapped_comp (VariableRenaming.lift outerBound) outerFree
        (VariableRenaming.lift innerBound) innerFree body).trans ?_
      apply Formula.renameMapped_congr (hFree := fun _ => rfl)
      intro resultSort entry
      cases entry <;> rfl
  | .existsE sort body => by
      apply congrArg (Formula.existsE sort)
      refine (Formula.renameMapped_comp (VariableRenaming.lift outerBound) outerFree
        (VariableRenaming.lift innerBound) innerFree body).trans ?_
      apply Formula.renameMapped_congr (hFree := fun _ => rfl)
      intro resultSort entry
      cases entry <;> rfl

/-- 连续项重命名先复合变换对象，因此只需一次 AST 遍历。 -/
@[simp] theorem Term.rename_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Renaming σ middleBound middleFree targetBound targetFree)
    (inner : Renaming σ sourceBound sourceFree middleBound middleFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.rename inner).rename outer = term.rename (Renaming.comp outer inner) := by
  cases outer with
  | id => rfl
  | map outerBound outerFree =>
      cases inner with
      | id => rfl
      | map innerBound innerFree =>
          exact Term.renameMapped_comp outerBound outerFree innerBound innerFree term

/-- 连续参数列重命名先复合变换对象，因此只需一次 AST 遍历。 -/
@[simp] theorem Arguments.rename_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Renaming σ middleBound middleFree targetBound targetFree)
    (inner : Renaming σ sourceBound sourceFree middleBound middleFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    (arguments.rename inner).rename outer =
      arguments.rename (Renaming.comp outer inner) := by
  cases outer with
  | id => rfl
  | map outerBound outerFree =>
      cases inner with
      | id => rfl
      | map innerBound innerFree =>
          exact Arguments.renameMapped_comp outerBound outerFree innerBound innerFree arguments

/-- 连续公式重命名先复合变换对象，因此只需一次 AST 遍历。 -/
@[simp] theorem Formula.rename_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Renaming σ middleBound middleFree targetBound targetFree)
    (inner : Renaming σ sourceBound sourceFree middleBound middleFree)
    (formula : Formula σ sourceBound sourceFree) :
    (formula.rename inner).rename outer =
      formula.rename (Renaming.comp outer inner) := by
  cases outer with
  | id => rfl
  | map outerBound outerFree =>
      cases inner with
      | id => rfl
      | map innerBound innerFree =>
          exact Formula.renameMapped_comp outerBound outerFree innerBound innerFree formula

mutual

/-- 两次非恒等项替换可合并为一次遍历。 -/
@[simp] theorem Term.substituteMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (innerBound : VariableSubstitution σ sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution σ sourceFree middleBound middleFree) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      (term.substituteMapped innerBound innerFree).substituteMapped
          outerBound outerFree =
        term.substituteMapped
          (fun entry => (innerBound entry).substituteMapped
            outerBound outerFree)
          (fun entry => (innerFree entry).substituteMapped
            outerBound outerFree)
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments =>
      congrArg (Term.app function)
        (Arguments.substituteMapped_comp outerBound outerFree innerBound innerFree arguments)

/-- 两次非恒等参数列替换可合并为一次遍历。 -/
@[simp] theorem Arguments.substituteMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (innerBound : VariableSubstitution σ sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution σ sourceFree middleBound middleFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
        (arguments.substituteMapped innerBound innerFree).substituteMapped
            outerBound outerFree =
          arguments.substituteMapped
            (fun entry => (innerBound entry).substituteMapped
              outerBound outerFree)
            (fun entry => (innerFree entry).substituteMapped
              outerBound outerFree)
  | _, .nil => rfl
  | _, .cons term rest =>
      congrArg₂ Arguments.cons
        (Term.substituteMapped_comp outerBound outerFree innerBound innerFree term)
        (Arguments.substituteMapped_comp outerBound outerFree innerBound innerFree rest)

end

mutual

/-- 非恒等项替换与 bound weakening 交换。 -/
@[simp] theorem Term.substituteMapped_weakenBound
    {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      (term.weakenBound introduced).substituteMapped
          (VariableSubstitution.liftBound introduced boundSubstitution)
          (VariableSubstitution.weakenBound introduced freeSubstitution) =
        (term.substituteMapped boundSubstitution freeSubstitution).weakenBound
          introduced
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments =>
      congrArg (Term.app function)
        (Arguments.substituteMapped_weakenBound introduced
          boundSubstitution freeSubstitution arguments)

/-- 非恒等参数列替换与 bound weakening 交换。 -/
@[simp] theorem Arguments.substituteMapped_weakenBound
    {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
        (arguments.weakenBound introduced).substituteMapped
            (VariableSubstitution.liftBound introduced boundSubstitution)
            (VariableSubstitution.weakenBound introduced freeSubstitution) =
          (arguments.substituteMapped boundSubstitution
            freeSubstitution).weakenBound introduced
  | _, .nil => rfl
  | _, .cons term rest =>
      congrArg₂ Arguments.cons
        (Term.substituteMapped_weakenBound introduced boundSubstitution freeSubstitution term)
        (Arguments.substituteMapped_weakenBound introduced boundSubstitution freeSubstitution rest)

end

/-- 连续项替换先复合变量像，因此只需一次 AST 遍历。 -/
@[simp] theorem Term.substitute_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.substitute inner).substitute outer =
      term.substitute (Substitution.comp outer inner) := by
  cases outer with
  | id => rfl
  | map outerBound outerFree =>
      cases inner with
      | id => rfl
      | map innerBound innerFree =>
          exact Term.substituteMapped_comp outerBound outerFree innerBound innerFree term

/-- 连续参数列替换先复合变量像，因此只需一次 AST 遍历。 -/
@[simp] theorem Arguments.substitute_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    (arguments.substitute inner).substitute outer =
      arguments.substitute (Substitution.comp outer inner) := by
  cases outer with
  | id => rfl
  | map outerBound outerFree =>
      cases inner with
      | id => rfl
      | map innerBound innerFree =>
          exact Arguments.substituteMapped_comp outerBound outerFree innerBound innerFree arguments

namespace VariableSubstitution

/-- bound 恒等替换穿过 binder 后仍是恒等替换。 -/
@[simp] theorem liftBound_boundId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (liftBound introduced (boundId (bound := bound) (free := free)) :
      VariableSubstitution σ (introduced :: bound)
        (introduced :: bound) free) =
      (boundId (bound := introduced :: bound) (free := free) :
        VariableSubstitution σ (introduced :: bound)
          (introduced :: bound) free) := by
  funext sort entry
  cases entry <;> rfl

/-- free 恒等替换的结果穿过 binder 后仍是 free 恒等替换。 -/
@[simp] theorem weakenBound_freeId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (weakenBound introduced (freeId (bound := bound) (free := free)) :
      VariableSubstitution σ free (introduced :: bound) free) =
      (freeId (bound := introduced :: bound) (free := free) :
        VariableSubstitution σ free (introduced :: bound) free) :=
  rfl

/-- 顶部 free 实例化穿过 binder 时，只需提升替换项。 -/
@[simp] theorem weakenBound_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (replacement : Term σ bound free sort) :
    (weakenBound introduced (instantiateFreeTop replacement) :
      VariableSubstitution σ (sort :: free) (introduced :: bound) free) =
      (instantiateFreeTop (replacement.weakenBound introduced) :
        VariableSubstitution σ (sort :: free) (introduced :: bound) free) := by
  funext resultSort entry
  cases entry <;> rfl

/-- lifted 变量替换保持非恒等替换复合。 -/
@[simp] theorem liftBound_substituteMapped
    {σ : Signature.{u, v, w}}
    {source middleBound middleFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (inner : VariableSubstitution σ source middleBound middleFree) :
    (liftBound introduced
        (fun {sort} (entry : Variable source sort) =>
          (inner entry).substituteMapped outerBound outerFree) :
      VariableSubstitution σ (introduced :: source)
        (introduced :: targetBound) targetFree) =
      (fun {sort} (entry : Variable (introduced :: source) sort) =>
        (liftBound introduced inner entry).substituteMapped
          (liftBound introduced outerBound)
          (weakenBound introduced outerFree) :
        VariableSubstitution σ (introduced :: source)
          (introduced :: targetBound) targetFree) := by
  funext sort entry
  cases entry with
  | here => rfl
  | there previous =>
      exact (Term.substituteMapped_weakenBound introduced outerBound outerFree (inner previous)).symm

/-- weakened 变量替换保持非恒等替换复合。 -/
@[simp] theorem weakenBound_substituteMapped
    {σ : Signature.{u, v, w}}
    {source middleBound middleFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (inner : VariableSubstitution σ source middleBound middleFree) :
    (weakenBound introduced
        (fun {sort} (entry : Variable source sort) =>
          (inner entry).substituteMapped outerBound outerFree) :
      VariableSubstitution σ source (introduced :: targetBound) targetFree) =
      (fun {sort} (entry : Variable source sort) =>
        (weakenBound introduced inner entry).substituteMapped
          (liftBound introduced outerBound)
          (weakenBound introduced outerFree) :
        VariableSubstitution σ source (introduced :: targetBound) targetFree) := by
  funext sort entry
  exact (Term.substituteMapped_weakenBound introduced outerBound outerFree (inner entry)).symm

end VariableSubstitution

/-- 两次非恒等公式替换可合并为一次遍历。 -/
@[simp] theorem Formula.substituteMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (innerBound : VariableSubstitution σ sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution σ sourceFree middleBound middleFree) :
    (formula : Formula σ sourceBound sourceFree) →
      (formula.substituteMapped innerBound innerFree).substituteMapped
          outerBound outerFree =
        formula.substituteMapped
          (fun entry => (innerBound entry).substituteMapped
            outerBound outerFree)
          (fun entry => (innerFree entry).substituteMapped
            outerBound outerFree)
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments =>
      congrArg (Formula.rel relation)
        (Arguments.substituteMapped_comp outerBound outerFree innerBound innerFree arguments)
  | .equal left right =>
      congrArg₂ Formula.equal
        (Term.substituteMapped_comp outerBound outerFree innerBound innerFree left)
        (Term.substituteMapped_comp outerBound outerFree innerBound innerFree right)
  | .neg body => congrArg Formula.neg
      (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree body)
  | .conj left right =>
      congrArg₂ Formula.conj
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree right)
  | .disj left right =>
      congrArg₂ Formula.disj
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree right)
  | .imp left right =>
      congrArg₂ Formula.imp
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree right)
  | .iff left right =>
      congrArg₂ Formula.iff
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree left)
        (Formula.substituteMapped_comp outerBound outerFree innerBound innerFree right)
  | .forallE sort body => by
      apply congrArg (Formula.forallE sort)
      refine (Formula.substituteMapped_comp (VariableSubstitution.liftBound sort outerBound)
        (VariableSubstitution.weakenBound sort outerFree)
        (VariableSubstitution.liftBound sort innerBound)
        (VariableSubstitution.weakenBound sort innerFree) body).trans ?_
      apply Formula.substituteMapped_congr
      · intro resultSort entry
        cases entry with
        | here => rfl
        | there previous =>
            exact Term.substituteMapped_weakenBound sort outerBound outerFree (innerBound previous)
      · intro resultSort entry
        exact Term.substituteMapped_weakenBound sort outerBound outerFree (innerFree entry)
  | .existsE sort body => by
      apply congrArg (Formula.existsE sort)
      refine (Formula.substituteMapped_comp (VariableSubstitution.liftBound sort outerBound)
        (VariableSubstitution.weakenBound sort outerFree)
        (VariableSubstitution.liftBound sort innerBound)
        (VariableSubstitution.weakenBound sort innerFree) body).trans ?_
      apply Formula.substituteMapped_congr
      · intro resultSort entry
        cases entry with
        | here => rfl
        | there previous =>
            exact Term.substituteMapped_weakenBound sort outerBound outerFree (innerBound previous)
      · intro resultSort entry
        exact Term.substituteMapped_weakenBound sort outerBound outerFree (innerFree entry)

/-- 连续公式替换先复合变量像，因此只需一次 AST 遍历。 -/
@[simp] theorem Formula.substitute_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree)
    (formula : Formula σ sourceBound sourceFree) :
    (formula.substitute inner).substitute outer =
      formula.substitute (Substitution.comp outer inner) := by
  cases outer with
  | id => rfl
  | map outerBound outerFree =>
      cases inner with
      | id => rfl
      | map innerBound innerFree =>
          exact Formula.substituteMapped_comp outerBound outerFree innerBound innerFree formula

namespace Substitution

/-- binder 提升保持替换复合，组合节点不会在量词下重新展开成两次遍历。 -/
@[simp] theorem liftBound_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (introduced : σ.SortSymbol)
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree) :
    liftBound introduced (comp outer inner) =
      comp (liftBound introduced outer) (liftBound introduced inner) := by
  cases outer with
  | id => rfl
  | map outerBound outerFree =>
      cases inner with
      | id => rfl
      | map innerBound innerFree =>
          exact congrArg₂ Substitution.map
            (VariableSubstitution.liftBound_substituteMapped introduced outerBound outerFree innerBound)
            (VariableSubstitution.weakenBound_substituteMapped introduced outerBound outerFree innerFree)

/-- 恒等替换穿过 binder 后仍由同一个 `.id` 构造子表示。 -/
@[simp] theorem liftBound_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    liftBound introduced
        (Substitution.id : Substitution σ bound free bound free) =
      (Substitution.id :
        Substitution σ (introduced :: bound) free
          (introduced :: bound) free) :=
  rfl

/-- 顶部 free 实例化穿过 binder 时保持捆绑替换形态。 -/
@[simp] theorem liftBound_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (replacement : Term σ bound free sort) :
    liftBound introduced (instantiateFreeTop replacement) =
      instantiateFreeTop (replacement.weakenBound introduced) := by
  exact congrArg₂ Substitution.map
    (VariableSubstitution.liftBound_boundId introduced)
    (VariableSubstitution.weakenBound_instantiateFreeTop introduced replacement)

end Substitution

/-- 项上的恒等替换在根节点命中快路径。 -/
@[simp] theorem Term.substitute_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    term.substitute Substitution.id = term :=
  rfl

/-- 参数列上的恒等替换在根节点命中快路径。 -/
@[simp] theorem Arguments.substitute_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    arguments.substitute Substitution.id = arguments :=
  rfl

/-- 公式上的恒等替换在根节点命中快路径。 -/
@[simp] theorem Formula.substitute_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (formula : Formula σ bound free) :
    formula.substitute Substitution.id = formula :=
  rfl

mutual

/-- 非恒等执行器对 weakened 旧项实例化顶部 free 变量时恢复原项。 -/
@[simp] theorem Term.substituteMapped_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced) :
    {sort : σ.SortSymbol} → (term : Term σ bound free sort) →
      (term.weakenFree introduced).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.instantiateFreeTop replacement) = term
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments =>
      congrArg (Term.app function)
        (Arguments.substituteMapped_weakenFree_instantiateFreeTop introduced replacement arguments)

/-- 非恒等执行器对 weakened 旧参数列实例化顶部 free 变量时恢复原参数列。 -/
@[simp] theorem Arguments.substituteMapped_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound free sorts) →
        (arguments.weakenFree introduced).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.instantiateFreeTop replacement) = arguments
  | _, .nil => rfl
  | _, .cons term rest =>
      congrArg₂ Arguments.cons
        (Term.substituteMapped_weakenFree_instantiateFreeTop introduced replacement term)
        (Arguments.substituteMapped_weakenFree_instantiateFreeTop introduced replacement rest)

end

/-- 公共替换入口对 weakened 旧项实例化顶部 free 变量时恢复原项。 -/
@[simp] theorem Term.substitute_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced)
    {sort : σ.SortSymbol} (term : Term σ bound free sort) :
    (term.weakenFree introduced).substitute
        (Substitution.instantiateFreeTop replacement) = term := by
  exact Term.substituteMapped_weakenFree_instantiateFreeTop introduced replacement term

/-- 公共替换入口对 weakened 旧参数列实例化顶部 free 变量时恢复原参数列。 -/
@[simp] theorem Arguments.substitute_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    (arguments.weakenFree introduced).substitute
        (Substitution.instantiateFreeTop replacement) = arguments := by
  exact Arguments.substituteMapped_weakenFree_instantiateFreeTop introduced replacement arguments


/--
规范新自由变量不出现在旧公式中，因此用任意同排序项实例化它都是严格空操作。
-/
@[simp] theorem Formula.instantiateFreeTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (formula : Formula σ bound free) →
      (replacement : Term σ bound free introduced) →
        (formula.weakenFree introduced).instantiateFreeTop replacement =
          formula := by
  intro formula
  induction formula with
  | falsum => intro replacement; rfl
  | truth => intro replacement; rfl
  | rel relation arguments =>
      intro replacement
      exact congrArg (Formula.rel relation)
        (Arguments.substituteMapped_weakenFree_instantiateFreeTop introduced replacement arguments)
  | equal left right =>
      intro replacement
      exact congrArg₂ Formula.equal
        (Term.substituteMapped_weakenFree_instantiateFreeTop introduced replacement left)
        (Term.substituteMapped_weakenFree_instantiateFreeTop introduced replacement right)
  | neg body ih => intro replacement; exact congrArg Formula.neg (ih replacement)
  | conj left right ihLeft ihRight =>
      intro replacement
      exact congrArg₂ Formula.conj (ihLeft replacement) (ihRight replacement)
  | disj left right ihLeft ihRight =>
      intro replacement
      exact congrArg₂ Formula.disj (ihLeft replacement) (ihRight replacement)
  | imp left right ihLeft ihRight =>
      intro replacement
      exact congrArg₂ Formula.imp (ihLeft replacement) (ihRight replacement)
  | iff left right ihLeft ihRight =>
      intro replacement
      exact congrArg₂ Formula.iff (ihLeft replacement) (ihRight replacement)
  | forallE sort body ih =>
      intro replacement
      rw [Formula.weakenFree_forallE]
      apply congrArg (Formula.forallE sort)
      refine Eq.trans ?_ (ih (replacement.weakenBound sort))
      apply Formula.substituteMapped_congr
      · intro resultSort entry; cases entry <;> rfl
      · intro resultSort entry; cases entry <;> rfl
  | existsE sort body ih =>
      intro replacement
      rw [Formula.weakenFree_existsE]
      apply congrArg (Formula.existsE sort)
      refine Eq.trans ?_ (ih (replacement.weakenBound sort))
      apply Formula.substituteMapped_congr
      · intro resultSort entry; cases entry <;> rfl
      · intro resultSort entry; cases entry <;> rfl

/-- 非恒等执行器对 weakened 旧公式实例化顶部 free 变量时恢复原公式。 -/
@[simp] theorem Formula.substituteMapped_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced)
    (formula : Formula σ bound free) :
    (formula.weakenFree introduced).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.instantiateFreeTop replacement) = formula := by
  change (formula.weakenFree introduced).instantiateFreeTop replacement =
    formula
  exact Formula.instantiateFreeTop_weakenFree introduced formula replacement

/-!
## 结构化新鲜性

free 上下文扩展本身就是新鲜性证书：旧对象通过 `weakenFree` 嵌入，新变量由
`newestFree` 唯一表示。以下定律说明可计算 strengthening 精确恢复这种嵌入。
-/

/-- 规范新自由变量不能降回扩展前的上下文。 -/
@[simp] theorem Term.strengthenFreeTop?_newestFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol) :
    Term.strengthenFreeTop? sort
        (Term.newestFree (σ := σ) (bound := bound) (free := free) sort) =
      none :=
  rfl

mutual

/-- 项穿过新 free 变量后，strengthening 精确恢复原项。 -/
@[simp] theorem Term.strengthenFreeTop?_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sort : σ.SortSymbol} → (term : Term σ bound free sort) →
      (term.weakenFree introduced).strengthenFreeTop? introduced = some term
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments => by
      change (match (arguments.weakenFree introduced).strengthenFreeTop? introduced with
        | some reduced => some (Term.app function reduced)
        | none => none) = some (Term.app function arguments)
      rw [Arguments.strengthenFreeTop?_weakenFree introduced arguments]

/-- 参数列穿过新 free 变量后，strengthening 精确恢复原参数列。 -/
@[simp] theorem Arguments.strengthenFreeTop?_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound free sorts) →
        (arguments.weakenFree introduced).strengthenFreeTop? introduced =
          some arguments
  | _, .nil => rfl
  | _, .cons term rest => by
      change (match (term.weakenFree introduced).strengthenFreeTop? introduced with
        | none => none
        | some reducedTerm =>
            match (rest.weakenFree introduced).strengthenFreeTop? introduced with
            | none => none
            | some reducedRest => some (Arguments.cons reducedTerm reducedRest)) =
        some (Arguments.cons term rest)
      rw [Term.strengthenFreeTop?_weakenFree introduced term,
        Arguments.strengthenFreeTop?_weakenFree introduced rest]

end


/-- 公式穿过新 free 变量后，strengthening 精确恢复原公式。 -/
@[simp] theorem Formula.strengthenFreeTop?_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (formula : Formula σ bound free) →
      (formula.weakenFree introduced).strengthenFreeTop? introduced =
        some formula := by
  intro formula
  induction formula with
  | falsum => rfl
  | truth => rfl
  | rel relation arguments =>
      change ((arguments.weakenFree introduced).strengthenFreeTop? introduced).map
        (Formula.rel relation) = _
      rw [Arguments.strengthenFreeTop?_weakenFree introduced arguments]
      rfl
  | equal left right =>
      change ((left.weakenFree introduced).strengthenFreeTop? introduced).bind
        (fun l => ((right.weakenFree introduced).strengthenFreeTop? introduced).map
          (Formula.equal l)) = _
      rw [Term.strengthenFreeTop?_weakenFree introduced left,
        Term.strengthenFreeTop?_weakenFree introduced right]
      rfl
  | neg body ih =>
      change ((body.weakenFree introduced).strengthenFreeTop? introduced).map Formula.neg = _
      rw [ih]; rfl
  | conj left right ihLeft ihRight =>
      change ((left.weakenFree introduced).strengthenFreeTop? introduced).bind
        (fun l => ((right.weakenFree introduced).strengthenFreeTop? introduced).map
          (Formula.conj l)) = _
      rw [ihLeft, ihRight]; rfl
  | disj left right ihLeft ihRight =>
      change ((left.weakenFree introduced).strengthenFreeTop? introduced).bind
        (fun l => ((right.weakenFree introduced).strengthenFreeTop? introduced).map
          (Formula.disj l)) = _
      rw [ihLeft, ihRight]; rfl
  | imp left right ihLeft ihRight =>
      change ((left.weakenFree introduced).strengthenFreeTop? introduced).bind
        (fun l => ((right.weakenFree introduced).strengthenFreeTop? introduced).map
          (Formula.imp l)) = _
      rw [ihLeft, ihRight]; rfl
  | iff left right ihLeft ihRight =>
      change ((left.weakenFree introduced).strengthenFreeTop? introduced).bind
        (fun l => ((right.weakenFree introduced).strengthenFreeTop? introduced).map
          (Formula.iff l)) = _
      rw [ihLeft, ihRight]; rfl
  | forallE sort body ih =>
      rw [Formula.weakenFree_forallE]
      change ((body.weakenFree introduced).strengthenFreeTop? introduced).map
        (Formula.forallE sort) = _
      rw [ih]; rfl
  | existsE sort body ih =>
      rw [Formula.weakenFree_existsE]
      change ((body.weakenFree introduced).strengthenFreeTop? introduced).map
        (Formula.existsE sort) = _
      rw [ih]; rfl

mutual

/-- 项 strengthening 成功时，其结果重新 weakening 后等于原项。 -/
theorem Term.weakenFree_of_strengthenFreeTop?_eq_some
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sort : σ.SortSymbol} →
      (expanded : Term σ bound (introduced :: free) sort) →
      (strengthened : Term σ bound free sort) →
      expanded.strengthenFreeTop? introduced = some strengthened →
        strengthened.weakenFree introduced = expanded
  | _, .bvar entry, strengthened, h => by
      cases h
      rfl
  | _, .fvar .here, _, h => by cases h
  | _, .fvar (.there entry), strengthened, h => by
      cases h
      rfl
  | _, .app function arguments, strengthened, h => by
      change (match arguments.strengthenFreeTop? introduced with
        | some reduced => some (Term.app function reduced)
        | none => none) = some strengthened at h
      cases hArguments : arguments.strengthenFreeTop? introduced with
      | none => rw [hArguments] at h; cases h
      | some reducedArguments =>
          rw [hArguments] at h
          cases h
          exact congrArg (Term.app function)
            (Arguments.weakenFree_of_strengthenFreeTop?_eq_some
              introduced arguments reducedArguments hArguments)

/-- 参数列 strengthening 成功时，其结果重新 weakening 后等于原参数列。 -/
theorem Arguments.weakenFree_of_strengthenFreeTop?_eq_some
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sorts : List σ.SortSymbol} →
      (expanded : Arguments σ bound (introduced :: free) sorts) →
      (strengthened : Arguments σ bound free sorts) →
      expanded.strengthenFreeTop? introduced = some strengthened →
        strengthened.weakenFree introduced = expanded
  | _, .nil, strengthened, h => by
      cases h
      rfl
  | _, .cons term rest, strengthened, h => by
      change (match term.strengthenFreeTop? introduced with
        | none => none
        | some reducedTerm =>
            match rest.strengthenFreeTop? introduced with
            | none => none
            | some reducedRest => some (Arguments.cons reducedTerm reducedRest)) =
        some strengthened at h
      cases hTerm : term.strengthenFreeTop? introduced with
      | none => rw [hTerm] at h; cases h
      | some reducedTerm =>
          rw [hTerm] at h
          cases hRest : rest.strengthenFreeTop? introduced with
          | none => rw [hRest] at h; cases h
          | some reducedRest =>
              rw [hRest] at h
              cases h
              exact congrArg₂ Arguments.cons
                (Term.weakenFree_of_strengthenFreeTop?_eq_some
                  introduced term reducedTerm hTerm)
                (Arguments.weakenFree_of_strengthenFreeTop?_eq_some
                  introduced rest reducedRest hRest)

end


private theorem Formula.weakenFree_of_strengthenFreeTopAux_eq_some
    {σ : Signature.{u, v, w}} {bound sourceFree : SortContext σ}
    (expanded : Formula σ bound sourceFree) :
    ∀ {introduced free} (hFree : sourceFree = introduced :: free)
      (strengthened : Formula σ bound free),
      expanded.strengthenFreeTopAux hFree = some strengthened →
        (hFree.symm ▸ strengthened.weakenFree introduced) = expanded := by
  induction expanded with
  | falsum => intro introduced free hFree strengthened h; cases hFree; cases h; rfl
  | truth => intro introduced free hFree strengthened h; cases hFree; cases h; rfl
  | rel relation arguments =>
      intro introduced free hFree strengthened h
      cases hFree
      change (arguments.strengthenFreeTop? introduced).map (Formula.rel relation) = some strengthened at h
      cases hArguments : arguments.strengthenFreeTop? introduced with
      | none => rw [hArguments] at h; cases h
      | some reduced =>
          rw [hArguments] at h
          cases h
          exact congrArg (Formula.rel relation)
            (Arguments.weakenFree_of_strengthenFreeTop?_eq_some introduced arguments reduced hArguments)
  | equal left right =>
      intro introduced free hFree strengthened h
      cases hFree
      change (left.strengthenFreeTop? introduced).bind
        (fun l => (right.strengthenFreeTop? introduced).map (Formula.equal l)) = some strengthened at h
      cases hLeft : left.strengthenFreeTop? introduced with
      | none => rw [hLeft] at h; cases h
      | some reducedLeft =>
          rw [hLeft] at h
          cases hRight : right.strengthenFreeTop? introduced with
          | none => rw [hRight] at h; cases h
          | some reducedRight =>
              rw [hRight] at h
              cases h
              exact congrArg₂ Formula.equal
                (Term.weakenFree_of_strengthenFreeTop?_eq_some introduced left reducedLeft hLeft)
                (Term.weakenFree_of_strengthenFreeTop?_eq_some introduced right reducedRight hRight)
  | neg body ih =>
      intro introduced free hFree strengthened h
      cases hFree
      change (body.strengthenFreeTop? introduced).map Formula.neg = some strengthened at h
      cases hBody : body.strengthenFreeTop? introduced with
      | none => rw [hBody] at h; cases h
      | some reduced =>
          rw [hBody] at h
          cases h
          exact congrArg Formula.neg (ih rfl reduced hBody)
  | conj left right ihLeft ihRight =>
      intro introduced free hFree strengthened h
      cases hFree
      change (left.strengthenFreeTop? introduced).bind
        (fun l => (right.strengthenFreeTop? introduced).map (Formula.conj l)) = some strengthened at h
      cases hLeft : left.strengthenFreeTop? introduced with
      | none => rw [hLeft] at h; cases h
      | some reducedLeft =>
          rw [hLeft] at h
          cases hRight : right.strengthenFreeTop? introduced with
          | none => rw [hRight] at h; cases h
          | some reducedRight =>
              rw [hRight] at h
              cases h
              exact congrArg₂ Formula.conj
                (ihLeft rfl reducedLeft hLeft) (ihRight rfl reducedRight hRight)
  | disj left right ihLeft ihRight =>
      intro introduced free hFree strengthened h
      cases hFree
      change (left.strengthenFreeTop? introduced).bind
        (fun l => (right.strengthenFreeTop? introduced).map (Formula.disj l)) = some strengthened at h
      cases hLeft : left.strengthenFreeTop? introduced with
      | none => rw [hLeft] at h; cases h
      | some reducedLeft =>
          rw [hLeft] at h
          cases hRight : right.strengthenFreeTop? introduced with
          | none => rw [hRight] at h; cases h
          | some reducedRight =>
              rw [hRight] at h
              cases h
              exact congrArg₂ Formula.disj
                (ihLeft rfl reducedLeft hLeft) (ihRight rfl reducedRight hRight)
  | imp left right ihLeft ihRight =>
      intro introduced free hFree strengthened h
      cases hFree
      change (left.strengthenFreeTop? introduced).bind
        (fun l => (right.strengthenFreeTop? introduced).map (Formula.imp l)) = some strengthened at h
      cases hLeft : left.strengthenFreeTop? introduced with
      | none => rw [hLeft] at h; cases h
      | some reducedLeft =>
          rw [hLeft] at h
          cases hRight : right.strengthenFreeTop? introduced with
          | none => rw [hRight] at h; cases h
          | some reducedRight =>
              rw [hRight] at h
              cases h
              exact congrArg₂ Formula.imp
                (ihLeft rfl reducedLeft hLeft) (ihRight rfl reducedRight hRight)
  | iff left right ihLeft ihRight =>
      intro introduced free hFree strengthened h
      cases hFree
      change (left.strengthenFreeTop? introduced).bind
        (fun l => (right.strengthenFreeTop? introduced).map (Formula.iff l)) = some strengthened at h
      cases hLeft : left.strengthenFreeTop? introduced with
      | none => rw [hLeft] at h; cases h
      | some reducedLeft =>
          rw [hLeft] at h
          cases hRight : right.strengthenFreeTop? introduced with
          | none => rw [hRight] at h; cases h
          | some reducedRight =>
              rw [hRight] at h
              cases h
              exact congrArg₂ Formula.iff
                (ihLeft rfl reducedLeft hLeft) (ihRight rfl reducedRight hRight)
  | forallE sort body ih =>
      intro introduced free hFree strengthened h
      cases hFree
      change (body.strengthenFreeTop? introduced).map (Formula.forallE sort) = some strengthened at h
      cases hBody : body.strengthenFreeTop? introduced with
      | none => rw [hBody] at h; cases h
      | some reduced =>
          rw [hBody] at h
          cases h
          rw [Formula.weakenFree_forallE]
          exact congrArg (Formula.forallE sort) (ih rfl reduced hBody)
  | existsE sort body ih =>
      intro introduced free hFree strengthened h
      cases hFree
      change (body.strengthenFreeTop? introduced).map (Formula.existsE sort) = some strengthened at h
      cases hBody : body.strengthenFreeTop? introduced with
      | none => rw [hBody] at h; cases h
      | some reduced =>
          rw [hBody] at h
          cases h
          rw [Formula.weakenFree_existsE]
          exact congrArg (Formula.existsE sort) (ih rfl reduced hBody)

/-- 公式 strengthening 成功时，其结果重新 weakening 后等于原公式。 -/
theorem Formula.weakenFree_of_strengthenFreeTop?_eq_some
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (expanded : Formula σ bound (introduced :: free)) →
    (strengthened : Formula σ bound free) →
    expanded.strengthenFreeTop? introduced = some strengthened →
      strengthened.weakenFree introduced = expanded := by
  intro expanded strengthened h
  exact Formula.weakenFree_of_strengthenFreeTopAux_eq_some expanded rfl strengthened h

end FirstOrder
end Logic
end YesMetaZFC
