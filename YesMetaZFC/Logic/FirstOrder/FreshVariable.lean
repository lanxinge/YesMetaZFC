import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-!
# 结构化自由变量新鲜性

新鲜变量不再通过扫描自然数编号获得。给 free 上下文头部加入一个排序后：

* `Term.newestFree` 是新引入的规范变量；
* 旧项与旧公式通过 `weakenFree` 嵌入扩展上下文；
* `strengthenFreeTop?` 可计算地区分规范新变量与所有旧对象。

因此本层没有支持上界、最大编号或“选择足够大编号”的证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FreshVariable

universe u v w

/-- 在 free 上下文头部引入的规范新变量。 -/
def newest {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol) :
    OpenTerm σ (sort :: free) sort :=
  Term.newestFree sort

/-- 将有限局部上下文整体嵌入一个 fresh 扩展。 -/
def extendContext {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol) :
    Context σ free → Context σ (sort :: free) :=
  List.map (Formula.weakenFree sort)

/-- 规范新变量不能来自旧 free 上下文。 -/
@[simp] theorem newest_not_strengthenable {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol) :
    (newest (σ := σ) (free := free) sort).strengthenFreeTop? sort = none :=
  rfl

/-- 旧公式进入 fresh 扩展后可由 strengthening 精确恢复。 -/
@[simp] theorem strengthen_weakened_formula {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (formula : OpenFormula σ free) :
    (formula.weakenFree sort).strengthenFreeTop? sort = some formula :=
  Formula.strengthenFreeTop?_weakenFree sort formula

/-- 整个旧上下文进入 fresh 扩展后可逐式恢复。 -/
theorem strengthen_extended_context {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (context : Context σ free) :
    (extendContext sort context).map
        (Formula.strengthenFreeTop? sort) =
      context.map some := by
  induction context with
  | nil =>
      rfl
  | cons formula rest ih =>
      simp [extendContext]

/-! ## 跨推导规则保持位置的持久新变量 -/

/-- 在上下文尾部加入一个在后续头部扩展下位置稳定的新变量。 -/
abbrev persistentContext {σ : Signature.{u, v, w}}
    (free : SortContext σ) (sort : σ.SortSymbol) :=
  free ++ [sort]

/-- 将旧 free 变量嵌入持久 fresh 扩展。 -/
def persistentRenaming {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol) :
    VariableRenaming free (persistentContext free sort) :=
  VariableRenaming.appendRight sort

/-- 持久 fresh 扩展中的末位新变量。 -/
def persistent {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol) :
    OpenTerm σ (persistentContext free sort) sort :=
  .fvar (Variable.last free sort)

/-- free 替换在源、目标两侧同步保留同一个持久新变量。 -/
def preservePersistent {σ : Signature.{u, v, w}}
    {source target : SortContext σ} (sort : σ.SortSymbol)
    (substitution : VariableSubstitution σ source []
      (persistentContext target sort)) :
    VariableSubstitution σ (persistentContext source sort) []
      (persistentContext target sort) :=
  match source with
  | [] =>
      fun entry =>
        match entry with
        | .here => persistent sort
  | _ :: _ =>
      fun entry =>
        match entry with
        | .here => substitution .here
        | .there previous =>
            preservePersistent sort
              (fun entry => substitution (.there entry)) previous

/-- 保留持久变量时，原上下文中的变量仍取给定项像。 -/
@[simp] theorem preservePersistent_appendRight
    {σ : Signature.{u, v, w}}
    {source target : SortContext σ} (sort : σ.SortSymbol)
    (substitution : VariableSubstitution σ source []
      (persistentContext target sort))
    {resultSort : σ.SortSymbol} (entry : Variable source resultSort) :
    preservePersistent sort substitution (Variable.appendRight sort entry) =
      substitution entry := by
  induction entry with
  | here =>
      rfl
  | there previous ih =>
      exact ih (substitution := fun entry => substitution (.there entry))

/-- 保留持久变量时，源上下文末位变量映到目标末位变量。 -/
@[simp] theorem preservePersistent_last
    {σ : Signature.{u, v, w}}
    {source target : SortContext σ} (sort : σ.SortSymbol)
    (substitution : VariableSubstitution σ source []
      (persistentContext target sort)) :
    preservePersistent sort substitution (Variable.last source sort) =
      persistent (σ := σ) (free := target) sort := by
  induction source with
  | nil =>
      rfl
  | cons _ tail ih =>
      exact ih (substitution := fun entry => substitution (.there entry))

/-- 普通 free 替换的两端同步加入持久新变量。 -/
def extendSubstitution {σ : Signature.{u, v, w}}
    {source target : SortContext σ} (sort : σ.SortSymbol)
    (substitution : VariableSubstitution σ source [] target) :
    VariableSubstitution σ (persistentContext source sort) []
      (persistentContext target sort) :=
  preservePersistent sort
    (fun entry =>
      (substitution entry).renameFree (persistentRenaming sort))

end FreshVariable

namespace VariableSubstitution

/-! ## bound 上下文尾槽的闭项实例化 -/

/--
删除 bound 上下文最右侧槽，并以 bound-closed 项替换它。局部 binder 只提升替换项，
因此该操作天然无捕获。
-/
def instantiateLastBound {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort) :
    VariableSubstitution σ (prefixContext ++ [sort]) prefixContext free :=
  match prefixContext with
  | [] => fun entry =>
      match entry with
      | .here => replacement
      | .there previous => nomatch previous
  | introduced :: rest => fun entry =>
      match entry with
      | .here => .bvar .here
      | .there previous =>
          (instantiateLastBound rest replacement previous).weakenBound introduced

@[simp] theorem instantiateLastBound_cons
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (introduced : σ.SortSymbol) (prefixContext : SortContext σ)
    {sort : σ.SortSymbol} (replacement : Term σ [] free sort) :
    (instantiateLastBound (introduced :: prefixContext) replacement :
      VariableSubstitution σ
        ((introduced :: prefixContext) ++ [sort])
        (introduced :: prefixContext) free) =
      (liftBound introduced
        (instantiateLastBound prefixContext replacement) :
        VariableSubstitution σ
          (introduced :: (prefixContext ++ [sort]))
          (introduced :: prefixContext) free) := by
  funext resultSort entry
  cases entry <;> rfl

/--
尾槽实例化在变量上只有两种结果：前缀变量保持原索引，唯一尾槽变为闭项在当前
前缀下的规范嵌入。
-/
theorem instantiateLastBound_bvar
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (prefixContext : SortContext σ) {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (entry : Variable (prefixContext ++ [sort]) resultSort) :
    (∃ target : Variable prefixContext resultSort,
      entry.index = target.index ∧
        instantiateLastBound prefixContext replacement entry =
          Term.bvar target) ∨
    (∃ hSort : resultSort = sort,
      entry.index = prefixContext.length ∧
        hSort ▸ instantiateLastBound prefixContext replacement entry =
          replacement.embedBoundClosed prefixContext) := by
  induction prefixContext generalizing resultSort with
  | nil =>
      cases entry with
      | here =>
          exact Or.inr ⟨rfl, rfl, rfl⟩
      | there previous => exact nomatch previous
  | cons introduced rest ih =>
      cases entry with
      | here =>
          exact Or.inl ⟨.here, rfl, rfl⟩
      | there previous =>
          rcases ih previous with
            ⟨target, hIndex, hTarget⟩ | ⟨hSort, hIndex, hTarget⟩
          · exact Or.inl ⟨.there target, by simp [Variable.index, hIndex], by
              simp [instantiateLastBound, hTarget]⟩
          · subst resultSort
            exact Or.inr ⟨rfl, by simp [Variable.index, hIndex], by
              simpa [instantiateLastBound, Term.embedBoundClosed] using
                congrArg (Term.weakenBound introduced) hTarget⟩

/-! ## bound 上下文尾槽的规范打开 -/

/-- 删除 bound 上下文最右侧槽，并把它转为规范 free 槽。 -/
def openLastBound {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol) :
    VariableSubstitution σ (prefixContext ++ [sort]) prefixContext
      (sort :: free) :=
  match prefixContext with
  | [] => fun entry =>
      match entry with
      | .here => .fvar .here
      | .there previous => nomatch previous
  | introduced :: rest => fun entry =>
      match entry with
      | .here => .bvar .here
      | .there previous =>
          (openLastBound rest sort previous).weakenBound introduced

@[simp] theorem openLastBound_single
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (introduced sort : σ.SortSymbol) :
    (openLastBound [introduced] sort :
      VariableSubstitution σ ([introduced] ++ [sort])
        [introduced] (sort :: free)) =
      (liftBound introduced
        (instantiateTop
          (FreshVariable.newest (σ := σ) (free := free) sort)) :
        VariableSubstitution σ ([introduced] ++ [sort])
          [introduced] (sort :: free)) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      cases previous with
      | here => rfl
      | there impossible => exact nomatch impossible

@[simp] theorem openLastBound_cons
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (introduced : σ.SortSymbol)
    (prefixContext : SortContext σ)
    (sort : σ.SortSymbol) :
    (openLastBound (introduced :: prefixContext) sort :
      VariableSubstitution σ
        ((introduced :: prefixContext) ++ [sort])
        (introduced :: prefixContext) (sort :: free)) =
      (liftBound introduced (openLastBound prefixContext sort) :
      VariableSubstitution σ
          (introduced :: (prefixContext ++ [sort]))
          (introduced :: prefixContext) (sort :: free)) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous => rfl

end VariableSubstitution

namespace Substitution

/-! ## bound 上下文尾槽的闭项实例化 -/

/-- 以 bound-closed 项实例化 bound 上下文最右侧槽。 -/
def instantiateLastBound {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort) :
    Substitution σ (prefixContext ++ [sort]) free prefixContext free :=
  .map (VariableSubstitution.instantiateLastBound prefixContext replacement)
    VariableSubstitution.freeId

/-! ## free 顶部变量向 bound 尾槽的规范抽象 -/

/--
把 free 上下文顶部变量抽象到 bound 上下文最右侧；既有局部 binder 的 de Bruijn
位置保持不变。
-/
def abstractFreeTopLast {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol) :
    Substitution σ prefixContext (sort :: free)
      (prefixContext ++ [sort]) free :=
  let boundSubstitution : VariableSubstitution σ prefixContext
      (prefixContext ++ [sort]) free :=
    fun entry => .bvar (Variable.appendRight sort entry)
  let freeSubstitution : VariableSubstitution σ (sort :: free)
      (prefixContext ++ [sort]) free :=
    fun {resultSort} entry =>
      match entry with
      | .here => .bvar (Variable.last prefixContext sort)
      | .there previous => .fvar previous
  .map boundSubstitution freeSubstitution

/-- 尾槽抽象穿过一个既有 binder，等于对抽象替换做一次 bound 提升。 -/
@[simp] theorem abstractFreeTopLast_cons
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (introduced : σ.SortSymbol)
    (prefixContext : SortContext σ) (sort : σ.SortSymbol) :
    (abstractFreeTopLast (introduced :: prefixContext) sort :
      Substitution σ (introduced :: prefixContext) (sort :: free)
        ((introduced :: prefixContext) ++ [sort]) free) =
      Substitution.liftBound introduced
        (abstractFreeTopLast prefixContext sort) := by
  change Substitution.map _ _ = Substitution.map _ _
  congr
  · funext resultSort entry
    cases entry <;> rfl
  · funext resultSort entry
    cases entry <;> rfl

end Substitution

namespace Term

/-! ## bound 上下文尾槽的闭项实例化 -/

/-- 以 bound-closed 项实例化项的最右侧 bound 槽。 -/
def instantiateLastBound {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (term : Term σ (prefixContext ++ [sort]) free resultSort) :
    Term σ prefixContext free resultSort :=
  term.substitute (Substitution.instantiateLastBound prefixContext replacement)

@[simp] theorem instantiateLastBound_nil
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    {sort resultSort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (term : Term σ [sort] free resultSort) :
    Term.instantiateLastBound [] replacement term =
      term.instantiateTop replacement :=
  by
    change term.substituteMapped _ _ = term.substituteMapped _ _
    apply congrArg (fun τ : VariableSubstitution σ [sort] [] free =>
      term.substituteMapped τ VariableSubstitution.freeId)
    funext currentSort entry
    cases entry with
    | here => rfl
    | there previous => exact nomatch previous

/-! ## free 顶部变量向 bound 尾槽的规范抽象 -/

/-- 把 free 顶部变量抽象到局部 binder 之后。 -/
def abstractFreeTopLast {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol)
    {resultSort : σ.SortSymbol}
    (term : Term σ prefixContext (sort :: free) resultSort) :
    Term σ (prefixContext ++ [sort]) free resultSort :=
  term.substitute (Substitution.abstractFreeTopLast prefixContext sort)

/-! ## bound 上下文尾槽的规范打开 -/

/-- 删除 bound 上下文最右侧槽，并把它转为规范 free 槽。 -/
def openBoundLast {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol)
    {resultSort : σ.SortSymbol}
    (term : Term σ (prefixContext ++ [sort]) free resultSort) :
    Term σ prefixContext (sort :: free) resultSort :=
  term.substituteMapped
    (VariableSubstitution.openLastBound prefixContext sort)
    (VariableSubstitution.of_renaming (VariableRenaming.weaken sort))

/-! ## bound 顶部打开 -/

/-- 把单个顶部 bound 槽打开为规范 fresh free 槽。 -/
def openBoundTop {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    {resultSort : σ.SortSymbol}
    (term : Term σ [sort] free resultSort) :
    OpenTerm σ (sort :: free) resultSort :=
  term.substituteMapped
    (VariableSubstitution.instantiateTop
      (FreshVariable.newest (σ := σ) (free := free) sort))
      (VariableSubstitution.of_renaming (σ := σ)
      (VariableRenaming.weaken sort))

theorem openBoundTop_eq_openBoundLast
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (sort : σ.SortSymbol)
    {resultSort : σ.SortSymbol}
    (term : Term σ [sort] free resultSort) :
    Term.openBoundTop sort term =
      Term.openBoundLast [] sort term := by
  change
    term.substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := σ) (free := free) sort))
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken sort)) =
      term.substituteMapped
        (VariableSubstitution.openLastBound [] sort)
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken sort))
  congr
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous => exact nomatch previous

@[simp] theorem openBoundLast_weakenBound
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (introduced : σ.SortSymbol)
    (prefixContext : SortContext σ)
    (sort : σ.SortSymbol)
    {resultSort : σ.SortSymbol}
    (term : Term σ (prefixContext ++ [sort]) free resultSort) :
    Term.openBoundLast (introduced :: prefixContext) sort
        (term.weakenBound introduced) =
      (Term.openBoundLast prefixContext sort term).weakenBound introduced := by
  simpa [Term.openBoundLast] using
    (Term.substituteMapped_weakenBound
      introduced
      (VariableSubstitution.openLastBound prefixContext sort)
      (VariableSubstitution.of_renaming
        (VariableRenaming.weaken sort)) term)

/-- 闭项先提升再打开，严格等于 free weakening。 -/
@[simp] theorem openBoundTop_weakenBound
    {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    {resultSort : σ.SortSymbol}
    (term : Term σ [] free resultSort) :
    Term.openBoundTop sort (term.weakenBound sort) =
      term.weakenFree sort := by

  change (term.renameMapped (VariableRenaming.weaken sort) VariableRenaming.id).substituteMapped
      (VariableSubstitution.instantiateTop (FreshVariable.newest (σ := σ) (free := free) sort))
      (VariableSubstitution.of_renaming (VariableRenaming.weaken sort)) =
    term.renameMapped VariableRenaming.id (VariableRenaming.weaken sort)
  rw [← Term.substituteMapped_of_bound_renaming, Term.substituteMapped_comp,
    ← Term.substituteMapped_of_renaming]
  rfl

end Term

namespace Arguments

/-! ## bound 上下文尾槽的闭项实例化 -/

/-- 以 bound-closed 项实例化参数列的最右侧 bound 槽。 -/
def instantiateLastBound {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort) {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (prefixContext ++ [sort]) free sorts) :
    Arguments σ prefixContext free sorts :=
  arguments.substitute
    (Substitution.instantiateLastBound prefixContext replacement)

@[simp] theorem instantiateLastBound_nil
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    {sort : σ.SortSymbol} (replacement : Term σ [] free sort)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ [sort] free sorts) :
    Arguments.instantiateLastBound [] replacement arguments =
      arguments.instantiateTop replacement :=
  by
    change arguments.substituteMapped _ _ =
      arguments.substituteMapped _ _
    apply congrArg (fun τ : VariableSubstitution σ [sort] [] free =>
      arguments.substituteMapped τ VariableSubstitution.freeId)
    funext currentSort entry
    cases entry with
    | here => rfl
    | there previous => exact nomatch previous

/-- bound 尾槽实例化与参数列排序索引的 transport 交换。 -/
@[simp] theorem instantiateLastBound_cast
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (prefixContext : SortContext σ) {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    {sourceSorts targetSorts : List σ.SortSymbol}
    (hSorts : sourceSorts = targetSorts)
    (arguments : Arguments σ (prefixContext ++ [sort]) free sourceSorts) :
    Arguments.instantiateLastBound prefixContext replacement
        (hSorts ▸ arguments) =
      hSorts ▸ Arguments.instantiateLastBound
        prefixContext replacement arguments := by
  cases hSorts
  rfl

/-! ## free 顶部变量向 bound 尾槽的规范抽象 -/

/-- 参数列逐项把 free 顶部变量抽象到局部 binder 之后。 -/
def abstractFreeTopLast {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ prefixContext (sort :: free) sorts) :
    Arguments σ (prefixContext ++ [sort]) free sorts :=
  arguments.substitute
    (Substitution.abstractFreeTopLast prefixContext sort)

/-- 尾槽抽象与参数列排序索引的 transport 交换。 -/
@[simp] theorem abstractFreeTopLast_cast
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol)
    {sourceSorts targetSorts : List σ.SortSymbol}
    (hSorts : sourceSorts = targetSorts)
    (arguments : Arguments σ prefixContext (sort :: free) sourceSorts) :
    (hSorts ▸ arguments).abstractFreeTopLast prefixContext sort =
      hSorts ▸ arguments.abstractFreeTopLast prefixContext sort := by
  cases hSorts
  rfl

end Arguments

namespace Formula

/-! ## bound 上下文尾槽的闭项实例化 -/

/-- 以 bound-closed 项实例化公式的最右侧 bound 槽。 -/
def instantiateLastBound {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort)
    (body : Formula σ (prefixContext ++ [sort]) free) :
    Formula σ prefixContext free :=
  body.substitute (Substitution.instantiateLastBound prefixContext replacement)

@[simp] theorem instantiateLastBound_nil
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    {sort : σ.SortSymbol} (replacement : Term σ [] free sort)
    (body : Formula σ [sort] free) :
    Formula.instantiateLastBound [] replacement body =
      Formula.instantiateTop replacement body :=
  by
    change body.substituteMapped _ _ = body.substituteMapped _ _
    apply congrArg (fun τ : VariableSubstitution σ [sort] [] free =>
      body.substituteMapped τ VariableSubstitution.freeId)
    funext currentSort entry
    cases entry with
    | here => rfl
    | there previous => exact nomatch previous

@[simp] theorem instantiateLastBound_forallE
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (prefixContext : SortContext σ) {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort) (quantified : σ.SortSymbol)
    (body : Formula σ
      (quantified :: (prefixContext ++ [sort])) free) :
    Formula.instantiateLastBound prefixContext replacement
        (Formula.forallE quantified body) =
      Formula.forallE quantified
        (Formula.instantiateLastBound
          (quantified :: prefixContext) replacement body) := by
  simp [Formula.instantiateLastBound, Substitution.instantiateLastBound,
    Formula.substitute, Formula.substituteMapped]

@[simp] theorem instantiateLastBound_existsE
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (prefixContext : SortContext σ) {sort : σ.SortSymbol}
    (replacement : Term σ [] free sort) (quantified : σ.SortSymbol)
    (body : Formula σ
      (quantified :: (prefixContext ++ [sort])) free) :
    Formula.instantiateLastBound prefixContext replacement
        (Formula.existsE quantified body) =
      Formula.existsE quantified
        (Formula.instantiateLastBound
          (quantified :: prefixContext) replacement body) := by
  simp [Formula.instantiateLastBound, Substitution.instantiateLastBound,
    Formula.substitute, Formula.substituteMapped]

/-! ## free 顶部变量向 bound 尾槽的规范抽象 -/

/-- 把 free 顶部变量抽象到所有局部 binder 之后。 -/
def abstractFreeTopLast {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol)
    (body : Formula σ prefixContext (sort :: free)) :
    Formula σ (prefixContext ++ [sort]) free :=
  body.substitute (Substitution.abstractFreeTopLast prefixContext sort)

/-- 根部没有局部 binder 时，尾槽抽象就是公共顶部抽象。 -/
@[simp] theorem abstractFreeTopLast_nil
    {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ [] (sort :: free)) :
    body.abstractFreeTopLast [] sort = body.abstractFreeTop := by
  change body.substituteMapped _ _ = body.substituteMapped _ _
  congr
  funext resultSort entry
  cases entry <;> rfl

/-! ## 最外层 binder 的规范打开 -/

/--
在保留当前顶部 binder 的同时，于其下插入一个新的 bound 槽。
这正是把一个量词体嵌入“外层参数模板”时所需的规范重命名。
-/
def weakenBoundUnderTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {top : σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (body : Formula σ (top :: bound) free) :
    Formula σ (top :: introduced :: bound) free :=
  body.renameMapped
    (VariableRenaming.lift (VariableRenaming.weaken introduced))
    VariableRenaming.id

/--
量词下插入的外层 bound 槽被实例化后严格消去；公式树只经一次复合替换。
-/
@[simp] theorem substituteMapped_liftBound_instantiateTop_weakenBoundUnderTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {top introduced : σ.SortSymbol}
    (replacement : Term σ bound free introduced)
    (body : Formula σ (top :: bound) free) :
    (body.weakenBoundUnderTop introduced).substituteMapped
        (VariableSubstitution.liftBound top
          (VariableSubstitution.instantiateTop replacement))
        VariableSubstitution.freeId = body := by
  change
    (body.renameMapped
        (VariableRenaming.lift
          (VariableRenaming.weaken introduced))
        VariableRenaming.id).substituteMapped
          (VariableSubstitution.liftBound top
            (VariableSubstitution.instantiateTop replacement))
          VariableSubstitution.freeId = body
  rw [← Formula.substituteMapped_of_bound_renaming]
  rw [Formula.substituteMapped_comp]
  have hBound :
      (fun {resultSort}
          (entry : Variable (top :: bound) resultSort) =>
        (VariableSubstitution.of_bound_renaming
          (free := free)
          (VariableRenaming.lift
            (VariableRenaming.weaken introduced)) entry).substituteMapped
              (VariableSubstitution.liftBound top
                (VariableSubstitution.instantiateTop replacement))
              VariableSubstitution.freeId) =
        (VariableSubstitution.boundId :
          VariableSubstitution σ (top :: bound)
            (top :: bound) free) := by
    funext resultSort entry
    cases entry <;> rfl
  have hFree :
      (fun {resultSort} (entry : Variable free resultSort) =>
        (VariableSubstitution.freeId entry).substituteMapped
          (VariableSubstitution.liftBound top
            (VariableSubstitution.instantiateTop replacement))
          VariableSubstitution.freeId) =
        (VariableSubstitution.freeId :
          VariableSubstitution σ free (top :: bound) free) := by
    funext resultSort entry
    rfl
  rw [hBound, hFree]
  exact Formula.substituteMapped_id body

/-- bound 顶部实例化与 free weakening 在公式层严格交换。 -/
@[simp] theorem instantiateTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {sort introduced : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (sort :: bound) free) :
    (body.weakenFree introduced).instantiateTop
        (replacement.weakenFree introduced) =
      (body.instantiateTop replacement).weakenFree introduced := by
  symm
  simpa only [
    VariableSubstitution.weakenBound_of_renaming,
    Formula.substituteMapped_of_renaming,
    Term.substituteMapped_of_renaming,
    Formula.weakenFree_eq_renameMapped,
    Term.weakenFree, Term.rename,
    Renaming.weakenFree, Renaming.free] using
    (Formula.substituteMapped_instantiateTop_boundId
      (VariableSubstitution.of_renaming (bound := bound)
        (VariableRenaming.weaken introduced))
      replacement body)

/-- 删除 bound 上下文最右侧槽，并把它转为规范 free 槽。 -/
def openBoundLast {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ) (sort : σ.SortSymbol)
    (body : Formula σ (prefixContext ++ [sort]) free) :
    Formula σ prefixContext (sort :: free) :=
  body.substituteMapped
    (VariableSubstitution.openLastBound prefixContext sort)
    (VariableSubstitution.of_renaming (VariableRenaming.weaken sort))

/--
把闭合于最外层 binder 的公式体直接打开为 free 上下文顶部的规范新变量。该实现把
bound 实例化与旧 free 变量嵌入合并为一次公式遍历。
-/
def openBoundTop {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ [sort] free) :
    OpenFormula σ (sort :: free) :=
  body.substituteMapped
    (VariableSubstitution.instantiateTop
      (FreshVariable.newest (σ := σ) (free := free) sort))
      (VariableSubstitution.of_renaming (σ := σ) (bound := [])
      (VariableRenaming.weaken sort))

/-- 规范打开等于先嵌入 fresh 上下文，再以最新变量实例化。 -/
theorem openBoundTop_eq_instantiateTop_weakenFree
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (sort : σ.SortSymbol)
    (body : Formula σ [sort] free) :
    Formula.openBoundTop sort body =
      Formula.instantiateTop
        (FreshVariable.newest (σ := σ) (free := free) sort)
        (body.weakenFree sort) := by
  change
    body.substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := σ) (free := free) sort))
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken sort)) =
      (body.renameMapped VariableRenaming.id
        (VariableRenaming.weaken sort)).substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := σ) (free := free) sort))
        VariableSubstitution.freeId
  rw [← Formula.substituteMapped_of_renaming]
  rw [Formula.substituteMapped_comp]
  congr

theorem openBoundTop_eq_openBoundLast
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (sort : σ.SortSymbol)
    (body : Formula σ [sort] free) :
    Formula.openBoundTop sort body =
      Formula.openBoundLast [] sort body := by
  change
    body.substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := σ) (free := free) sort))
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken sort)) =
      body.substituteMapped
        (VariableSubstitution.openLastBound [] sort)
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken sort))
  congr
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous => exact nomatch previous

@[simp] theorem openBoundLast_existsE
    {σ : Signature.{u, v, w}}
    {free : SortContext σ}
    (prefixContext : SortContext σ)
    (sort quantified : σ.SortSymbol)
    (body : Formula σ (quantified :: (prefixContext ++ [sort])) free) :
    Formula.openBoundLast prefixContext sort
        (Formula.existsE quantified body) =
      Formula.existsE quantified
        (Formula.openBoundLast (quantified :: prefixContext) sort body) := by
  change
    Formula.existsE quantified
        (body.substituteMapped
          (VariableSubstitution.liftBound quantified
            (VariableSubstitution.openLastBound prefixContext sort))
          (VariableSubstitution.weakenBound quantified
            (VariableSubstitution.of_renaming
              (VariableRenaming.weaken sort)))) =
      Formula.existsE quantified
        (body.substituteMapped
          (VariableSubstitution.openLastBound (quantified :: prefixContext) sort)
          (VariableSubstitution.of_renaming
            (VariableRenaming.weaken sort)))
  rw [VariableSubstitution.openLastBound_cons,
    VariableSubstitution.weakenBound_of_renaming]

/-- 规范打开后的顶部 free 变量重新抽象时严格恢复原量词体。 -/
@[simp] theorem abstractFreeTop_openBoundTop
    {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ [sort] free) :
    (body.openBoundTop sort).abstractFreeTop = body := by
  change
    (body.substituteMapped
      (VariableSubstitution.instantiateTop
        (FreshVariable.newest (σ := σ) (free := free) sort))
      (VariableSubstitution.of_renaming (σ := σ) (bound := [])
        (VariableRenaming.weaken sort))).substituteMapped
          (VariableSubstitution.abstractBound (σ := σ) sort)
          (VariableSubstitution.abstractFreeTop (σ := σ)) = body
  rw [Formula.substituteMapped_comp]
  have hBound :
      (fun {resultSort} (entry : Variable [sort] resultSort) =>
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := σ) (free := free) sort)
          entry).substituteMapped
            (VariableSubstitution.abstractBound (σ := σ) sort)
            (VariableSubstitution.abstractFreeTop (σ := σ))) =
        (VariableSubstitution.boundId :
          VariableSubstitution σ [sort] [sort] free) := by
    funext resultSort entry
    cases entry with
    | here => rfl
    | there previous => exact nomatch previous
  have hFree :
      (fun {resultSort} (entry : Variable free resultSort) =>
        (VariableSubstitution.of_renaming (σ := σ) (bound := [])
          (VariableRenaming.weaken sort) entry).substituteMapped
            (VariableSubstitution.abstractBound (σ := σ) sort)
            (VariableSubstitution.abstractFreeTop (σ := σ))) =
        (VariableSubstitution.freeId :
          VariableSubstitution σ free [sort] free) := by
    funext resultSort entry
    cases entry <;> rfl
  calc
    body.substituteMapped
        (fun entry =>
          (VariableSubstitution.instantiateTop
            (FreshVariable.newest (σ := σ) (free := free) sort)
            entry).substituteMapped
              (VariableSubstitution.abstractBound (σ := σ) sort)
              (VariableSubstitution.abstractFreeTop (σ := σ)))
        (fun entry =>
          (VariableSubstitution.of_renaming (σ := σ) (bound := [])
            (VariableRenaming.weaken sort) entry).substituteMapped
              (VariableSubstitution.abstractBound (σ := σ) sort)
              (VariableSubstitution.abstractFreeTop (σ := σ))) =
      body.substituteMapped VariableSubstitution.boundId
        VariableSubstitution.freeId := by
      rw [hBound, hFree]
    _ = body := Formula.substituteMapped_id body

/-- 规范打开后重新全称封闭，严格恢复原全称式。 -/
@[simp] theorem forallFreeTop_openBoundTop
    {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ [sort] free) :
    (body.openBoundTop sort).forallFreeTop sort =
      (.forallE sort body : OpenFormula σ free) := by
  simp [Formula.forallFreeTop]

/-- 规范打开后重新存在封闭，严格恢复原存在式。 -/
@[simp] theorem existsFreeTop_openBoundTop
    {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ [sort] free) :
    (body.openBoundTop sort).existsFreeTop sort =
      (.existsE sort body : OpenFormula σ free) := by
  simp [Formula.existsFreeTop]

end Formula

end FirstOrder
end Logic
end YesMetaZFC
