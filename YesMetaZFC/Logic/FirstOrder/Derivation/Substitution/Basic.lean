import YesMetaZFC.Logic.FirstOrder.Context.Basic

/-!
# 类型化 free 替换

本模块不再实现第二套按自然数编号递归的替换器。free 替换被表示为源 free 上下文到
目标语法中的保排序项映射，再统一交给语法核的 `Substitution` 执行。

替换项的排序、作用域与终止性全部由类型保证，因此不存在 `BoundClosed`、
well-sorted 或 admissible 前提。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace VariableSubstitution

/-- 将保排序 free 重命名视为项值替换。 -/
def of_renaming {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree) :
    VariableSubstitution σ sourceFree bound targetFree :=
  fun entry => .fvar (ρ entry)

end VariableSubstitution

namespace Substitution

/-- 只替换 free 变量并保持 bound 上下文。 -/
def free_map {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (freeSubstitution :
      VariableSubstitution σ sourceFree bound targetFree) :
    Substitution σ bound sourceFree bound targetFree :=
  .map VariableSubstitution.boundId freeSubstitution

end Substitution

namespace Term

/-- 按类型化上下文映射替换项中的全部 free 变量。 -/
def substituteFree {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (freeSubstitution :
      VariableSubstitution σ sourceFree bound targetFree)
    {sort : σ.SortSymbol}
    (term : Term σ bound sourceFree sort) :
    Term σ bound targetFree sort :=
  term.substitute (Substitution.free_map freeSubstitution)

end Term

namespace Arguments

/-- 按类型化上下文映射替换异质参数列中的全部 free 变量。 -/
def substituteFree {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (freeSubstitution :
      VariableSubstitution σ sourceFree bound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound sourceFree sorts) :
    Arguments σ bound targetFree sorts :=
  arguments.substitute (Substitution.free_map freeSubstitution)

end Arguments

namespace Formula

/-- 按类型化上下文映射替换公式中的全部 free 变量。 -/
def substituteFree {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (freeSubstitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (formula : Formula σ bound sourceFree) :
    Formula σ bound targetFree :=
  formula.substitute (Substitution.free_map freeSubstitution)

end Formula

@[simp] theorem VariableSubstitution.weakenBound_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (ρ : VariableRenaming sourceFree targetFree) :
    (VariableSubstitution.weakenBound introduced
        (VariableSubstitution.of_renaming (bound := bound) ρ) :
      VariableSubstitution σ sourceFree
        (introduced :: bound) targetFree) =
      (VariableSubstitution.of_renaming
        (bound := introduced :: bound) ρ :
      VariableSubstitution σ sourceFree
        (introduced :: bound) targetFree) := by
  funext sort entry
  simp [VariableSubstitution.weakenBound,
    VariableSubstitution.of_renaming, Term.weakenBound,
    Term.rename, Renaming.weakenBound, Renaming.bound,
    Term.renameMapped, VariableRenaming.id]

/-- free 重命名替换穿过规范新变量后仍保持重命名规范形。 -/
@[simp] theorem VariableSubstitution.liftFree_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (ρ : VariableRenaming sourceFree targetFree) :
    (VariableSubstitution.liftFree introduced
      (VariableSubstitution.of_renaming (bound := bound) ρ) :
        VariableSubstitution σ (introduced :: sourceFree) bound
          (introduced :: targetFree)) =
      (VariableSubstitution.of_renaming (bound := bound)
        (VariableRenaming.lift (introduced := introduced) ρ) :
        VariableSubstitution σ (introduced :: sourceFree) bound
          (introduced :: targetFree)) := by
  funext resultSort entry
  cases entry <;> rfl

mutual

/-- 映射替换中的 free 重命名与底层专用重命名递归一致。 -/
@[simp] theorem Term.substituteMapped_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {sort : σ.SortSymbol} (term : Term σ bound sourceFree sort) :
    term.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.of_renaming ρ) =
      term.renameMapped VariableRenaming.id ρ := by
  cases term with
  | bvar entry =>
      rfl
  | fvar entry =>
      rfl
  | app function arguments =>
      simp [Term.substituteMapped, Term.renameMapped,
        Arguments.substituteMapped_of_renaming]

/-- 异质参数列上的映射替换与重命名递归一致。 -/
@[simp] theorem Arguments.substituteMapped_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound sourceFree sorts) :
    arguments.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.of_renaming ρ) =
      arguments.renameMapped VariableRenaming.id ρ := by
  cases arguments with
  | nil =>
      rfl
  | cons term rest =>
      simp [Arguments.substituteMapped, Arguments.renameMapped,
        Term.substituteMapped_of_renaming,
        Arguments.substituteMapped_of_renaming]

end

/-- 公式上的映射替换与 free 重命名递归一致。 -/
@[simp] theorem Formula.substituteMapped_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree) :
    (formula : Formula σ bound sourceFree) →
      formula.substituteMapped VariableSubstitution.boundId
          (VariableSubstitution.of_renaming ρ) =
        formula.renameMapped VariableRenaming.id ρ
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments => by
      simp [Formula.substituteMapped, Formula.renameMapped]
  | .equal left right => by
      simp [Formula.substituteMapped, Formula.renameMapped]
  | .neg body => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_renaming]
  | .conj left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_renaming]
  | .disj left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_renaming]
  | .imp left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_renaming]
  | .iff left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_renaming]
  | .forallE sort body => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_renaming]
  | .existsE sort body => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_renaming]

namespace VariableSubstitution

/-- 将保排序 bound 重命名视为 bound 项值替换。 -/
def of_bound_renaming {σ : Signature.{u, v, w}}
    {sourceBound targetBound free : SortContext σ}
    (ρ : VariableRenaming sourceBound targetBound) :
    VariableSubstitution σ sourceBound targetBound free :=
  fun entry => .bvar (ρ entry)

/-- bound 重命名替换穿过一个新 binder 后仍保持重命名规范形。 -/
@[simp] theorem liftBound_of_bound_renaming
    {σ : Signature.{u, v, w}}
    {sourceBound targetBound free : SortContext σ}
    (introduced : σ.SortSymbol)
    (ρ : VariableRenaming sourceBound targetBound) :
    (liftBound introduced (of_bound_renaming (free := free) ρ) :
      VariableSubstitution σ (introduced :: sourceBound)
        (introduced :: targetBound) free) =
      (of_bound_renaming (free := free)
        (VariableRenaming.lift (introduced := introduced) ρ) :
      VariableSubstitution σ (introduced :: sourceBound)
        (introduced :: targetBound) free) := by
  funext resultSort entry
  cases entry <;> rfl

end VariableSubstitution

mutual

/-- bound 重命名经项替换执行与专用重命名路径一致。 -/
@[simp] theorem Term.substituteMapped_of_bound_renaming
    {σ : Signature.{u, v, w}}
    {sourceBound targetBound free : SortContext σ}
    (ρ : VariableRenaming sourceBound targetBound)
    {sort : σ.SortSymbol} :
    (term : Term σ sourceBound free sort) →
      term.substituteMapped
          (VariableSubstitution.of_bound_renaming (free := free) ρ)
          VariableSubstitution.freeId =
        term.renameMapped ρ VariableRenaming.id
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app function arguments => by
      simp [Term.substituteMapped, Term.renameMapped,
        Arguments.substituteMapped_of_bound_renaming]

/-- bound 重命名经参数列替换执行与专用重命名路径一致。 -/
@[simp] theorem Arguments.substituteMapped_of_bound_renaming
    {σ : Signature.{u, v, w}}
    {sourceBound targetBound free : SortContext σ}
    (ρ : VariableRenaming sourceBound targetBound)
    {sorts : List σ.SortSymbol} :
    (arguments : Arguments σ sourceBound free sorts) →
      arguments.substituteMapped
          (VariableSubstitution.of_bound_renaming (free := free) ρ)
          VariableSubstitution.freeId =
        arguments.renameMapped ρ VariableRenaming.id
  | .nil => rfl
  | .cons head tail => by
      simp [Arguments.substituteMapped, Arguments.renameMapped,
        Term.substituteMapped_of_bound_renaming,
        Arguments.substituteMapped_of_bound_renaming]

end


/-- bound 重命名经公式替换执行与专用重命名路径一致。 -/
@[simp] theorem Formula.substituteMapped_of_bound_renaming
    {σ : Signature.{u, v, w}}
    {sourceBound targetBound free : SortContext σ}
    (ρ : VariableRenaming sourceBound targetBound) :
    (formula : Formula σ sourceBound free) →
      formula.substituteMapped
          (VariableSubstitution.of_bound_renaming (free := free) ρ)
          VariableSubstitution.freeId =
        formula.renameMapped ρ VariableRenaming.id
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments => by
      simp [Formula.substituteMapped, Formula.renameMapped]
  | .equal left right => by
      simp [Formula.substituteMapped, Formula.renameMapped]
  | .neg body => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_bound_renaming]
  | .conj left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_bound_renaming]
  | .disj left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_bound_renaming]
  | .imp left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_bound_renaming]
  | .iff left right => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_bound_renaming]
  | .forallE sort body => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_bound_renaming]
  | .existsE sort body => by
      simp [Formula.substituteMapped, Formula.renameMapped,
        Formula.substituteMapped_of_bound_renaming]

mutual

/-- 刚弱化出的顶部 free 槽未被使用，后续重命名可直接丢弃其像。 -/
@[simp] theorem Term.renameMapped_weakenFree_cons
    {σ : Signature.{u, v, w}}
    {bound free targetBound targetFree : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (boundRenaming : VariableRenaming bound targetBound)
    (head : Variable targetFree introduced)
    (tail : VariableRenaming free targetFree) :
    (term : Term σ bound free resultSort) →
      (term.weakenFree introduced).renameMapped boundRenaming
          (VariableRenaming.cons head tail) =
        term.renameMapped boundRenaming tail
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app function arguments => by
      simp [Term.renameMapped,
        Arguments.renameMapped_weakenFree_cons]

/-- free weakening 后沿 lifted 重命名继续映射，等于先映射再 weakening。 -/
@[simp] theorem Term.renameMapped_weakenFree_lift
    {σ : Signature.{u, v, w}}
    {bound free targetBound targetFree : SortContext σ}
    {introduced resultSort : σ.SortSymbol}
    (boundRenaming : VariableRenaming bound targetBound)
    (freeRenaming : VariableRenaming free targetFree)
    (term : Term σ bound free resultSort) :
    (term.weakenFree introduced).renameMapped boundRenaming
        (VariableRenaming.lift (introduced := introduced) freeRenaming) =
      (term.renameMapped boundRenaming freeRenaming).weakenFree introduced := by
  change
    (term.renameMapped VariableRenaming.id
      (VariableRenaming.weaken introduced)).renameMapped
        boundRenaming
        (VariableRenaming.lift (introduced := introduced) freeRenaming) =
      (term.renameMapped boundRenaming freeRenaming).renameMapped
        VariableRenaming.id (VariableRenaming.weaken introduced)
  rw [Term.renameMapped_comp, Term.renameMapped_comp]
  congr

/-- 异质参数列同样丢弃刚弱化出的未用顶部槽。 -/
@[simp] theorem Arguments.renameMapped_weakenFree_cons
    {σ : Signature.{u, v, w}}
    {bound free targetBound targetFree : SortContext σ}
    {introduced : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (boundRenaming : VariableRenaming bound targetBound)
    (head : Variable targetFree introduced)
    (tail : VariableRenaming free targetFree) :
    (arguments : Arguments σ bound free sorts) →
      (arguments.weakenFree introduced).renameMapped boundRenaming
          (VariableRenaming.cons head tail) =
        arguments.renameMapped boundRenaming tail
  | .nil => rfl
  | .cons term rest => by
      simp [Arguments.renameMapped,
        Term.renameMapped_weakenFree_cons,
        Arguments.renameMapped_weakenFree_cons]

end


mutual

/-- 两次 free weakening 的复合映射直接恢复对应的两层结构弱化。 -/
@[simp] theorem Term.renameMapped_two_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {first second resultSort : σ.SortSymbol} :
    (term : Term σ bound free resultSort) →
      term.renameMapped VariableRenaming.id
          (VariableRenaming.comp
            (VariableRenaming.weaken second)
            (VariableRenaming.weaken first)) =
        (term.weakenFree first).weakenFree second
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app function arguments => by
      simp [Term.renameMapped,
        Arguments.renameMapped_two_weakenFree]

/-- 异质参数列的两次 free weakening 同样合并为一次映射遍历。 -/
@[simp] theorem Arguments.renameMapped_two_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {first second : σ.SortSymbol} {sorts : List σ.SortSymbol} :
    (arguments : Arguments σ bound free sorts) →
      arguments.renameMapped VariableRenaming.id
          (VariableRenaming.comp
            (VariableRenaming.weaken second)
            (VariableRenaming.weaken first)) =
        (arguments.weakenFree first).weakenFree second
  | .nil => rfl
  | .cons term rest => by
      simp [Arguments.renameMapped,
        Term.renameMapped_two_weakenFree,
        Arguments.renameMapped_two_weakenFree]

end

mutual

/-- 三次 free weakening 的复合映射直接恢复三层结构弱化。 -/
@[simp] theorem Term.renameMapped_three_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {first second third resultSort : σ.SortSymbol} :
    (term : Term σ bound free resultSort) →
      term.renameMapped VariableRenaming.id
          (VariableRenaming.comp
            (VariableRenaming.weaken third)
            (VariableRenaming.comp
              (VariableRenaming.weaken second)
              (VariableRenaming.weaken first))) =
        ((term.weakenFree first).weakenFree second).weakenFree third
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app function arguments => by
      simp [Term.renameMapped,
        Arguments.renameMapped_three_weakenFree]

/-- 异质参数列的三次 free weakening 同样合并为一次映射遍历。 -/
@[simp] theorem Arguments.renameMapped_three_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {first second third : σ.SortSymbol} {sorts : List σ.SortSymbol} :
    (arguments : Arguments σ bound free sorts) →
      arguments.renameMapped VariableRenaming.id
          (VariableRenaming.comp
            (VariableRenaming.weaken third)
            (VariableRenaming.comp
              (VariableRenaming.weaken second)
              (VariableRenaming.weaken first))) =
        ((arguments.weakenFree first).weakenFree second).weakenFree third
  | .nil => rfl
  | .cons term rest => by
      simp [Arguments.renameMapped,
        Term.renameMapped_three_weakenFree,
        Arguments.renameMapped_three_weakenFree]

end

mutual

/-- 显式恒等变量像在项上不产生 AST 变化。 -/
@[simp] theorem Term.substituteMapped_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    {sort : σ.SortSymbol} → (term : Term σ bound free sort) →
      term.substituteMapped VariableSubstitution.boundId
          VariableSubstitution.freeId = term
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments => by
      simp [Term.substituteMapped, Arguments.substituteMapped_id]

/-- 显式恒等变量像在参数列上不产生 AST 变化。 -/
@[simp] theorem Arguments.substituteMapped_id
    {σ : Signature.{u, v, w}} {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound free sorts) →
      arguments.substituteMapped VariableSubstitution.boundId
          VariableSubstitution.freeId = arguments
  | _, .nil => rfl
  | _, .cons term rest => by
      simp [Arguments.substituteMapped, Term.substituteMapped_id,
        Arguments.substituteMapped_id]

end

/-- 显式恒等变量像在公式上不产生 AST 变化。 -/
@[simp] theorem Formula.substituteMapped_id
    {σ : Signature.{u, v, w}} {bound free : SortContext σ} :
    (formula : Formula σ bound free) →
      formula.substituteMapped VariableSubstitution.boundId
          VariableSubstitution.freeId = formula
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments => by
      simp [Formula.substituteMapped]
  | .equal left right => by
      simp [Formula.substituteMapped]
  | .neg body => by
      simp [Formula.substituteMapped, Formula.substituteMapped_id]
  | .conj left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_id]
  | .disj left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_id]
  | .imp left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_id]
  | .iff left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_id]
  | .forallE sort body => by
      simp [Formula.substituteMapped, Formula.substituteMapped_id]
  | .existsE sort body => by
      simp [Formula.substituteMapped, Formula.substituteMapped_id]

/-- 抽象顶部 free 变量后再实例化，等于直接实例化该 free 变量。 -/
@[simp] theorem Formula.instantiateTop_abstractFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ bound (sort :: free)) :
    body.abstractFreeTop.instantiateTop replacement =
      body.instantiateFreeTop replacement := by
  change
    (body.substituteMapped
        (fun entry => VariableSubstitution.abstractBound sort entry)
        (fun entry => VariableSubstitution.abstractFreeTop entry)).substituteMapped
      (VariableSubstitution.instantiateTop replacement)
      VariableSubstitution.freeId =
    body.substituteMapped VariableSubstitution.boundId
      (VariableSubstitution.instantiateFreeTop replacement)
  rw [Formula.substituteMapped_comp]
  have hBound :
      (fun {resultSort} (entry : Variable bound resultSort) =>
        (VariableSubstitution.abstractBound sort entry).substituteMapped
          (VariableSubstitution.instantiateTop replacement)
          VariableSubstitution.freeId) =
        (VariableSubstitution.boundId :
          VariableSubstitution σ bound bound free) := by
    funext resultSort entry
    rfl
  have hFree :
      (fun {resultSort} (entry : Variable (sort :: free) resultSort) =>
        (VariableSubstitution.abstractFreeTop entry).substituteMapped
          (VariableSubstitution.instantiateTop replacement)
          VariableSubstitution.freeId) =
        (VariableSubstitution.instantiateFreeTop replacement :
          VariableSubstitution σ (sort :: free) bound free) := by
    funext resultSort entry
    cases entry <;> rfl
  rw [hBound, hFree]

/--
free 上下文顶部变量抽象成 binder 后，在扩展上下文中以规范新变量重新打开，
严格恢复原公式。证明只复合变量像，不重复遍历公式。
-/
@[simp] theorem Formula.instantiateTop_weakenFree_abstractFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (body : Formula σ bound (introduced :: free)) :
    ((body.abstractFreeTop).weakenFree introduced).instantiateTop
        (Term.newestFree introduced) = body := by
  change
    (((body.substituteMapped
          (fun entry => VariableSubstitution.abstractBound introduced entry)
          (fun entry => VariableSubstitution.abstractFreeTop entry)).renameMapped
        VariableRenaming.id (VariableRenaming.weaken introduced)).substituteMapped
      (VariableSubstitution.instantiateTop (Term.newestFree introduced))
      VariableSubstitution.freeId) = body
  rw [← Formula.substituteMapped_of_renaming]
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  have hBound :
      (fun {resultSort} (entry : Variable bound resultSort) =>
        (VariableSubstitution.abstractBound introduced entry).substituteMapped
          (fun middleEntry =>
            (VariableSubstitution.boundId middleEntry).substituteMapped
              (VariableSubstitution.instantiateTop
                (Term.newestFree introduced))
              VariableSubstitution.freeId)
          (fun middleEntry =>
            (VariableSubstitution.of_renaming
                (VariableRenaming.weaken introduced) middleEntry).substituteMapped
              (VariableSubstitution.instantiateTop
                (Term.newestFree introduced))
              VariableSubstitution.freeId)) =
        (VariableSubstitution.boundId :
          VariableSubstitution σ bound bound (introduced :: free)) := by
    funext resultSort entry
    rfl
  have hFree :
      (fun {resultSort}
          (entry : Variable (introduced :: free) resultSort) =>
        (VariableSubstitution.abstractFreeTop entry).substituteMapped
          (fun middleEntry =>
            (VariableSubstitution.boundId middleEntry).substituteMapped
              (VariableSubstitution.instantiateTop
                (Term.newestFree introduced))
              VariableSubstitution.freeId)
          (fun middleEntry =>
            (VariableSubstitution.of_renaming
                (VariableRenaming.weaken introduced) middleEntry).substituteMapped
              (VariableSubstitution.instantiateTop
                (Term.newestFree introduced))
              VariableSubstitution.freeId)) =
        (VariableSubstitution.freeId :
          VariableSubstitution σ (introduced :: free) bound
            (introduced :: free)) := by
    funext resultSort entry
    cases entry <;> rfl
  rw [hBound, hFree]
  exact Formula.substituteMapped_id body

/-- β 往返律的执行器规范形，供重命名后的量词消去直接命中。 -/
@[simp] theorem Formula.instantiateTop_renameMapped_abstractFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (body : Formula σ bound (introduced :: free)) :
    ((body.abstractFreeTop).renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced)).instantiateTop
      (Term.newestFree introduced) = body := by
  simpa only [Formula.weakenFree, Formula.rename,
    Renaming.weakenFree, Renaming.free] using
    Formula.instantiateTop_weakenFree_abstractFreeTop introduced body

/-- 显式恒等重命名不改变公式。 -/
@[simp] theorem Formula.renameMapped_id
    {σ : Signature.{u, v, w}} {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    formula.renameMapped VariableRenaming.id VariableRenaming.id =
      formula := by
  rw [← Formula.substituteMapped_of_renaming]
  have hFree :
      (VariableSubstitution.of_renaming VariableRenaming.id :
        VariableSubstitution σ free bound free) =
      (VariableSubstitution.freeId :
        VariableSubstitution σ free bound free) := by
    funext resultSort entry
    rfl
  rw [hFree]
  exact Formula.substituteMapped_id formula

/-- 公式 free weakening 直接命中专用重命名执行器。 -/
theorem Formula.weakenFree_eq_renameMapped
    {σ : Signature.{u, v, w}} {bound free : SortContext σ}
    (introduced : σ.SortSymbol) (formula : Formula σ bound free) :
    formula.weakenFree introduced =
      formula.renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced) := by
  rfl

/-- 公式的 free weakening 与 lifted 重命名交换，并保持单次结构遍历。 -/
@[simp] theorem Formula.renameMapped_weakenFree_lift
    {σ : Signature.{u, v, w}}
    {bound free targetBound targetFree : SortContext σ}
    {introduced : σ.SortSymbol}
    (boundRenaming : VariableRenaming bound targetBound)
    (freeRenaming : VariableRenaming free targetFree)
    (formula : Formula σ bound free) :
    (formula.weakenFree introduced).renameMapped boundRenaming
        (VariableRenaming.lift (introduced := introduced) freeRenaming) =
      (formula.renameMapped boundRenaming freeRenaming).weakenFree introduced := by
  change
    (formula.renameMapped VariableRenaming.id
      (VariableRenaming.weaken introduced)).renameMapped
        boundRenaming
        (VariableRenaming.lift (introduced := introduced) freeRenaming) =
      (formula.renameMapped boundRenaming freeRenaming).renameMapped
        VariableRenaming.id (VariableRenaming.weaken introduced)
  rw [Formula.renameMapped_comp, Formula.renameMapped_comp]
  congr

/-- 公式 free 上下文顶部交换两次后严格恢复。 -/
@[simp] theorem Formula.renameFree_swapTop_swapTop
    {σ : Signature.{u, v, w}} {bound free : SortContext σ}
    {first second : σ.SortSymbol}
    (formula : Formula σ bound (first :: second :: free)) :
    (formula.renameFree
        (VariableRenaming.swapTop :
          VariableRenaming (first :: second :: free)
            (second :: first :: free))).renameFree
        (VariableRenaming.swapTop :
          VariableRenaming (second :: first :: free)
            (first :: second :: free)) =
      formula := by
  change
    (formula.renameMapped VariableRenaming.id
      (VariableRenaming.swapTop :
        VariableRenaming (first :: second :: free)
          (second :: first :: free))).renameMapped
        VariableRenaming.id
        (VariableRenaming.swapTop :
          VariableRenaming (second :: first :: free)
            (first :: second :: free)) = formula
  rw [Formula.renameMapped_comp]
  change
    formula.renameMapped VariableRenaming.id
      (fun {resultSort}
        (entry : Variable (first :: second :: free) resultSort) =>
          (VariableRenaming.swapTop :
            VariableRenaming (second :: first :: free)
              (first :: second :: free))
            ((VariableRenaming.swapTop :
              VariableRenaming (first :: second :: free)
                (second :: first :: free)) entry)) = formula
  have hFree :
      (fun {resultSort}
        (entry : Variable (first :: second :: free) resultSort) =>
          (VariableRenaming.swapTop :
            VariableRenaming (second :: first :: free)
              (first :: second :: free))
            ((VariableRenaming.swapTop :
              VariableRenaming (first :: second :: free)
                (second :: first :: free)) entry)) =
      (fun {resultSort}
        (entry : Variable (first :: second :: free) resultSort) => entry) := by
    funext resultSort entry
    exact VariableRenaming.swapTop_swapTop entry
  rw [hFree]
  exact Formula.renameMapped_id formula

/-- 两次弱化后的公式随顶部交换只交换两个新槽位。 -/
@[simp] theorem Formula.renameFree_swapTop_weakenFree_weakenFree
    {σ : Signature.{u, v, w}} {bound free : SortContext σ}
    {first second : σ.SortSymbol}
    (formula : Formula σ bound free) :
    ((formula.weakenFree first).weakenFree second).renameFree
        (VariableRenaming.swapTop :
          VariableRenaming (second :: first :: free)
            (first :: second :: free)) =
      (formula.weakenFree second).weakenFree first := by
  change
    ((formula.renameMapped VariableRenaming.id
      (VariableRenaming.weaken first)).renameMapped
        VariableRenaming.id (VariableRenaming.weaken second)).renameMapped
      VariableRenaming.id VariableRenaming.swapTop =
    (formula.renameMapped VariableRenaming.id
      (VariableRenaming.weaken second)).renameMapped
        VariableRenaming.id (VariableRenaming.weaken first)
  rw [Formula.renameMapped_comp, Formula.renameMapped_comp,
    Formula.renameMapped_comp]
  congr

/-- 抽象顶部 free 变量后，在任意重命名目标中以指定变量打开。 -/
@[simp] theorem Formula.instantiateTop_renameMapped_abstractFreeTop_fvar
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (ρ : VariableRenaming sourceFree targetFree)
    (head : Variable targetFree sort)
    (body : Formula σ bound (sort :: sourceFree)) :
    ((body.abstractFreeTop).renameMapped VariableRenaming.id ρ).instantiateTop
        (.fvar head) =
      body.renameMapped VariableRenaming.id
        (VariableRenaming.cons head ρ) := by
  change
    (((body.substituteMapped
          (fun entry => VariableSubstitution.abstractBound sort entry)
          (fun entry => VariableSubstitution.abstractFreeTop entry)).renameMapped
        VariableRenaming.id ρ).substituteMapped
      (VariableSubstitution.instantiateTop (.fvar head))
      VariableSubstitution.freeId) =
    body.renameMapped VariableRenaming.id
      (VariableRenaming.cons head ρ)
  rw [← Formula.substituteMapped_of_renaming]
  rw [← Formula.substituteMapped_of_renaming]
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr
  funext resultSort entry
  cases entry <;>
    simp [VariableSubstitution.abstractFreeTop,
      VariableSubstitution.boundId,
      VariableSubstitution.instantiateTop,
      VariableSubstitution.freeId,
      VariableSubstitution.of_renaming,
      VariableRenaming.cons, Term.substituteMapped]

/-- 弱化后的 binder 以弱化项打开，等于先实例化再整体弱化。 -/
@[simp] theorem Formula.instantiateTop_renameMapped_abstractFreeTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {sort introduced : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ bound (sort :: free)) :
    ((body.abstractFreeTop).renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced)).instantiateTop
          (replacement.weakenFree introduced) =
      (body.instantiateFreeTop replacement).weakenFree introduced := by
  change
    (((body.substituteMapped
          (fun entry => VariableSubstitution.abstractBound sort entry)
          (fun entry => VariableSubstitution.abstractFreeTop entry)).renameMapped
        VariableRenaming.id
        (VariableRenaming.weaken introduced)).substituteMapped
      (VariableSubstitution.instantiateTop
        (replacement.weakenFree introduced))
      VariableSubstitution.freeId) =
    (body.substituteMapped VariableSubstitution.boundId
      (VariableSubstitution.instantiateFreeTop replacement)).renameMapped
        VariableRenaming.id (VariableRenaming.weaken introduced)
  rw [← Formula.substituteMapped_of_renaming]
  rw [← Formula.substituteMapped_of_renaming]
  simp only [Formula.substituteMapped_comp]
  congr
  funext resultSort entry
  cases entry <;>
    simp [VariableSubstitution.abstractFreeTop,
      VariableSubstitution.instantiateTop,
      VariableSubstitution.instantiateFreeTop,
      VariableSubstitution.freeId,
      VariableRenaming.id, VariableRenaming.weaken,
      Term.substituteMapped,
      Term.weakenFree, Term.rename, Renaming.weakenFree,
      Renaming.free, Term.renameMapped]

/-- 两层 free 弱化后，以次新变量打开最内层 binder 的 β 归约。 -/
@[simp] theorem Formula.instantiateTop_two_weakenings_abstractFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (body : Formula σ bound (sort :: free)) :
    Formula.instantiateTop ((Term.newestFree sort).weakenFree introduced)
        (((body.abstractFreeTop).weakenFree sort).weakenFree introduced) =
      body.weakenFree introduced := by
  change
    (((body.abstractFreeTop).renameMapped VariableRenaming.id
        (VariableRenaming.weaken sort)).renameMapped VariableRenaming.id
      (VariableRenaming.weaken introduced)).instantiateTop
        (.fvar (.there .here)) =
      body.renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced)
  rw [Formula.renameMapped_comp]
  change
    ((body.abstractFreeTop).renameMapped VariableRenaming.id
      (VariableRenaming.comp
        (VariableRenaming.weaken introduced)
        (VariableRenaming.weaken sort))).instantiateTop
        (.fvar (.there .here)) =
      body.renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced)
  rw [Formula.instantiateTop_renameMapped_abstractFreeTop_fvar]
  congr
  funext resultSort entry
  cases entry <;> rfl

/--
抽象顶部 free 变量后先加入一个参数槽、再加入新的元素槽，以最新元素槽打开 binder。
结果只执行一次复合重命名，不展开公式树。
-/
@[simp] theorem Formula.instantiateTop_two_weakenings_abstractFreeTop_newest
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (body : Formula σ bound (sort :: free)) :
    Formula.instantiateTop (Term.newestFree sort)
        (((body.abstractFreeTop).weakenFree introduced).weakenFree sort) =
      body.renameMapped VariableRenaming.id
        (VariableRenaming.lift (introduced := sort)
          (VariableRenaming.weaken introduced)) := by
  change
    (((body.abstractFreeTop).renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced)).renameMapped
      VariableRenaming.id (VariableRenaming.weaken sort)).instantiateTop
        (.fvar .here) =
      body.renameMapped VariableRenaming.id
        (VariableRenaming.lift (introduced := sort)
          (VariableRenaming.weaken introduced))
  rw [Formula.renameMapped_comp]
  change
    ((body.abstractFreeTop).renameMapped VariableRenaming.id
      (VariableRenaming.comp
        (VariableRenaming.weaken sort)
        (VariableRenaming.weaken introduced))).instantiateTop
          (.fvar .here) = _
  rw [Formula.instantiateTop_renameMapped_abstractFreeTop_fvar]
  congr

/-- 项穿过一个 binder 后再以任意项实例化该 binder，严格恢复原项。 -/
@[simp] theorem Term.instantiateTop_weakenBound
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (term : Term σ bound free resultSort) :
    (term.weakenBound sort).instantiateTop replacement = term := by

  change (term.renameMapped (VariableRenaming.weaken sort)
    VariableRenaming.id).substituteMapped
      (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId = _
  rw [← Term.substituteMapped_of_bound_renaming, Term.substituteMapped_comp]
  change term.substituteMapped VariableSubstitution.boundId VariableSubstitution.freeId = _
  exact Term.substituteMapped_id term

/-- 参数列穿过一个 binder 后再以任意项实例化该 binder，严格恢复原参数列。 -/
@[simp] theorem Arguments.instantiateTop_weakenBound
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (arguments : Arguments σ bound free sorts) :
    (arguments.weakenBound sort).instantiateTop replacement = arguments := by

  change (arguments.renameMapped (VariableRenaming.weaken sort)
    VariableRenaming.id).substituteMapped
      (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId = _
  rw [← Arguments.substituteMapped_of_bound_renaming, Arguments.substituteMapped_comp]
  change arguments.substituteMapped VariableSubstitution.boundId VariableSubstitution.freeId = _
  exact Arguments.substituteMapped_id arguments

/-- 公式穿过一个 binder 后再以任意项实例化该 binder，严格恢复原公式。 -/
@[simp] theorem Formula.instantiateTop_weakenBound
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (formula : Formula σ bound free) :
    (formula.weakenBound sort).instantiateTop replacement = formula := by

  change (formula.renameMapped (VariableRenaming.weaken sort)
    VariableRenaming.id).substituteMapped
      (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId = _
  rw [← Formula.substituteMapped_of_bound_renaming, Formula.substituteMapped_comp]
  change formula.substituteMapped VariableSubstitution.boundId VariableSubstitution.freeId = _
  exact Formula.substituteMapped_id formula

/-- 最新 bound 变量以给定项实例化为该项。 -/
@[simp] theorem Term.instantiateTop_bvar_here
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    (Term.bvar (.here) : Term σ (sort :: bound) free sort).instantiateTop
        replacement = replacement :=
  rfl

@[simp] theorem Term.instantiateTop_bvar_there
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (entry : Variable bound resultSort) :
    (Term.bvar (.there entry) :
      Term σ (sort :: bound) free resultSort).instantiateTop replacement =
        .bvar entry :=
  rfl

@[simp] theorem Term.instantiateTop_fvar
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (entry : Variable free resultSort) :
    (Term.fvar entry :
      Term σ (sort :: bound) free resultSort).instantiateTop replacement =
        .fvar entry :=
  rfl

@[simp] theorem Term.instantiateTop_app
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (function : σ.FuncSymbol)
    (arguments : Arguments σ (sort :: bound) free
      (σ.funcDomain function)) :
    (Term.app function arguments).instantiateTop replacement =
      .app function (arguments.instantiateTop replacement) :=
  rfl

/-- 空参数列的顶部实例化保持为空。 -/
@[simp] theorem Arguments.instantiateTop_nil
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    (Arguments.nil : Arguments σ (sort :: bound) free []).instantiateTop
        replacement = .nil :=
  rfl

/-- 参数列顶部实例化逐项执行。 -/
@[simp] theorem Arguments.instantiateTop_cons
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort headSort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (head : Term σ (sort :: bound) free headSort)
    (tail : Arguments σ (sort :: bound) free sorts) :
    (Arguments.cons head tail).instantiateTop replacement =
      .cons (head.instantiateTop replacement)
        (tail.instantiateTop replacement) :=
  rfl

mutual

/-- bound 顶部实例化与同一个新 free 槽的 weakening 交换。 -/
@[simp] theorem Term.instantiateTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    {resultSort : σ.SortSymbol} →
      (term : Term σ (sort :: bound) free resultSort) →
      (term.weakenFree introduced).instantiateTop
          (replacement.weakenFree introduced) =
        (term.instantiateTop replacement).weakenFree introduced
  | _, .bvar .here => rfl
  | _, .bvar (.there _) => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments => by
      change
        (Term.app function (arguments.weakenFree introduced)).instantiateTop
            (replacement.weakenFree introduced) =
          (Term.app function
            (arguments.instantiateTop replacement)).weakenFree introduced
      rw [Term.instantiateTop_app]
      change
        Term.app function
            ((arguments.weakenFree introduced).instantiateTop
              (replacement.weakenFree introduced)) =
          Term.app function
            ((arguments.instantiateTop replacement).weakenFree introduced)
      rw [Arguments.instantiateTop_weakenFree]

/-- 异质参数列的 bound 顶部实例化同样与 free weakening 交换。 -/
@[simp] theorem Arguments.instantiateTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ (sort :: bound) free sorts) →
      (arguments.weakenFree introduced).instantiateTop
          (replacement.weakenFree introduced) =
        (arguments.instantiateTop replacement).weakenFree introduced
  | _, .nil => rfl
  | _, .cons head tail => by
      change
        (Arguments.cons (head.weakenFree introduced)
          (tail.weakenFree introduced)).instantiateTop
            (replacement.weakenFree introduced) =
          (Arguments.cons (head.instantiateTop replacement)
            (tail.instantiateTop replacement)).weakenFree introduced
      rw [Arguments.instantiateTop_cons]
      change
        Arguments.cons
            ((head.weakenFree introduced).instantiateTop
              (replacement.weakenFree introduced))
            ((tail.weakenFree introduced).instantiateTop
              (replacement.weakenFree introduced)) =
          Arguments.cons
            ((head.instantiateTop replacement).weakenFree introduced)
            ((tail.instantiateTop replacement).weakenFree introduced)
      rw [Term.instantiateTop_weakenFree,
        Arguments.instantiateTop_weakenFree]

end

/-- 关系原子的顶部实例化只作用于参数列。 -/
@[simp] theorem Formula.instantiateTop_rel
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (relation : σ.RelSymbol)
    (arguments : Arguments σ (sort :: bound) free
      (σ.relDomain relation)) :
    (Formula.rel relation arguments).instantiateTop replacement =
      Formula.rel relation (arguments.instantiateTop replacement) :=
  rfl

/-- 等式公式的顶部实例化只分别实例化两端。 -/
@[simp] theorem Formula.instantiateTop_equal
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort equalitySort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Term σ (sort :: bound) free equalitySort) :
    (Formula.equal left right).instantiateTop replacement =
      Formula.equal (left.instantiateTop replacement)
        (right.instantiateTop replacement) :=
  rfl

/-- 假、真在顶部 bound 实例化下保持不变。 -/
@[simp] theorem Formula.instantiateTop_falsum
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    (Formula.falsum : Formula σ (sort :: bound) free).instantiateTop
        replacement = .falsum :=
  rfl

@[simp] theorem Formula.instantiateTop_truth
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    (Formula.truth : Formula σ (sort :: bound) free).instantiateTop
        replacement = .truth :=
  rfl

/-- 命题连接词逐子式执行顶部 bound 实例化。 -/
@[simp] theorem Formula.instantiateTop_neg
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (sort :: bound) free) :
    (Formula.neg body).instantiateTop replacement =
      .neg (body.instantiateTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateTop_conj
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ (sort :: bound) free) :
    (Formula.conj left right).instantiateTop replacement =
      .conj (left.instantiateTop replacement)
        (right.instantiateTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateTop_disj
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ (sort :: bound) free) :
    (Formula.disj left right).instantiateTop replacement =
      .disj (left.instantiateTop replacement)
        (right.instantiateTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateTop_imp
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ (sort :: bound) free) :
    (Formula.imp left right).instantiateTop replacement =
      .imp (left.instantiateTop replacement)
        (right.instantiateTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateTop_iff
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ (sort :: bound) free) :
    (Formula.iff left right).instantiateTop replacement =
      .iff (left.instantiateTop replacement)
        (right.instantiateTop replacement) :=
  rfl

/-- 最新 free 变量由给定项实例化，其余旧变量和 bound 变量保持不变。 -/
@[simp] theorem Term.instantiateFreeTop_bvar
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (entry : Variable bound resultSort) :
    Term.instantiateFreeTop
        (Term.bvar entry : Term σ bound (sort :: free) resultSort)
        replacement = .bvar entry :=
  rfl

@[simp] theorem Term.instantiateFreeTop_fvar_here
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Term.instantiateFreeTop
        (Term.fvar .here : Term σ bound (sort :: free) sort)
        replacement = replacement :=
  rfl

@[simp] theorem Term.instantiateFreeTop_fvar_there
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (entry : Variable free resultSort) :
    Term.instantiateFreeTop
        (Term.fvar (.there entry) :
          Term σ bound (sort :: free) resultSort)
        replacement = .fvar entry :=
  rfl

@[simp] theorem Term.instantiateFreeTop_app
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (function : σ.FuncSymbol)
    (arguments : Arguments σ bound (sort :: free)
      (σ.funcDomain function)) :
    (Term.app function arguments).instantiateFreeTop replacement =
      .app function (arguments.instantiateFreeTop replacement) :=
  rfl

@[simp] theorem Term.instantiateFreeTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (term : Term σ bound free resultSort) :
    (term.weakenFree sort).instantiateFreeTop replacement = term := by
  exact Term.substitute_weakenFree_instantiateFreeTop
    sort replacement term

/-- 参数列的顶部 free 实例化逐项执行。 -/
@[simp] theorem Arguments.instantiateFreeTop_nil
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Arguments.instantiateFreeTop
        (Arguments.nil : Arguments σ bound (sort :: free) [])
        replacement = .nil :=
  rfl

@[simp] theorem Arguments.instantiateFreeTop_cons
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort headSort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (head : Term σ bound (sort :: free) headSort)
    (tail : Arguments σ bound (sort :: free) sorts) :
    (Arguments.cons head tail).instantiateFreeTop replacement =
      .cons (head.instantiateFreeTop replacement)
        (tail.instantiateFreeTop replacement) :=
  rfl

/-- 公式节点逐子式执行顶部 free 实例化。 -/
@[simp] theorem Formula.instantiateFreeTop_falsum
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Formula.instantiateFreeTop replacement
        (Formula.falsum : Formula σ bound (sort :: free)) = .falsum :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_truth
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Formula.instantiateFreeTop replacement
        (Formula.truth : Formula σ bound (sort :: free)) = .truth :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_rel
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound (sort :: free)
      (σ.relDomain relation)) :
    (Formula.rel relation arguments).instantiateFreeTop replacement =
      .rel relation (arguments.instantiateFreeTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_equal
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort equalitySort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Term σ bound (sort :: free) equalitySort) :
    (Formula.equal left right).instantiateFreeTop replacement =
      .equal (left.instantiateFreeTop replacement)
        (right.instantiateFreeTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_neg
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ bound (sort :: free)) :
    (Formula.neg body).instantiateFreeTop replacement =
      .neg (body.instantiateFreeTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_conj
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ bound (sort :: free)) :
    (Formula.conj left right).instantiateFreeTop replacement =
      .conj (left.instantiateFreeTop replacement)
        (right.instantiateFreeTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_disj
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ bound (sort :: free)) :
    (Formula.disj left right).instantiateFreeTop replacement =
      .disj (left.instantiateFreeTop replacement)
        (right.instantiateFreeTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_imp
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ bound (sort :: free)) :
    (Formula.imp left right).instantiateFreeTop replacement =
      .imp (left.instantiateFreeTop replacement)
        (right.instantiateFreeTop replacement) :=
  rfl

@[simp] theorem Formula.instantiateFreeTop_iff
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (left right : Formula σ bound (sort :: free)) :
    (Formula.iff left right).instantiateFreeTop replacement =
      .iff (left.instantiateFreeTop replacement)
        (right.instantiateFreeTop replacement) :=
  rfl

/-- 顶部 free 实例化穿过量词时只提升替换项。 -/
@[simp] theorem Formula.instantiateFreeTop_forallE
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort quantified : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (quantified :: bound) (sort :: free)) :
    (Formula.forallE quantified body).instantiateFreeTop replacement =
      .forallE quantified
        (body.instantiateFreeTop (replacement.weakenBound quantified)) := by
  simp [Formula.instantiateFreeTop, Formula.substitute,
    Formula.substituteMapped, Substitution.instantiateFreeTop]

@[simp] theorem Formula.instantiateFreeTop_existsE
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort quantified : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (quantified :: bound) (sort :: free)) :
    (Formula.existsE quantified body).instantiateFreeTop replacement =
      .existsE quantified
        (body.instantiateFreeTop (replacement.weakenBound quantified)) := by
  simp [Formula.instantiateFreeTop, Formula.substitute,
    Formula.substituteMapped, Substitution.instantiateFreeTop]

/--
项先穿过一个新 free 槽，再把该槽抽象为 binder，等于直接穿过该 binder。
-/
@[simp] theorem Term.substituteMapped_abstractFreeTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced resultSort : σ.SortSymbol}
    (term : Term σ bound free resultSort) :
    (term.weakenFree introduced).substituteMapped
        (VariableSubstitution.abstractBound introduced)
        VariableSubstitution.abstractFreeTop =
      term.weakenBound introduced := by

  change (term.renameMapped VariableRenaming.id (VariableRenaming.weaken introduced)).substituteMapped
      (VariableSubstitution.abstractBound introduced) VariableSubstitution.abstractFreeTop =
    term.renameMapped (VariableRenaming.weaken introduced) VariableRenaming.id
  rw [← Term.substituteMapped_of_renaming, Term.substituteMapped_comp,
    ← Term.substituteMapped_of_bound_renaming]
  rfl

/-- bound 恒等的非恒等替换与规范全称封闭交换。 -/
@[simp] theorem Formula.substituteMapped_forallFreeTop_boundId
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (body : Formula σ bound (sort :: sourceFree)) :
    (body.forallFreeTop sort).substituteMapped
        VariableSubstitution.boundId substitution =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.liftFree sort substitution)).forallFreeTop sort := by
  change
    Formula.forallE sort
        ((body.abstractFreeTop).substituteMapped
          (VariableSubstitution.liftBound sort
            VariableSubstitution.boundId)
          (VariableSubstitution.weakenBound sort substitution)) =
      Formula.forallE sort
        ((body.substituteMapped VariableSubstitution.boundId
          (VariableSubstitution.liftFree sort substitution)).abstractFreeTop)
  congr 1
  change
    (body.substituteMapped
        (VariableSubstitution.abstractBound sort)
        VariableSubstitution.abstractFreeTop).substituteMapped
          (VariableSubstitution.liftBound sort
            VariableSubstitution.boundId)
          (VariableSubstitution.weakenBound sort substitution) =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.liftFree sort substitution)).substituteMapped
          (VariableSubstitution.abstractBound sort)
          VariableSubstitution.abstractFreeTop
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      change (substitution previous).weakenBound sort =
        ((substitution previous).weakenFree sort).substituteMapped
          (VariableSubstitution.abstractBound sort)
          VariableSubstitution.abstractFreeTop
      exact (Term.substituteMapped_abstractFreeTop_weakenFree
        (substitution previous)).symm

/-- 外部 bound 实例化与规范全称 free 封闭交换。 -/
@[simp] theorem Formula.instantiateTop_forallFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort quantified : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (sort :: bound) (quantified :: free)) :
    (body.forallFreeTop quantified).instantiateTop replacement =
      Formula.forallFreeTop quantified
        (body.instantiateTop (replacement.weakenFree quantified)) := by
  change
    Formula.forallE quantified
        ((body.substituteMapped
          (VariableSubstitution.abstractBound quantified)
          VariableSubstitution.abstractFreeTop).substituteMapped
            (VariableSubstitution.liftBound quantified
              (VariableSubstitution.instantiateTop replacement))
            (VariableSubstitution.weakenBound quantified
              VariableSubstitution.freeId)) =
      Formula.forallE quantified
        ((body.substituteMapped
          (VariableSubstitution.instantiateTop
            (replacement.weakenFree quantified))
          VariableSubstitution.freeId).substituteMapped
            (VariableSubstitution.abstractBound quantified)
            VariableSubstitution.abstractFreeTop)
  congr 1
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr
  · funext resultSort entry
    cases entry with
    | here =>
        change replacement.weakenBound quantified =
          (replacement.weakenFree quantified).substituteMapped
            (VariableSubstitution.abstractBound quantified)
            VariableSubstitution.abstractFreeTop
        exact (Term.substituteMapped_abstractFreeTop_weakenFree
          replacement).symm
    | there previous => rfl
  · funext resultSort entry
    cases entry <;> rfl

/-- 外部 bound 实例化与规范存在 free 封闭交换。 -/
@[simp] theorem Formula.instantiateTop_existsFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort quantified : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (sort :: bound) (quantified :: free)) :
    (body.existsFreeTop quantified).instantiateTop replacement =
      Formula.existsFreeTop quantified
        (body.instantiateTop (replacement.weakenFree quantified)) := by
  change
    Formula.existsE quantified
        ((body.substituteMapped
          (VariableSubstitution.abstractBound quantified)
          VariableSubstitution.abstractFreeTop).substituteMapped
            (VariableSubstitution.liftBound quantified
              (VariableSubstitution.instantiateTop replacement))
            (VariableSubstitution.weakenBound quantified
              VariableSubstitution.freeId)) =
      Formula.existsE quantified
        ((body.substituteMapped
          (VariableSubstitution.instantiateTop
            (replacement.weakenFree quantified))
          VariableSubstitution.freeId).substituteMapped
            (VariableSubstitution.abstractBound quantified)
            VariableSubstitution.abstractFreeTop)
  congr 1
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr
  · funext resultSort entry
    cases entry with
    | here =>
        change replacement.weakenBound quantified =
          (replacement.weakenFree quantified).substituteMapped
            (VariableSubstitution.abstractBound quantified)
            VariableSubstitution.abstractFreeTop
        exact (Term.substituteMapped_abstractFreeTop_weakenFree
          replacement).symm
    | there previous => rfl
  · funext resultSort entry
    cases entry <;> rfl

mutual

/-- 项的 bound/free weakening 可交换。 -/
@[simp] theorem Term.weakenFree_weakenBound
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    (freeIntroduced boundIntroduced : σ.SortSymbol) :
    {sort : σ.SortSymbol} → (term : Term σ bound free sort) →
    (term.weakenFree freeIntroduced).weakenBound boundIntroduced =
      (term.weakenBound boundIntroduced).weakenFree freeIntroduced
  | _, .bvar entry => rfl
  | _, .fvar entry => rfl
  | _, .app function arguments => by
      simp [Arguments.weakenFree_weakenBound]

/-- 异质参数列的 bound/free weakening 可交换。 -/
@[simp] theorem Arguments.weakenFree_weakenBound
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    (freeIntroduced boundIntroduced : σ.SortSymbol) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound free sorts) →
    (arguments.weakenFree freeIntroduced).weakenBound boundIntroduced =
      (arguments.weakenBound boundIntroduced).weakenFree freeIntroduced
  | _, .nil => rfl
  | _, .cons head tail => by
      simp [Term.weakenFree_weakenBound,
        Arguments.weakenFree_weakenBound]

end

/-- bound weakening 后再扩展 free 槽，顶部实例化仍直接恢复旧项。 -/
@[simp] theorem Term.instantiateTop_weakenBound_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (term : Term σ bound free resultSort) :
    ((term.weakenBound sort).weakenFree introduced).instantiateTop
        (replacement.weakenFree introduced) =
      term.weakenFree introduced := by
  rw [← Term.weakenFree_weakenBound introduced sort term]
  exact Term.instantiateTop_weakenBound
    (replacement.weakenFree introduced) (term.weakenFree introduced)

/-- 两层 free weakening 后的 bound 顶部实例化仍直接恢复旧项。 -/
@[simp] theorem Term.instantiateTop_weakenBound_two_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {sort first second resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (term : Term σ bound free resultSort) :
    ((((term.weakenBound sort).weakenFree first).weakenFree second)
        |>.instantiateTop
          ((replacement.weakenFree first).weakenFree second)) =
      (term.weakenFree first).weakenFree second := by
  rw [← Term.weakenFree_weakenBound first sort term]
  exact Term.instantiateTop_weakenBound_weakenFree
    (replacement.weakenFree first) (term.weakenFree first)

namespace VariableSubstitution

/-- bound weakening 与 free 替换提升可交换。 -/
@[simp] theorem weakenBound_liftFree
    {σ : Signature.{u, v, w}}
    {source bound targetFree : SortContext σ}
    (freeIntroduced boundIntroduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source bound targetFree) :
    (weakenBound boundIntroduced
        (liftFree freeIntroduced substitution) :
      VariableSubstitution σ (freeIntroduced :: source)
        (boundIntroduced :: bound) (freeIntroduced :: targetFree)) =
      (liftFree freeIntroduced
        (weakenBound boundIntroduced substitution) :
      VariableSubstitution σ (freeIntroduced :: source)
        (boundIntroduced :: bound) (freeIntroduced :: targetFree)) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      exact Term.weakenFree_weakenBound
        freeIntroduced boundIntroduced (substitution previous)

end VariableSubstitution

/-- lifted free 替换保持规范新变量。 -/
@[simp] theorem Term.substituteMapped_newestFree_liftFree
    {σ : Signature.{u, v, w}}
    {source bound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source bound targetFree) :
    (Term.newestFree (σ := σ) (bound := bound) (free := source)
        introduced).substituteMapped VariableSubstitution.boundId
          (VariableSubstitution.liftFree introduced substitution) =
      Term.newestFree (σ := σ) (bound := bound) (free := targetFree)
        introduced :=
  rfl

/-- 顶部 free 实例化把规范新变量直接归约为替换项。 -/
@[simp] theorem Term.substituteMapped_newestFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    (Term.newestFree (σ := σ) (bound := bound) (free := free)
        sort).substituteMapped VariableSubstitution.boundId
          (VariableSubstitution.instantiateFreeTop replacement) =
      replacement :=
  rfl

mutual

/-- 项上的 free 替换与同一个新 free 槽的 weakening 交换。 -/
@[simp] theorem Term.substituteMapped_weakenFree_boundId
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree) :
    {sort : σ.SortSymbol} → (term : Term σ bound sourceFree sort) →
    (term.weakenFree introduced).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.liftFree introduced substitution) =
      (term.substituteMapped VariableSubstitution.boundId
        substitution).weakenFree introduced
  | _, .bvar entry => by
      simp [Term.substituteMapped, Term.weakenFree, Term.rename,
        Renaming.weakenFree, Renaming.free, Term.renameMapped,
        VariableSubstitution.boundId, VariableRenaming.id]
  | _, .fvar entry => by
      simp [Term.substituteMapped, Term.weakenFree, Term.rename,
        Renaming.weakenFree, Renaming.free, VariableRenaming.weaken,
        Term.renameMapped, VariableSubstitution.liftFree]
  | _, .app function arguments => by
      simp [Term.substituteMapped,
        Arguments.substituteMapped_weakenFree_boundId]

/-- 异质参数列上的 free 替换与同一个新 free 槽的 weakening 交换。 -/
@[simp] theorem Arguments.substituteMapped_weakenFree_boundId
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound sourceFree sorts) →
    (arguments.weakenFree introduced).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.liftFree introduced substitution) =
      (arguments.substituteMapped VariableSubstitution.boundId
        substitution).weakenFree introduced
  | _, .nil => rfl
  | _, .cons head tail => by
      simp [Arguments.substituteMapped,
        Term.substituteMapped_weakenFree_boundId,
        Arguments.substituteMapped_weakenFree_boundId]

end

/-- free 替换穿过同一个新 free 槽时，只提升变量像，不重复遍历原公式。 -/
@[simp] theorem Formula.substituteMapped_weakenFree_boundId
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (formula : Formula σ bound sourceFree) :
    (formula.weakenFree introduced).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.liftFree introduced substitution) =
      (formula.substituteMapped VariableSubstitution.boundId
        substitution).weakenFree introduced := by
  change
    (formula.renameMapped VariableRenaming.id
      (VariableRenaming.weaken introduced)).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.liftFree introduced substitution) =
      (formula.substituteMapped VariableSubstitution.boundId
        substitution).renameMapped VariableRenaming.id
          (VariableRenaming.weaken introduced)
  rw [← Formula.substituteMapped_of_renaming]
  rw [← Formula.substituteMapped_of_renaming]
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr
  funext resultSort entry
  simp [VariableSubstitution.of_renaming,
    VariableSubstitution.liftFree, VariableRenaming.weaken,
    Term.substituteMapped, Term.weakenFree, Term.rename,
    Renaming.weakenFree, Renaming.free]

/-- free 替换与同一个新 free 槽的 weakening 交换。 -/
@[simp] theorem Formula.substituteFree_weakenFree
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (formula : Formula σ bound sourceFree) :
    (formula.weakenFree introduced).substituteFree
        (VariableSubstitution.liftFree introduced substitution) =
      (formula.substituteFree substitution).weakenFree introduced := by
  change
    (formula.weakenFree introduced).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.liftFree introduced substitution) =
      (formula.substituteMapped VariableSubstitution.boundId
        substitution).weakenFree introduced
  exact Formula.substituteMapped_weakenFree_boundId
    introduced substitution formula

/-- bound 恒等的非恒等替换与 bound 顶部实例化交换。 -/
@[simp] theorem Formula.substituteMapped_instantiateTop_boundId
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (replacement : Term σ bound sourceFree sort)
    (body : Formula σ (sort :: bound) sourceFree) :
    (body.instantiateTop replacement).substituteMapped
        VariableSubstitution.boundId substitution =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.weakenBound sort substitution)).instantiateTop
          (replacement.substituteMapped
            VariableSubstitution.boundId substitution) := by
  change
    (body.substituteMapped
        (VariableSubstitution.instantiateTop replacement)
        VariableSubstitution.freeId).substituteMapped
          VariableSubstitution.boundId substitution =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.weakenBound sort substitution)).substituteMapped
          (VariableSubstitution.instantiateTop
            (replacement.substituteMapped
              VariableSubstitution.boundId substitution))
          VariableSubstitution.freeId
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  have hBound :
      (fun {resultSort} (entry : Variable (sort :: bound) resultSort) =>
        (VariableSubstitution.instantiateTop replacement entry).substituteMapped
          VariableSubstitution.boundId substitution) =
        (fun {resultSort} (entry : Variable (sort :: bound) resultSort) =>
          (VariableSubstitution.boundId entry).substituteMapped
            (VariableSubstitution.instantiateTop
              (replacement.substituteMapped
                VariableSubstitution.boundId substitution))
            VariableSubstitution.freeId) := by
    funext resultSort entry
    cases entry <;> rfl
  have hFree :
      (fun {resultSort} (entry : Variable sourceFree resultSort) =>
        (VariableSubstitution.freeId entry).substituteMapped
          VariableSubstitution.boundId substitution) =
        (fun {resultSort} (entry : Variable sourceFree resultSort) =>
          (VariableSubstitution.weakenBound sort substitution entry).substituteMapped
            (VariableSubstitution.instantiateTop
              (replacement.substituteMapped
                VariableSubstitution.boundId substitution))
            VariableSubstitution.freeId) := by
    funext resultSort entry
    change substitution entry =
      ((substitution entry).weakenBound sort).instantiateTop
        (replacement.substituteMapped
          VariableSubstitution.boundId substitution)
    exact (Term.instantiateTop_weakenBound
      (replacement.substituteMapped
        VariableSubstitution.boundId substitution)
      (substitution entry)).symm
  rw [hBound, hFree]

/-- free 替换与 bound 顶部实例化交换，复合后只遍历一次公式。 -/
@[simp] theorem Formula.substituteFree_instantiateTop
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (replacement : Term σ bound sourceFree sort)
    (body : Formula σ (sort :: bound) sourceFree) :
    (body.instantiateTop replacement).substituteFree substitution =
      (body.substituteFree
        (VariableSubstitution.weakenBound sort substitution)).instantiateTop
          (replacement.substituteFree substitution) := by
  change
    (body.instantiateTop replacement).substituteMapped
        VariableSubstitution.boundId substitution =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.weakenBound sort substitution)).instantiateTop
          (replacement.substituteMapped
            VariableSubstitution.boundId substitution)
  exact Formula.substituteMapped_instantiateTop_boundId
    substitution replacement body

/-- free 替换与规范全称封闭交换。 -/
@[simp] theorem Formula.substituteFree_forallFreeTop
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (body : Formula σ bound (sort :: sourceFree)) :
    (body.forallFreeTop sort).substituteFree substitution =
      (body.substituteFree
        (VariableSubstitution.liftFree sort substitution)).forallFreeTop sort := by
  change
    (body.forallFreeTop sort).substituteMapped
        VariableSubstitution.boundId substitution =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.liftFree sort substitution)).forallFreeTop sort
  exact Formula.substituteMapped_forallFreeTop_boundId substitution body

/-- 顶部 free 实例化穿过一个更晚的规范全称变量。 -/
@[simp] theorem Formula.instantiateFreeTop_forallFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {instantiated quantified : σ.SortSymbol}
    (replacement : Term σ bound free instantiated)
    (body : Formula σ bound (quantified :: instantiated :: free)) :
    (body.forallFreeTop quantified).instantiateFreeTop replacement =
      (body.substituteFree
        (VariableSubstitution.liftFree quantified
          (VariableSubstitution.instantiateFreeTop replacement))).forallFreeTop
            quantified := by
  change
    (body.forallFreeTop quantified).substituteFree
        (VariableSubstitution.instantiateFreeTop replacement) = _
  exact Formula.substituteFree_forallFreeTop
    (VariableSubstitution.instantiateFreeTop replacement) body

/-- free 重命名与规范全称封闭交换，并保持专用重命名执行路径。 -/
@[simp] theorem Formula.renameMapped_forallFreeTop
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (ρ : VariableRenaming sourceFree targetFree)
    (body : Formula σ bound (sort :: sourceFree)) :
    (body.forallFreeTop sort).renameMapped VariableRenaming.id ρ =
      (body.renameMapped VariableRenaming.id
        (VariableRenaming.lift (introduced := sort) ρ)).forallFreeTop sort := by
  rw [← Formula.substituteMapped_of_renaming]
  change
    (body.forallFreeTop sort).substituteFree
        (VariableSubstitution.of_renaming (bound := bound) ρ) = _
  rw [Formula.substituteFree_forallFreeTop]
  rw [VariableSubstitution.liftFree_of_renaming]
  change
    (body.substituteMapped VariableSubstitution.boundId
      (VariableSubstitution.of_renaming
        (VariableRenaming.lift (introduced := sort) ρ))).forallFreeTop sort = _
  rw [Formula.substituteMapped_of_renaming]

/-- bound 恒等的非恒等替换与规范存在封闭交换。 -/
@[simp] theorem Formula.substituteMapped_existsFreeTop_boundId
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (body : Formula σ bound (sort :: sourceFree)) :
    (body.existsFreeTop sort).substituteMapped
        VariableSubstitution.boundId substitution =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.liftFree sort substitution)).existsFreeTop sort := by
  change
    Formula.existsE sort
        ((body.abstractFreeTop).substituteMapped
          (VariableSubstitution.liftBound sort
            VariableSubstitution.boundId)
          (VariableSubstitution.weakenBound sort substitution)) =
      Formula.existsE sort
        ((body.substituteMapped VariableSubstitution.boundId
          (VariableSubstitution.liftFree sort substitution)).abstractFreeTop)
  congr 1
  change
    (body.substituteMapped
        (VariableSubstitution.abstractBound sort)
        VariableSubstitution.abstractFreeTop).substituteMapped
          (VariableSubstitution.liftBound sort
            VariableSubstitution.boundId)
          (VariableSubstitution.weakenBound sort substitution) =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.liftFree sort substitution)).substituteMapped
          (VariableSubstitution.abstractBound sort)
          VariableSubstitution.abstractFreeTop
  rw [Formula.substituteMapped_comp, Formula.substituteMapped_comp]
  congr
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      change (substitution previous).weakenBound sort =
        ((substitution previous).weakenFree sort).substituteMapped
          (VariableSubstitution.abstractBound sort)
          VariableSubstitution.abstractFreeTop
      exact (Term.substituteMapped_abstractFreeTop_weakenFree
        (substitution previous)).symm

/-- free 替换与规范存在封闭交换。 -/
@[simp] theorem Formula.substituteFree_existsFreeTop
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (body : Formula σ bound (sort :: sourceFree)) :
    (body.existsFreeTop sort).substituteFree substitution =
      (body.substituteFree
        (VariableSubstitution.liftFree sort substitution)).existsFreeTop sort := by
  change
    (body.existsFreeTop sort).substituteMapped
        VariableSubstitution.boundId substitution =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.liftFree sort substitution)).existsFreeTop sort
  exact Formula.substituteMapped_existsFreeTop_boundId substitution body

/-- free 重命名与规范存在封闭交换，并保持专用重命名执行路径。 -/
@[simp] theorem Formula.renameMapped_existsFreeTop
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    {sort : σ.SortSymbol}
    (ρ : VariableRenaming sourceFree targetFree)
    (body : Formula σ bound (sort :: sourceFree)) :
    (body.existsFreeTop sort).renameMapped VariableRenaming.id ρ =
      (body.renameMapped VariableRenaming.id
        (VariableRenaming.lift (introduced := sort) ρ)).existsFreeTop sort := by
  rw [← Formula.substituteMapped_of_renaming]
  change
    (body.existsFreeTop sort).substituteFree
        (VariableSubstitution.of_renaming (bound := bound) ρ) = _
  rw [Formula.substituteFree_existsFreeTop]
  rw [VariableSubstitution.liftFree_of_renaming]
  change
    (body.substituteMapped VariableSubstitution.boundId
      (VariableSubstitution.of_renaming
        (VariableRenaming.lift (introduced := sort) ρ))).existsFreeTop sort = _
  rw [Formula.substituteMapped_of_renaming]

/-- 顶部 free 实例化穿过一个更晚引入的规范存在变量。 -/
@[simp] theorem Formula.instantiateFreeTop_existsFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {instantiated quantified : σ.SortSymbol}
    (replacement : Term σ bound free instantiated)
    (body : Formula σ bound (quantified :: instantiated :: free)) :
    (body.existsFreeTop quantified).instantiateFreeTop replacement =
      (body.substituteFree
        (VariableSubstitution.liftFree quantified
          (VariableSubstitution.instantiateFreeTop replacement))).existsFreeTop
        quantified := by
  change
    (body.existsFreeTop quantified).substituteFree
        (VariableSubstitution.instantiateFreeTop replacement) =
      (body.substituteFree
        (VariableSubstitution.liftFree quantified
          (VariableSubstitution.instantiateFreeTop replacement))).existsFreeTop
        quantified
  exact Formula.substituteFree_existsFreeTop
    (VariableSubstitution.instantiateFreeTop replacement) body

/-- free 重命名经替换执行与语法核的专用重命名路径一致。 -/
@[simp] theorem Term.substituteFree_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {sort : σ.SortSymbol} (term : Term σ bound sourceFree sort) :
    term.substituteFree (VariableSubstitution.of_renaming ρ) =
      term.renameFree ρ := by
  simp [Term.substituteFree, Substitution.free_map,
    Term.substitute, Term.renameFree, Term.rename, Renaming.free]

/-- 异质参数列上的 free 重命名同样命中专用重命名路径。 -/
@[simp] theorem Arguments.substituteFree_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound sourceFree sorts) :
    arguments.substituteFree (VariableSubstitution.of_renaming ρ) =
      arguments.renameFree ρ := by
  simp [Arguments.substituteFree, Substitution.free_map,
    Arguments.substitute, Arguments.renameFree, Arguments.rename,
    Renaming.free]

/-- 公式上的 free 重命名经替换执行与专用重命名路径一致。 -/
@[simp] theorem Formula.substituteFree_of_renaming
    {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    (formula : Formula σ bound sourceFree) :
    formula.substituteFree (VariableSubstitution.of_renaming ρ) =
      formula.renameFree ρ := by
  induction formula <;>
    simp_all [Formula.substituteFree, Substitution.free_map,
      Formula.substitute, Formula.substituteMapped,
      Formula.renameFree, Formula.rename, Renaming.free,
      Formula.renameMapped]

namespace Context

/-- 对局部上下文中的每个开放公式执行同一个类型化 free 替换。 -/
def substituteFree {σ : Signature.{u, v, w}}
    {sourceFree targetFree : SortContext σ}
    (freeSubstitution :
      VariableSubstitution σ sourceFree [] targetFree) :
    Context σ sourceFree → Context σ targetFree :=
  List.map (Formula.substituteFree freeSubstitution)

end Context
end FirstOrder
end Logic
end YesMetaZFC
