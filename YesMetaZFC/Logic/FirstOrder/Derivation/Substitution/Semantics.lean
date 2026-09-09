import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
import YesMetaZFC.Logic.Semantics
import YesMetaZFC.Logic.Theory

/-!
# 类型化替换的语义

替换在语义上只做一件事：把目标环境沿变量到项的映射拉回源上下文。该表述同时
覆盖 bound/free 替换、fresh 变量实例化及量词下的提升，不再需要单点更新、自然数
深度或 `openAt` 插入关系。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace Env

/-- 在 free 上下文头部压入一个值。 -/
def pushFree {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier sort) :
    Env M bound (sort :: free) where
  boundVal := env.boundVal
  freeVal := Assignment.push value env.freeVal

@[simp] theorem pushFree_bound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (entry : Variable bound sort) :
    (env.pushFree value).boundVal entry = env.boundVal entry :=
  rfl

@[simp] theorem pushFree_here {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier sort) :
    (env.pushFree value).freeVal
      (.here : Variable (sort :: free) sort) = value :=
  rfl

@[simp] theorem pushFree_there {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (entry : Variable free sort) :
    (env.pushFree value).freeVal (.there entry) = env.freeVal entry :=
  rfl

/-- 将目标环境沿一个类型化替换拉回源上下文。恒等替换保持根级快路径。 -/
def pullback {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree) :
    Substitution σ sourceBound sourceFree targetBound targetFree →
      Env M sourceBound sourceFree
  | .id => env
  | .map boundSubstitution freeSubstitution =>
      { boundVal := fun entry => (boundSubstitution entry).eval env
        freeVal := fun entry => (freeSubstitution entry).eval env }

/-- 将目标环境沿一个类型化重命名拉回源上下文。 -/
def pullbackRenaming {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree) :
    Renaming σ sourceBound sourceFree targetBound targetFree →
      Env M sourceBound sourceFree
  | .id => env
  | .map boundRenaming freeRenaming =>
      { boundVal := fun entry => env.boundVal (boundRenaming entry)
        freeVal := fun entry => env.freeVal (freeRenaming entry) }

end Env

mutual

/-- 项重命名后的解释等于在拉回环境中解释原项。 -/
theorem Term.eval_rename {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.rename ρ).eval env =
      term.eval (env.pullbackRenaming ρ) := by
  cases ρ with
  | id =>
      rfl
  | map boundRenaming freeRenaming =>
      cases term with
      | bvar entry =>
          rfl
      | fvar entry =>
          rfl
      | app function arguments =>
          exact congrArg (M.funcInterp function)
            (Arguments.eval_rename env
              (.map boundRenaming freeRenaming) arguments)

/-- 参数列重命名后的解释等于在拉回环境中解释原参数列。 -/
theorem Arguments.eval_rename {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    (arguments.rename ρ).eval env =
      arguments.eval (env.pullbackRenaming ρ) := by
  cases ρ with
  | id =>
      rfl
  | map boundRenaming freeRenaming =>
      cases arguments with
      | nil =>
          rfl
      | cons term rest =>
          let ρ := Renaming.map boundRenaming freeRenaming
          change Values.cons
              ((term.rename ρ).eval env)
              ((rest.rename ρ).eval env) =
            Values.cons
              (term.eval (env.pullbackRenaming ρ))
              (rest.eval (env.pullbackRenaming ρ))
          rw [Term.eval_rename, Arguments.eval_rename]

/-- 项穿过新 binder 后，在压入环境中的解释保持不变。 -/
theorem Term.eval_weakenBound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (term : Term σ bound free sort) :
    (term.weakenBound introduced).eval (env.pushBound value) =
      term.eval env := by
  cases term with
  | bvar entry =>
      rfl
  | fvar entry =>
      rfl
  | app function arguments =>
      exact congrArg (M.funcInterp function)
        (Arguments.eval_weakenBound env value arguments)

/-- 异质参数列穿过新 binder 后的解释保持不变。 -/
theorem Arguments.eval_weakenBound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (arguments : Arguments σ bound free sorts) :
    (arguments.weakenBound introduced).eval (env.pushBound value) =
      arguments.eval env := by
  cases arguments with
  | nil =>
      rfl
  | cons term rest =>
      change Values.cons
          ((term.weakenBound introduced).eval (env.pushBound value))
          ((rest.weakenBound introduced).eval (env.pushBound value)) =
        Values.cons (term.eval env) (rest.eval env)
      rw [Term.eval_weakenBound, Arguments.eval_weakenBound]

/-- 项穿过新 free 变量后，在压入环境中的解释保持不变。 -/
theorem Term.eval_weakenFree {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (term : Term σ bound free sort) :
    (term.weakenFree introduced).eval (env.pushFree value) =
      term.eval env := by
  cases term with
  | bvar entry =>
      rfl
  | fvar entry =>
      rfl
  | app function arguments =>
      exact congrArg (M.funcInterp function)
        (Arguments.eval_weakenFree env value arguments)

/-- 异质参数列穿过新 free 变量后的解释保持不变。 -/
theorem Arguments.eval_weakenFree {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (arguments : Arguments σ bound free sorts) :
    (arguments.weakenFree introduced).eval (env.pushFree value) =
      arguments.eval env := by
  cases arguments with
  | nil =>
      rfl
  | cons term rest =>
      change Values.cons
          ((term.weakenFree introduced).eval (env.pushFree value))
          ((rest.weakenFree introduced).eval (env.pushFree value)) =
        Values.cons (term.eval env) (rest.eval env)
      rw [Term.eval_weakenFree, Arguments.eval_weakenFree]

/-- 项替换后的解释等于在拉回环境中解释原项。 -/
theorem Term.eval_substitute {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (substitution :
      Substitution σ sourceBound sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.substitute substitution).eval env =
      term.eval (env.pullback substitution) := by
  cases substitution with
  | id =>
      rfl
  | map boundSubstitution freeSubstitution =>
      cases term with
      | bvar entry =>
          rfl
      | fvar entry =>
          rfl
      | app function arguments =>
          exact congrArg (M.funcInterp function)
            (Arguments.eval_substitute env
              (.map boundSubstitution freeSubstitution) arguments)

/-- 参数列替换后的解释等于在拉回环境中解释原参数列。 -/
theorem Arguments.eval_substitute {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (substitution :
      Substitution σ sourceBound sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    (arguments.substitute substitution).eval env =
      arguments.eval (env.pullback substitution) := by
  cases substitution with
  | id =>
      rfl
  | map boundSubstitution freeSubstitution =>
      cases arguments with
      | nil =>
          rfl
      | cons term rest =>
          let substitution :
              Substitution σ sourceBound sourceFree targetBound targetFree :=
            .map boundSubstitution freeSubstitution
          change Values.cons
              ((term.substitute substitution).eval env)
              ((rest.substitute substitution).eval env) =
            Values.cons
              (term.eval (env.pullback substitution))
              (rest.eval (env.pullback substitution))
          rw [Term.eval_substitute, Arguments.eval_substitute]

end

namespace Env

/-- 重命名环境拉回与 binder 提升交换。 -/
theorem pullbackRenaming_liftBound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    (introduced : σ.SortSymbol) (value : M.Carrier introduced) :
    (env.pushBound value).pullbackRenaming
        (ρ.liftBound introduced) =
      (env.pullbackRenaming ρ).pushBound value := by
  cases ρ with
  | id =>
      rfl
  | map boundRenaming freeRenaming =>
      rw [Env.mk.injEq]
      constructor
      · funext sort entry
        cases entry <;> rfl
      · rfl

/-- 空 bound/free 上下文中的环境唯一。 -/
theorem empty_unique {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (env : Env M [] []) :
    env = Env.empty := by
  rw [Env.mk.injEq]
  constructor
  · funext sort entry
    exact nomatch entry
  · funext sort entry
    exact nomatch entry

/-- 闭句重命名到任意 free 上下文时，拉回环境仍是唯一空环境。 -/
@[simp] theorem pullbackRenaming_emptyFree {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (env : Env M [] free) :
    env.pullbackRenaming
        (Renaming.emptyFree : Renaming σ [] [] [] free) = Env.empty :=
  empty_unique _

/-- 环境拉回与 binder 提升交换。 -/
theorem pullback_liftBound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (substitution :
      Substitution σ sourceBound sourceFree targetBound targetFree)
    (introduced : σ.SortSymbol) (value : M.Carrier introduced) :
    (env.pushBound value).pullback
        (substitution.liftBound introduced) =
      (env.pullback substitution).pushBound value := by
  cases substitution with
  | id =>
      rfl
  | map boundSubstitution freeSubstitution =>
      rw [Env.mk.injEq]
      constructor
      · funext sort entry
        cases entry with
        | here =>
            rfl
        | there previous =>
            exact Term.eval_weakenBound env value
              (boundSubstitution previous)
      · funext sort entry
        exact Term.eval_weakenBound env value
          (freeSubstitution entry)

/-- 顶部 free 实例化的拉回环境就是压入见证值。 -/
@[simp] theorem pullback_instantiateTop
    {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (replacement : Term σ bound free sort) :
    env.pullback (Substitution.instantiateTop replacement) =
      env.pushBound (replacement.eval env) := by
  rw [Env.mk.injEq]
  constructor
  · funext target entry
    cases entry with
    | here =>
        rfl
    | there previous =>
        rfl
  · rfl

/-- 顶部 free 实例化的拉回环境就是压入见证值。 -/
@[simp] theorem pullback_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (replacement : Term σ bound free sort) :
    env.pullback (Substitution.instantiateFreeTop replacement) =
      env.pushFree (replacement.eval env) := by
  rw [Env.mk.injEq]
  constructor
  · rfl
  · funext target entry
    cases entry with
    | here =>
        rfl
    | there previous =>
        rfl

/-- fresh 变量抽象为 binder 后的拉回环境恢复原 fresh 环境。 -/
@[simp] theorem pullback_abstractFreeTop
    {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier sort) :
    (env.pushBound value).pullback
        (Substitution.abstractFreeTop :
          Substitution σ bound (sort :: free)
            (sort :: bound) free) =
      env.pushFree value := by
  rw [Env.mk.injEq]
  constructor
  · funext target entry
    rfl
  · funext target entry
    cases entry with
    | here =>
        rfl
    | there previous =>
        rfl

end Env

namespace Formula

/-- 公式重命名后的满足关系等价于在拉回环境中满足原公式。 -/
theorem satisfies_rename {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    satisfies env (formula.rename ρ) ↔
      satisfies (env.pullbackRenaming ρ) formula := by
  cases ρ with
  | id => rfl
  | map boundMap freeMap =>
      cases formula with
      | falsum | truth => rfl
      | rel relation arguments =>
          exact (congrArg (M.relInterp relation)
            (Arguments.eval_rename env (.map boundMap freeMap) arguments)).to_iff
      | equal left right =>
          exact (congr (congrArg Eq
            (Term.eval_rename env (.map boundMap freeMap) left))
            (Term.eval_rename env (.map boundMap freeMap) right)).to_iff
      | neg body => exact not_congr (satisfies_rename env (.map boundMap freeMap) body)
      | conj left right =>
          exact and_congr (satisfies_rename env (.map boundMap freeMap) left) (satisfies_rename env (.map boundMap freeMap) right)
      | disj left right =>
          exact or_congr (satisfies_rename env (.map boundMap freeMap) left) (satisfies_rename env (.map boundMap freeMap) right)
      | imp left right =>
          exact imp_congr (satisfies_rename env (.map boundMap freeMap) left) (satisfies_rename env (.map boundMap freeMap) right)
      | iff left right =>
          exact iff_congr (satisfies_rename env (.map boundMap freeMap) left) (satisfies_rename env (.map boundMap freeMap) right)
      | forallE sort body =>
          apply forall_congr'
          intro value
          exact (satisfies_rename (env.pushBound value)
            ((Renaming.map boundMap freeMap).liftBound sort) body).trans
              (by rw [Env.pullbackRenaming_liftBound])
      | existsE sort body =>
          apply exists_congr
          intro value
          exact (satisfies_rename (env.pushBound value)
            ((Renaming.map boundMap freeMap).liftBound sort) body).trans
              (by rw [Env.pullbackRenaming_liftBound])

/-- 闭句嵌入任意 free 上下文后保持其闭语义。 -/
theorem satisfies_fromSentence {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (env : Env M [] free) (sentence : Sentence σ) :
    satisfies env (Formula.fromSentence sentence) ↔
      sentence.TrueIn M := by
  simpa [Formula.fromSentence, Formula.TrueIn] using
    satisfies_rename env
      (Renaming.emptyFree : Renaming σ [] [] [] free) sentence

/-- 公式替换后的满足关系等价于在拉回环境中满足原公式。 -/
theorem satisfies_substitute {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (env : Env M targetBound targetFree)
    (substitution :
      Substitution σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    satisfies env (formula.substitute substitution) ↔
      satisfies (env.pullback substitution) formula := by
  cases substitution with
  | id => rfl
  | map boundMap freeMap =>
      cases formula with
      | falsum | truth => rfl
      | rel relation arguments =>
          exact (congrArg (M.relInterp relation)
            (Arguments.eval_substitute env (.map boundMap freeMap) arguments)).to_iff
      | equal left right =>
          exact (congr (congrArg Eq
            (Term.eval_substitute env (.map boundMap freeMap) left))
            (Term.eval_substitute env (.map boundMap freeMap) right)).to_iff
      | neg body => exact not_congr (satisfies_substitute env (.map boundMap freeMap) body)
      | conj left right =>
          exact and_congr (satisfies_substitute env (.map boundMap freeMap) left) (satisfies_substitute env (.map boundMap freeMap) right)
      | disj left right =>
          exact or_congr (satisfies_substitute env (.map boundMap freeMap) left) (satisfies_substitute env (.map boundMap freeMap) right)
      | imp left right =>
          exact imp_congr (satisfies_substitute env (.map boundMap freeMap) left) (satisfies_substitute env (.map boundMap freeMap) right)
      | iff left right =>
          exact iff_congr (satisfies_substitute env (.map boundMap freeMap) left) (satisfies_substitute env (.map boundMap freeMap) right)
      | forallE sort body =>
          apply forall_congr'
          intro value
          exact (satisfies_substitute (env.pushBound value)
            ((Substitution.map boundMap freeMap).liftBound sort) body).trans
              (by rw [Env.pullback_liftBound])
      | existsE sort body =>
          apply exists_congr
          intro value
          exact (satisfies_substitute (env.pushBound value)
            ((Substitution.map boundMap freeMap).liftBound sort) body).trans
              (by rw [Env.pullback_liftBound])

/-- free 替换语义是统一替换语义的直接特例。 -/
theorem satisfies_substituteFree {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound sourceFree targetFree : SortContext σ}
    (env : Env M bound targetFree)
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree)
    (formula : Formula σ bound sourceFree) :
    satisfies env (formula.substituteFree substitution) ↔
      satisfies (env.pullback (Substitution.free_map substitution)) formula := by
  simpa [Formula.substituteFree] using
    satisfies_substitute env (Substitution.free_map substitution) formula

/-- fresh 变量实例化的语义等于把见证值压入 free 环境。 -/
theorem satisfies_instantiateFreeTop {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (replacement : Term σ bound free sort)
    (body : Formula σ bound (sort :: free)) :
    satisfies env (body.instantiateFreeTop replacement) ↔
      satisfies (env.pushFree (replacement.eval env)) body := by
  simpa [Formula.instantiateFreeTop] using
    satisfies_substitute env
      (Substitution.instantiateFreeTop replacement) body

/-- binder 顶部实例化的语义等于把见证值压入 bound 环境。 -/
theorem satisfies_instantiateTop {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (replacement : Term σ bound free sort)
    (body : Formula σ (sort :: bound) free) :
    satisfies env (body.instantiateTop replacement) ↔
      satisfies (env.pushBound (replacement.eval env)) body := by
  simpa [Formula.instantiateTop] using
    satisfies_substitute env
      (Substitution.instantiateTop replacement) body

/-- fresh 变量抽象为 binder 后保持满足关系。 -/
theorem satisfies_abstractFreeTop {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier sort)
    (body : Formula σ bound (sort :: free)) :
    satisfies (env.pushBound value) body.abstractFreeTop ↔
      satisfies (env.pushFree value) body := by
  simpa [Formula.abstractFreeTop] using
    satisfies_substitute (env.pushBound value)
      (Substitution.abstractFreeTop :
        Substitution σ bound (sort :: free) (sort :: bound) free) body

/-- 全称量化 fresh 顶部变量的直接语义。 -/
theorem satisfies_forallFreeTop {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (body : Formula σ bound (sort :: free)) :
    satisfies env (body.forallFreeTop sort) ↔
      ∀ value, satisfies (env.pushFree value) body := by
  simp [Formula.forallFreeTop, satisfies, satisfies_abstractFreeTop]

/-- 存在量化 fresh 顶部变量的直接语义。 -/
theorem satisfies_existsFreeTop {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (body : Formula σ bound (sort :: free)) :
    satisfies env (body.existsFreeTop sort) ↔
      ∃ value, satisfies (env.pushFree value) body := by
  simp [Formula.existsFreeTop, satisfies, satisfies_abstractFreeTop]

/-- 旧公式穿过 fresh free 变量后，满足关系不依赖新变量的值。 -/
theorem satisfies_weakenFree {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier introduced)
    (formula : Formula σ bound free) :
    satisfies (env.pushFree value) (formula.weakenFree introduced) ↔
      satisfies env formula := by
  induction formula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp [satisfies, Arguments.eval_weakenFree]
  | equal left right =>
      simp [satisfies, Term.eval_weakenFree]
  | neg body ih =>
      simpa [satisfies] using not_congr (ih env)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft env) (ihRight env)
  | disj left right ihLeft ihRight =>
      exact or_congr (ihLeft env) (ihRight env)
  | imp left right ihLeft ihRight =>
      exact imp_congr (ihLeft env) (ihRight env)
  | iff left right ihLeft ihRight =>
      exact iff_congr (ihLeft env) (ihRight env)
  | forallE sort body ih =>
      simp only [Formula.weakenFree_forallE, satisfies]
      constructor
      · intro hFormula boundValue
        exact (ih (env.pushBound boundValue)).mp (hFormula boundValue)
      · intro hFormula boundValue
        exact (ih (env.pushBound boundValue)).mpr (hFormula boundValue)
  | existsE sort body ih =>
      simp only [Formula.weakenFree_existsE, satisfies]
      constructor
      · rintro ⟨boundValue, hBody⟩
        exact ⟨boundValue, (ih (env.pushBound boundValue)).mp hBody⟩
      · rintro ⟨boundValue, hBody⟩
        exact ⟨boundValue, (ih (env.pushBound boundValue)).mpr hBody⟩

end Formula
end FirstOrder
end Logic
end YesMetaZFC
