import YesMetaZFC.Model.Henkin.Elimination
import YesMetaZFC.Logic.FirstOrder.FreshVariable

/-!
# Henkin 见证消去的推导搬运

指定见证常量被统一解释为 free 上下文末位的持久新变量。该位置在全称一般化、
free strengthening 与统一替换中保持稳定，因此推导搬运不需要自然数新鲜性、
良构性或额外的变量避让条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}}
variable [DecidableEq σ.SortSymbol]

/-! ## 规范持久变量解释 -/

/-- 原 free 变量进入末位持久扩展后的规范项像。 -/
def persistentFreeSubstitution
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) :
    VariableSubstitution (HSignature σ) free bound
      (FreshVariable.persistentContext free witnessSort) :=
  fun entry => .fvar (FreshVariable.persistentRenaming witnessSort entry)

/-- 被消去见证常量的规范像。 -/
def persistentImage
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) :
    Term (HSignature σ) bound
      (FreshVariable.persistentContext free witnessSort) witnessSort :=
  (FreshVariable.persistent (σ := HSignature σ) (free := free)
    witnessSort).embedBoundClosed bound

/-- 把指定见证常量消去为 free 上下文末位的持久变量。 -/
def Term.eliminatePersistentWitness
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {sort : σ.SortSymbol}
    (term : Term (HSignature σ) bound free sort) :
    Term (HSignature σ) bound
      (FreshVariable.persistentContext free witnessSort) sort :=
  Term.eliminateWitness witnessSort witnessIndex
    VariableSubstitution.boundId
    (persistentFreeSubstitution (σ := σ) witnessSort)
    (persistentImage (σ := σ) witnessSort) term

/-- 参数列上的规范持久变量见证消去。 -/
def Arguments.eliminatePersistentWitness
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) bound free sorts) :
    Arguments (HSignature σ) bound
      (FreshVariable.persistentContext free witnessSort) sorts :=
  Arguments.eliminateWitness witnessSort witnessIndex
    VariableSubstitution.boundId
    (persistentFreeSubstitution (σ := σ) witnessSort)
    (persistentImage (σ := σ) witnessSort) arguments

/-- 公式上的规范持久变量见证消去。 -/
def Formula.eliminatePersistentWitness
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (formula : Formula (HSignature σ) bound free) :
    Formula (HSignature σ) bound
      (FreshVariable.persistentContext free witnessSort) :=
  Formula.eliminateWitness witnessSort witnessIndex
    VariableSubstitution.boundId
    (persistentFreeSubstitution (σ := σ) witnessSort)
    (persistentImage (σ := σ) witnessSort) formula

omit [DecidableEq σ.SortSymbol] in
@[simp] theorem persistentFreeSubstitution_weakenBound
    {bound free : SortContext (HSignature σ)}
    (introduced witnessSort : σ.SortSymbol) :
    (VariableSubstitution.weakenBound (σ := HSignature σ) introduced
        (persistentFreeSubstitution (σ := σ) (bound := bound)
          (free := free) witnessSort) :
      VariableSubstitution (HSignature σ) free (introduced :: bound)
        (FreshVariable.persistentContext free witnessSort)) =
      (persistentFreeSubstitution
        (σ := σ) (bound := introduced :: bound) (free := free)
          witnessSort :
        VariableSubstitution (HSignature σ) free (introduced :: bound)
          (FreshVariable.persistentContext free witnessSort)) := by
  funext sort entry
  simp [persistentFreeSubstitution, VariableSubstitution.weakenBound,
    Term.weakenBound, Term.rename, Renaming.weakenBound, Renaming.bound,
    Term.renameMapped, VariableRenaming.id]

omit [DecidableEq σ.SortSymbol] in
@[simp] theorem persistentImage_weakenBound
    {bound free : SortContext (HSignature σ)}
    (introduced witnessSort : σ.SortSymbol) :
    Term.weakenBound (σ := HSignature σ) introduced
        (persistentImage (σ := σ) (bound := bound) (free := free)
          witnessSort) =
      persistentImage (σ := σ) (bound := introduced :: bound) (free := free)
        witnessSort := by
  change Term.weakenBound (σ := HSignature σ) introduced
      ((FreshVariable.persistent (σ := HSignature σ) (free := free)
        witnessSort).embedBoundClosed bound) =
    Term.weakenBound (σ := HSignature σ) introduced
      ((FreshVariable.persistent (σ := HSignature σ) (free := free)
        witnessSort).embedBoundClosed bound)
  rfl

/-- 规范见证消去与最外层 bound 实例化交换。 -/
@[simp] theorem Formula.eliminatePersistentWitness_instantiateTop
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {sort : σ.SortSymbol}
    (replacement : Term (HSignature σ) bound free sort)
    (body : Formula (HSignature σ) (sort :: bound) free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (body.instantiateTop replacement) =
      (Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        body).instantiateTop
        (Term.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
          replacement) := by
  simpa [Formula.eliminatePersistentWitness,
    Term.eliminatePersistentWitness] using
    (Formula.eliminateWitness_instantiateTop
      (σ := σ) witnessSort witnessIndex
      (VariableSubstitution.boundId :
        VariableSubstitution (HSignature σ) bound bound
          (FreshVariable.persistentContext free witnessSort))
      (persistentFreeSubstitution (σ := σ) (bound := bound) witnessSort)
      (persistentImage (σ := σ) (bound := bound) (free := free) witnessSort)
      replacement body)

/-! ## 持久消去与 free 替换 -/

/--
先消去普通替换项中的见证，再在源、目标两侧保留同一个末位持久变量。
-/
def eliminateSubstitution
    {sourceFree targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (substitution : VariableSubstitution (HSignature σ)
      sourceFree [] targetFree) :
    VariableSubstitution (HSignature σ)
      (FreshVariable.persistentContext sourceFree witnessSort) []
      (FreshVariable.persistentContext targetFree witnessSort) :=
  FreshVariable.preservePersistent (σ := HSignature σ) witnessSort
    (fun entry =>
      Term.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (substitution entry))

/-- 规范见证消去与任意类型化 free 替换交换。 -/
@[simp] theorem Formula.eliminatePersistentWitness_substituteFree
    {sourceFree targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (substitution : VariableSubstitution (HSignature σ)
      sourceFree [] targetFree)
    (formula : OpenFormula (HSignature σ) sourceFree) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (formula.substituteFree substitution) =
      (Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        formula).substituteFree
          (eliminateSubstitution (σ := σ) witnessSort witnessIndex
            substitution) := by
  change Formula.eliminateWitness witnessSort witnessIndex
      (VariableSubstitution.boundId :
        VariableSubstitution (HSignature σ) [] []
          (FreshVariable.persistentContext targetFree witnessSort))
      (persistentFreeSubstitution (σ := σ) (bound := [])
        (free := targetFree) witnessSort)
      (persistentImage (σ := σ) (bound := []) (free := targetFree)
        witnessSort)
      (formula.substituteMapped
        (VariableSubstitution.boundId :
          VariableSubstitution (HSignature σ) [] [] targetFree)
        substitution) =
    (Formula.eliminateWitness witnessSort witnessIndex
      (VariableSubstitution.boundId :
        VariableSubstitution (HSignature σ) [] []
          (FreshVariable.persistentContext sourceFree witnessSort))
      (persistentFreeSubstitution (σ := σ) (bound := [])
        (free := sourceFree) witnessSort)
      (persistentImage (σ := σ) (bound := []) (free := sourceFree)
        witnessSort) formula).substituteMapped
      (VariableSubstitution.boundId :
        VariableSubstitution (HSignature σ) [] []
          (FreshVariable.persistentContext targetFree witnessSort))
      (eliminateSubstitution (σ := σ) witnessSort witnessIndex substitution)
  rw [Formula.eliminateWitness_substituteMapped_source,
    Formula.eliminateWitness_substituteMapped]
  congr
  · funext resultSort entry
    change Term.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (substitution entry) =
      FreshVariable.preservePersistent (σ := HSignature σ) witnessSort
        (fun entry =>
          Term.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
            (substitution entry))
        (Variable.appendRight witnessSort entry)
    exact (FreshVariable.preservePersistent_appendRight
      (σ := HSignature σ) witnessSort
      (fun entry =>
        Term.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
          (substitution entry)) entry).symm
  · simp [persistentImage, eliminateSubstitution,
      FreshVariable.persistent, Term.substituteMapped]

/-- 规范见证消去与 free 上下文头部 weakening 交换。 -/
@[simp] theorem Formula.eliminatePersistentWitness_weakenFree
    {free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (introduced : σ.SortSymbol)
    (formula : OpenFormula (HSignature σ) free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (Formula.weakenFree (σ := HSignature σ) introduced formula) =
      Formula.weakenFree (σ := HSignature σ) introduced
        (Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
          formula) := by
  change Formula.eliminateWitness witnessSort witnessIndex
      (VariableSubstitution.boundId :
        VariableSubstitution (HSignature σ) [] []
          (introduced :: FreshVariable.persistentContext free witnessSort))
      (persistentFreeSubstitution (σ := σ) (bound := [])
        (free := introduced :: free) witnessSort)
      (persistentImage (σ := σ) (bound := [])
        (free := introduced :: free) witnessSort)
      (Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
        (VariableRenaming.weaken introduced) formula) =
    Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
      (VariableRenaming.weaken introduced)
      (Formula.eliminateWitness witnessSort witnessIndex
        (VariableSubstitution.boundId :
          VariableSubstitution (HSignature σ) [] []
            (FreshVariable.persistentContext free witnessSort))
        (persistentFreeSubstitution (σ := σ) (bound := [])
          (free := free) witnessSort)
        (persistentImage (σ := σ) (bound := []) (free := free)
          witnessSort) formula)
  rw [← Formula.substituteMapped_of_renaming,
    ← Formula.substituteMapped_of_renaming,
    Formula.eliminateWitness_substituteMapped_source,
    Formula.eliminateWitness_substituteMapped]
  congr

/-- 规范见证消去与 free 顶部变量抽象为 binder 交换。 -/
@[simp] theorem Formula.eliminatePersistentWitness_abstractFreeTop
    {free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (introduced : σ.SortSymbol)
    (body : OpenFormula (HSignature σ) (introduced :: free)) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (Formula.abstractFreeTop (σ := HSignature σ) body) =
      Formula.abstractFreeTop (σ := HSignature σ)
        (Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
          body) := by
  change Formula.eliminateWitness witnessSort witnessIndex
      (VariableSubstitution.boundId :
        VariableSubstitution (HSignature σ) [introduced] [introduced]
          (FreshVariable.persistentContext free witnessSort))
      (persistentFreeSubstitution (σ := σ) (bound := [introduced])
        (free := free) witnessSort)
      (persistentImage (σ := σ) (bound := [introduced]) (free := free)
        witnessSort)
      (Formula.substituteMapped (σ := HSignature σ)
        (VariableSubstitution.abstractBound (σ := HSignature σ) introduced)
        (VariableSubstitution.abstractFreeTop (σ := HSignature σ)) body) =
    Formula.substituteMapped (σ := HSignature σ)
      (VariableSubstitution.abstractBound (σ := HSignature σ) introduced)
      (VariableSubstitution.abstractFreeTop (σ := HSignature σ))
      (Formula.eliminateWitness witnessSort witnessIndex
        (VariableSubstitution.boundId :
          VariableSubstitution (HSignature σ) [] []
            (introduced :: FreshVariable.persistentContext free witnessSort))
        (persistentFreeSubstitution (σ := σ) (bound := [])
          (free := introduced :: free) witnessSort)
        (persistentImage (σ := σ) (bound := [])
          (free := introduced :: free) witnessSort) body)
  rw [Formula.eliminateWitness_substituteMapped_source,
    Formula.eliminateWitness_substituteMapped]
  congr
  funext resultSort entry
  cases entry with
  | here =>
      rfl
  | there previous =>
      change (Term.fvar (σ := HSignature σ)
          (Variable.appendRight witnessSort previous) :
          Term (HSignature σ) [introduced]
            (FreshVariable.persistentContext free witnessSort) resultSort) =
        (Term.fvar (σ := HSignature σ)
          (Variable.appendRight witnessSort previous) :
          Term (HSignature σ) [introduced]
            (FreshVariable.persistentContext free witnessSort) resultSort)
      rfl

/-- 规范见证消去与 free 顶部全称封闭交换。 -/
@[simp] theorem Formula.eliminatePersistentWitness_forallFreeTop
    {free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (introduced : σ.SortSymbol)
    (body : OpenFormula (HSignature σ) (introduced :: free)) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (Formula.forallFreeTop (σ := HSignature σ) introduced body) =
      Formula.forallFreeTop (σ := HSignature σ) introduced
        (Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
          body) := by
  simp only [Formula.forallFreeTop, Formula.eliminatePersistentWitness,
    Formula.eliminateWitness, VariableSubstitution.liftBound_boundId,
    persistentFreeSubstitution_weakenBound, persistentImage_weakenBound]
  congr 1
  exact Formula.eliminatePersistentWitness_abstractFreeTop
    (σ := σ) witnessSort witnessIndex introduced body

/-- 规范见证消去与 free 顶部存在封闭交换。 -/
@[simp] theorem Formula.eliminatePersistentWitness_existsFreeTop
    {free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (introduced : σ.SortSymbol)
    (body : OpenFormula (HSignature σ) (introduced :: free)) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (Formula.existsFreeTop (σ := HSignature σ) introduced body) =
      Formula.existsFreeTop (σ := HSignature σ) introduced
        (Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
          body) := by
  simp only [Formula.existsFreeTop, Formula.eliminatePersistentWitness,
    Formula.eliminateWitness, VariableSubstitution.liftBound_boundId,
    persistentFreeSubstitution_weakenBound, persistentImage_weakenBound]
  congr 1
  exact Formula.eliminatePersistentWitness_abstractFreeTop
    (σ := σ) witnessSort witnessIndex introduced body

/-! ## 规范消去的构造子快路径 -/

@[simp] theorem Formula.eliminatePersistentWitness_falsum
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.falsum : Formula (HSignature σ) bound free) = .falsum :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_truth
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.truth : Formula (HSignature σ) bound free) = .truth :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_equal
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {sort : σ.SortSymbol}
    (left right : Term (HSignature σ) bound free sort) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.equal left right) =
      .equal
        (Term.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex left)
        (Term.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex right) :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_neg
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (body : Formula (HSignature σ) bound free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.neg body) =
      .neg (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex body) :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_conj
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (left right : Formula (HSignature σ) bound free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.conj left right) =
      .conj
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex left)
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex right) :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_disj
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (left right : Formula (HSignature σ) bound free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.disj left right) =
      .disj
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex left)
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex right) :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_imp
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (left right : Formula (HSignature σ) bound free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.imp left right) =
      .imp
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex left)
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex right) :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_iff
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (left right : Formula (HSignature σ) bound free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.iff left right) =
      .iff
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex left)
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex right) :=
  rfl

@[simp] theorem Formula.eliminatePersistentWitness_forallE
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (sort : σ.SortSymbol)
    (body : Formula (HSignature σ) (sort :: bound) free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.forallE sort body) =
      .forallE sort
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex body) := by
  simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]

@[simp] theorem Formula.eliminatePersistentWitness_existsE
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (sort : σ.SortSymbol)
    (body : Formula (HSignature σ) (sort :: bound) free) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (.existsE sort body) =
      .existsE sort
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex body) := by
  simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]

/-- 指定见证常量在持久消去下直接变成末位规范变量。 -/
@[simp] theorem Term.eliminatePersistentWitness_witnessTerm
    (sort : σ.SortSymbol) (index : Nat) :
    Term.eliminatePersistentWitness (σ := σ) sort index
        (witnessTerm (σ := σ) sort index) =
      persistentImage (σ := σ) (bound := []) (free := []) sort := by
  simp [Term.eliminatePersistentWitness, witnessTerm,
    Term.eliminateWitness]

/-- 不含指定见证的空 free 公式只执行到持久上下文的规范嵌入。 -/
theorem Formula.eliminatePersistentWitness_emptyFree_of_not_uses
    {bound : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (formula : Formula (HSignature σ) bound [])
    (hNoWitness :
      ¬ Formula.usesWitness witnessSort witnessIndex formula) :
    Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex formula =
      Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
        (VariableRenaming.empty : VariableRenaming [] [witnessSort])
        formula := by
  unfold Formula.eliminatePersistentWitness
  have hFree :
      (persistentFreeSubstitution (σ := σ) (bound := bound)
        (free := []) witnessSort :
        VariableSubstitution (HSignature σ) [] bound [witnessSort]) =
      (VariableSubstitution.of_renaming (σ := HSignature σ)
        (bound := bound)
        (VariableRenaming.empty : VariableRenaming [] [witnessSort]) :
        VariableSubstitution (HSignature σ) [] bound [witnessSort]) := by
    funext resultSort entry
    exact nomatch entry
  change
    Formula.eliminateWitness witnessSort witnessIndex
        (VariableSubstitution.boundId :
          VariableSubstitution (HSignature σ) bound bound [witnessSort])
        (persistentFreeSubstitution (σ := σ) (bound := bound)
          (free := []) witnessSort)
        (persistentImage (σ := σ) (bound := bound) (free := []) witnessSort)
        formula =
      Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
        (VariableRenaming.empty : VariableRenaming [] [witnessSort]) formula
  rw [Formula.eliminateWitness_eq_substituteMapped_of_not_uses
      (σ := σ) witnessSort witnessIndex
      (VariableSubstitution.boundId :
        VariableSubstitution (HSignature σ) bound bound [witnessSort])
      (persistentFreeSubstitution (σ := σ) (bound := bound)
        (free := []) witnessSort)
      (persistentImage (σ := σ) (bound := bound) (free := []) witnessSort)
      hNoWitness,
    hFree]
  exact Formula.substituteMapped_of_renaming
    (σ := HSignature σ)
    (VariableRenaming.empty : VariableRenaming [] [witnessSort]) formula

/-- 新见证实例消去后正好成为规范打开的量词体。 -/
@[simp] theorem Formula.eliminatePersistentWitness_witnessInstance
    (sort : σ.SortSymbol) (index : Nat)
    (body : Formula (HSignature σ) [sort] [])
    (hBody : ¬ Formula.usesWitness sort index body) :
    Formula.eliminatePersistentWitness (σ := σ) sort index
        (body.instantiateTop (witnessTerm (σ := σ) sort index)) =
      Formula.openBoundTop (σ := HSignature σ) sort body := by
  rw [Formula.eliminatePersistentWitness_instantiateTop,
    Term.eliminatePersistentWitness_witnessTerm,
    Formula.eliminatePersistentWitness_emptyFree_of_not_uses
      (σ := σ) sort index body hBody]
  change
    (Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
      (VariableRenaming.empty : VariableRenaming [] [sort]) body).substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := HSignature σ) (free := []) sort))
        VariableSubstitution.freeId =
      Formula.openBoundTop (σ := HSignature σ) sort body
  unfold Formula.openBoundTop
  calc
    (Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
        (VariableRenaming.empty : VariableRenaming [] [sort]) body).substituteMapped
          (VariableSubstitution.instantiateTop
            (FreshVariable.newest (σ := HSignature σ) (free := []) sort))
          VariableSubstitution.freeId =
      (body.substituteMapped VariableSubstitution.boundId
        (VariableSubstitution.of_renaming (σ := HSignature σ) (bound := [sort])
          (VariableRenaming.empty : VariableRenaming [] [sort]))).substituteMapped
            (VariableSubstitution.instantiateTop
              (FreshVariable.newest (σ := HSignature σ) (free := []) sort))
            VariableSubstitution.freeId := by
        exact congrArg
          (fun formula =>
            formula.substituteMapped
              (VariableSubstitution.instantiateTop
                (FreshVariable.newest (σ := HSignature σ) (free := []) sort))
              VariableSubstitution.freeId)
          (Formula.substituteMapped_of_renaming
            (σ := HSignature σ)
            (VariableRenaming.empty : VariableRenaming [] [sort]) body).symm
    _ = body.substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := HSignature σ) (free := []) sort))
        (VariableSubstitution.of_renaming (σ := HSignature σ) (bound := [])
          (VariableRenaming.weaken sort : VariableRenaming [] [sort])) := by
      rw [Formula.substituteMapped_comp]
      congr
      funext resultSort entry
      exact nomatch entry

/-- 不含指定见证的闭句消去后只是进入单变量 fresh 上下文。 -/
@[simp] theorem Formula.eliminatePersistentWitness_sentence_of_not_uses
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (sentence : Sentence (HSignature σ))
    (hNoWitness :
      ¬ Formula.usesWitness witnessSort witnessIndex sentence) :
    Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex sentence =
      Formula.weakenFree (σ := HSignature σ) witnessSort sentence := by
  rw [Formula.eliminatePersistentWitness_emptyFree_of_not_uses
    (σ := σ) witnessSort witnessIndex sentence hNoWitness]
  change
    Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
        (VariableRenaming.empty : VariableRenaming [] [witnessSort]) sentence =
      Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
        (VariableRenaming.weaken witnessSort) sentence
  congr
  funext resultSort entry
  exact nomatch entry

/-! ## 闭句嵌入的不变性 -/

omit [DecidableEq σ.SortSymbol] in
@[simp] theorem Formula.usesWitness_fromSentence
    {free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (sentence : Sentence (HSignature σ)) :
    Formula.usesWitness witnessSort witnessIndex
        (Formula.fromSentence (free := free) sentence) ↔
      Formula.usesWitness witnessSort witnessIndex sentence := by
  cases free with
  | nil =>
      rfl
  | cons head tail =>
      change Formula.usesWitness witnessSort witnessIndex
          (sentence.renameMapped VariableRenaming.id
            (VariableRenaming.empty :
              VariableRenaming [] (head :: tail))) ↔
        Formula.usesWitness witnessSort witnessIndex sentence
      exact Formula.usesWitness_renameMapped (σ := σ)
        witnessSort witnessIndex VariableRenaming.id
        (VariableRenaming.empty :
          VariableRenaming [] (head :: tail)) sentence

/-- 不含指定见证的闭句在规范持久消去下保持原闭句嵌入。 -/
@[simp] theorem Formula.eliminatePersistentWitness_fromSentence_of_not_uses
    {free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (sentence : Sentence (HSignature σ))
    (hNoWitness :
      ¬ Formula.usesWitness witnessSort witnessIndex sentence) :
    Formula.eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
        (Formula.fromSentence (free := free) sentence) =
      Formula.fromSentence
        (free := FreshVariable.persistentContext free witnessSort) sentence := by
  have hEmbedded :
      ¬ Formula.usesWitness witnessSort witnessIndex
        (Formula.fromSentence (free := free) sentence) := by
    simpa using hNoWitness
  unfold Formula.eliminatePersistentWitness
  rw [Formula.eliminateWitness_eq_substituteMapped_of_not_uses
    (σ := σ) witnessSort witnessIndex
    (VariableSubstitution.boundId :
      VariableSubstitution (HSignature σ) [] []
        (FreshVariable.persistentContext free witnessSort))
    (persistentFreeSubstitution (σ := σ) (bound := [])
      (free := free) witnessSort)
    (persistentImage (σ := σ) (bound := []) (free := free) witnessSort)
    (formula := Formula.fromSentence (free := free) sentence) hEmbedded]
  cases free with
  | nil =>
      have hFree :
          (persistentFreeSubstitution (σ := σ) (bound := [])
            (free := []) witnessSort :
            VariableSubstitution (HSignature σ) [] [] [witnessSort]) =
          (VariableSubstitution.of_renaming (σ := HSignature σ)
            (bound := [])
            (VariableRenaming.empty : VariableRenaming []
              (FreshVariable.persistentContext [] witnessSort)) :
            VariableSubstitution (HSignature σ) [] []
              (FreshVariable.persistentContext [] witnessSort)) := by
        funext resultSort entry
        exact nomatch entry
      rw [hFree]
      change
        Formula.substituteMapped (σ := HSignature σ)
            VariableSubstitution.boundId
            (VariableSubstitution.of_renaming (σ := HSignature σ)
              (VariableRenaming.empty : VariableRenaming [] [witnessSort]))
            sentence =
          Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
            (VariableRenaming.empty : VariableRenaming [] [witnessSort])
            sentence
      exact Formula.substituteMapped_of_renaming
        (σ := HSignature σ)
        (VariableRenaming.empty : VariableRenaming [] [witnessSort]) sentence
  | cons head tail =>
      change
        (sentence.renameMapped VariableRenaming.id
          (VariableRenaming.empty :
            VariableRenaming [] (head :: tail))).substituteMapped
              VariableSubstitution.boundId
              (persistentFreeSubstitution (σ := σ) (bound := [])
                (free := head :: tail) witnessSort) =
          sentence.renameMapped VariableRenaming.id
            (VariableRenaming.empty : VariableRenaming []
              (FreshVariable.persistentContext (head :: tail)
                witnessSort))
      rw [← Formula.substituteMapped_of_renaming,
        Formula.substituteMapped_comp]
      have hBound :
          (fun {resultSort} (entry : Variable [] resultSort) =>
            (VariableSubstitution.boundId entry).substituteMapped
              VariableSubstitution.boundId
              (persistentFreeSubstitution (σ := σ) (bound := [])
                (free := head :: tail) witnessSort)) =
            (VariableSubstitution.boundId :
              VariableSubstitution (HSignature σ) [] []
                (FreshVariable.persistentContext (head :: tail)
                  witnessSort)) := by
        funext resultSort entry
        exact nomatch entry
      have hFree :
          (fun {resultSort} (entry : Variable [] resultSort) =>
            (VariableSubstitution.of_renaming (σ := HSignature σ)
              (bound := [])
              (VariableRenaming.empty :
                VariableRenaming [] (head :: tail)) entry).substituteMapped
                VariableSubstitution.boundId
                (persistentFreeSubstitution (σ := σ) (bound := [])
                  (free := head :: tail) witnessSort)) =
            (VariableSubstitution.of_renaming (σ := HSignature σ)
              (bound := [])
              (VariableRenaming.empty :
                VariableRenaming []
                  (FreshVariable.persistentContext (head :: tail)
                    witnessSort)) :
              VariableSubstitution (HSignature σ) [] []
                (FreshVariable.persistentContext (head :: tail)
                  witnessSort)) := by
        funext resultSort entry
        exact nomatch entry
      rw [hBound, hFree, Formula.substituteMapped_of_renaming]

/-! ## Hilbert 公理与推导搬运 -/

end HenkinSignature

open HenkinSignature

variable {σ : Signature.{u, v, w}}
variable [DecidableEq σ.SortSymbol]

namespace HilbertBaseAxiom

/-- 每个基础 Hilbert 公理在规范见证消去下仍是同一类公理。 -/
def eliminatePersistentWitness
    {free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {formula : OpenFormula (HSignature σ) free}
    (hAxiom : HilbertBaseAxiom (HSignature σ) formula) :
    HilbertBaseAxiom (HSignature σ)
      (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex formula) := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.implication_distribution (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex antecedent)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex middle)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex consequent))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | self_implication formula =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.self_implication (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | weakening formula extra =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.weakening (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex extra))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | contradiction formula conclusion =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.contradiction (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex conclusion))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | classical formula =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.classical (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | explosion formula conclusion =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.explosion (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex conclusion))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | case_analysis formula conclusion =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.case_analysis (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex conclusion))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | truth_intro =>
      exact .truth_intro
  | falsum_elimination conclusion =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.falsum_elimination (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex conclusion))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | negation_intro formula =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.negation_intro (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | negation_elimination formula =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.negation_elimination (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | conjunction_intro left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.conjunction_intro (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | conjunction_elim_left left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.conjunction_elim_left (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | conjunction_elim_right left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.conjunction_elim_right (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | disjunction_intro_left left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.disjunction_intro_left (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | disjunction_intro_right left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.disjunction_intro_right (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | disjunction_elimination left right conclusion =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.disjunction_elimination (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex conclusion))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | biconditional_intro left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.biconditional_intro (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | biconditional_elim_left left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.biconditional_elim_left (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | biconditional_elim_right left right =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.biconditional_elim_right (σ := HSignature σ)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness]
  | forall_specialization sort body term =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.forall_specialization (σ := HSignature σ) sort
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex body)
          (Term.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex term))
      simp
  | forall_distribution sort antecedent consequent =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.forall_distribution (σ := HSignature σ) sort
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex antecedent)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex consequent))
      simp
  | vacuous_forall sort formula =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.vacuous_forall (σ := HSignature σ) sort
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex formula))
      simp
  | exists_introduction sort body term =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.exists_introduction (σ := HSignature σ) sort
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex body)
          (Term.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex term))
      simp
  | exists_elimination sort body conclusion =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.exists_elimination (σ := HSignature σ) sort
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex body)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex conclusion))
      simp
  | equality_substitution sort left right body =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.equality_substitution (σ := HSignature σ) sort
          (Term.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex left)
          (Term.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex right)
          (Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex body))
      simp
  | equality_reflexivity term =>
      refine HilbertBaseAxiom.castFormula ?_
        (HilbertBaseAxiom.equality_reflexivity (σ := HSignature σ)
          (Term.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex term))
      simp [Formula.eliminatePersistentWitness, Formula.eliminateWitness,
        Term.eliminatePersistentWitness]

end HilbertBaseAxiom

namespace HilbertDerivation

/--
若理论公理不含指定见证常量，则整棵 Hilbert 推导可一次性把该常量解释为
free 上下文末位的持久变量。递归严格沿原推导树进行，不引入兼容推导系统。
-/
def eliminatePersistentWitness
    {T : Theory (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (hTheoryAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    {free : SortContext (HSignature σ)}
    {formula : OpenFormula (HSignature σ) free}
    (proof : HilbertDerivation T free formula) :
    HilbertDerivation T
      (FreshVariable.persistentContext free witnessSort)
      (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex formula) :=
  match proof with
  | logical_axiom hAxiom =>
      .logical_axiom
        (hAxiom.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex)
  | theory_axiom hTheory =>
      HilbertDerivation.castFormula
        (Formula.eliminatePersistentWitness_fromSentence_of_not_uses
          (σ := σ) witnessSort witnessIndex _
          (hTheoryAvoids hTheory)).symm
        (.theory_axiom hTheory)
  | modus_ponens hAntecedent hImplication =>
      .modus_ponens
        (eliminatePersistentWitness witnessSort witnessIndex
          hTheoryAvoids hAntecedent)
        (eliminatePersistentWitness witnessSort witnessIndex
          hTheoryAvoids hImplication)
  | forall_generalization hFormula =>
      HilbertDerivation.castFormula
        (Formula.eliminatePersistentWitness_forallFreeTop
          (σ := σ) witnessSort witnessIndex _ _).symm
        (HilbertDerivation.forall_generalization
          (eliminatePersistentWitness witnessSort witnessIndex
            hTheoryAvoids hFormula))
  | free_strengthening hFormula =>
      HilbertDerivation.free_strengthening
        (HilbertDerivation.castFormula
          (Formula.eliminatePersistentWitness_weakenFree
            (σ := σ) witnessSort witnessIndex _ _)
        (eliminatePersistentWitness witnessSort witnessIndex
          hTheoryAvoids hFormula))
  | free_substitution substitution hFormula =>
      HilbertDerivation.castFormula
        (Formula.eliminatePersistentWitness_substituteFree
          (σ := σ) witnessSort witnessIndex substitution _).symm
        (HilbertDerivation.free_substitution
          (eliminateSubstitution (σ := σ) witnessSort witnessIndex
            substitution)
          (eliminatePersistentWitness witnessSort witnessIndex
            hTheoryAvoids hFormula))

/--
若闭句本身不含指定见证，则消去整棵证明中的该见证后可立即删除新引入的持久变量，
得到同一闭句的新证明树。
-/
def eliminateSentenceWitness
    {T : Theory (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (hTheoryAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    {sentence : Sentence (HSignature σ)}
    (hSentenceAvoids :
      ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    (proof : HilbertDerivation T [] sentence) :
    HilbertDerivation T [] sentence := by
  have eliminated :=
    eliminatePersistentWitness (σ := σ) witnessSort witnessIndex
      hTheoryAvoids proof
  have hFormula :=
    Formula.eliminatePersistentWitness_sentence_of_not_uses
      (σ := σ) witnessSort witnessIndex sentence hSentenceAvoids
  exact .free_strengthening
    (HilbertDerivation.castFormula hFormula eliminated)

end HilbertDerivation

namespace Provable

/-- 公共可证性沿持久变量解释搬运。 -/
theorem eliminatePersistentWitness
    {T : Theory (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (hTheoryAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    {free : SortContext (HSignature σ)}
    {formula : OpenFormula (HSignature σ) free}
    (hFormula : Provable T formula) :
    Provable T
      (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex formula) := by
  rcases hFormula with ⟨proof⟩
  exact ⟨proof.eliminatePersistentWitness (σ := σ)
    witnessSort witnessIndex hTheoryAvoids⟩

end Provable

namespace Context

/--
若闭句上下文不含指定见证，则逐式消去恰好等于把整个上下文嵌入规范 fresh
变量上下文。
-/
theorem eliminatePersistentWitness_sentences
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (Γ : Context (HSignature σ) [])
    (hContextAvoids :
      ∀ sentence, sentence ∈ Γ →
        ¬ Formula.usesWitness witnessSort witnessIndex sentence) :
    Γ.map (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex) =
      FreshVariable.extendContext (σ := HSignature σ) witnessSort Γ := by
  induction Γ with
  | nil =>
      rfl
  | cons sentence rest ih =>
      have hSentence :=
        hContextAvoids sentence List.mem_cons_self
      have hRest :
          ∀ candidate, candidate ∈ rest →
            ¬ Formula.usesWitness witnessSort witnessIndex candidate := by
        intro candidate hCandidate
        exact hContextAvoids candidate
          (List.mem_cons_of_mem sentence hCandidate)
      change
        Formula.eliminatePersistentWitness (σ := σ)
            witnessSort witnessIndex sentence ::
            rest.map (Formula.eliminatePersistentWitness (σ := σ)
              witnessSort witnessIndex) =
          Formula.weakenFree (σ := HSignature σ) witnessSort sentence ::
            rest.map (Formula.weakenFree (σ := HSignature σ) witnessSort)
      rw [Formula.eliminatePersistentWitness_sentence_of_not_uses
          (σ := σ) witnessSort witnessIndex sentence hSentence]
      exact congrArg
        (List.cons
          (Formula.weakenFree (σ := HSignature σ) witnessSort sentence))
        (by simpa [FreshVariable.extendContext] using ih hRest)

/-- 持久见证消去与局部上下文的规范蕴含编译交换。 -/
@[simp] theorem eliminatePersistentWitness_discharge
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {free : SortContext (HSignature σ)}
    (Γ : Context (HSignature σ) free)
    (formula : OpenFormula (HSignature σ) free) :
    Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex (discharge Γ formula) =
      discharge
        (Γ.map (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex))
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex formula) := by
  induction Γ generalizing formula with
  | nil =>
      rfl
  | cons assumption rest ih =>
      simpa [Context.discharge] using
        ih (Formula.imp assumption formula)

end Context

namespace Derives

/-- 局部上下文与结论同步沿持久变量解释搬运。 -/
theorem eliminatePersistentWitness
    {T : Theory (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (hTheoryAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    {free : SortContext (HSignature σ)}
    {Γ : Context (HSignature σ) free}
    {formula : OpenFormula (HSignature σ) free}
    (hFormula : Derives T Γ formula) :
    Derives T
      (Γ.map (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex))
      (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex formula) := by
  change Provable T (Context.discharge Γ formula) at hFormula
  change Provable T
    (Context.discharge
      (Γ.map (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex))
      (Formula.eliminatePersistentWitness (σ := σ)
        witnessSort witnessIndex formula))
  rw [← Context.eliminatePersistentWitness_discharge]
  exact hFormula.eliminatePersistentWitness (σ := σ)
    witnessSort witnessIndex hTheoryAvoids

end Derives
end FirstOrder
end Logic
end YesMetaZFC
