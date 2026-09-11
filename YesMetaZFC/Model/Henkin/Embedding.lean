import YesMetaZFC.Model.Henkin.Transport
import YesMetaZFC.Model.FirstOrder.Soundness

/-!
# 原签名到 Henkin 签名的内在嵌入

本模块给出原签名语法、理论、Hilbert 推导和语义向 Henkin 常量扩张的统一搬运。
所有映射都直接作用于内在排序语法；没有 raw AST、良构检查或兼容包装。

反向保守性需要先把有限证明中的见证常量消去，单独放在后续模块中。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace HenkinSignature

universe u v w x

variable {σ : Signature.{u, v, w}}

/-! ## 重命名与替换的提升 -/

/-- 原签名重命名在 Henkin 扩张中的同一排序映射。 -/
def liftRenaming
    {sourceBound sourceFree targetBound targetFree : SortContext σ} :
    Renaming σ sourceBound sourceFree targetBound targetFree →
      Renaming (HSignature σ) sourceBound sourceFree targetBound targetFree
  | .id => .id
  | .map boundRenaming freeRenaming =>
      .map boundRenaming freeRenaming

/-- 原签名变量替换逐项提升到 Henkin 扩张。 -/
def liftVariableSubstitution
    {source targetBound targetFree : SortContext σ}
    (substitution : VariableSubstitution σ source targetBound targetFree) :
    VariableSubstitution (HSignature σ) source targetBound targetFree :=
  fun entry => liftTerm (substitution entry)

/-- 原签名替换逐项提升到 Henkin 扩张。 -/
def liftSubstitution
    {sourceBound sourceFree targetBound targetFree : SortContext σ} :
    Substitution σ sourceBound sourceFree targetBound targetFree →
      Substitution (HSignature σ) sourceBound sourceFree
        targetBound targetFree
  | .id => .id
  | .map boundSubstitution freeSubstitution =>
      .map (liftVariableSubstitution boundSubstitution)
        (liftVariableSubstitution freeSubstitution)

mutual

theorem liftTerm_renameMapped
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    {sort : σ.SortSymbol}
    (term : Term σ sourceBound sourceFree sort) :
    liftTerm (term.renameMapped boundRenaming freeRenaming) =
      Term.renameMapped (σ := HSignature σ)
        boundRenaming freeRenaming (liftTerm term) := by

  match term with
  | .bvar _ | .fvar _ => rfl
  | .app function arguments =>
      simpa only [Term.renameMapped, liftTerm_app] using
        congrArg (fun arguments => Term.app (σ := HSignature σ)
          (HenkinFunc.base function) arguments)
          (liftArguments_renameMapped boundRenaming freeRenaming arguments)

theorem liftArguments_renameMapped
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    liftArguments
        (arguments.renameMapped boundRenaming freeRenaming) =
      Arguments.renameMapped (σ := HSignature σ)
        boundRenaming freeRenaming (liftArguments arguments) := by

  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp only [Arguments.renameMapped, liftArguments_cons,
        liftTerm_renameMapped, liftArguments_renameMapped]

end

@[simp] theorem liftFormula_renameMapped
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    liftFormula
        (formula.renameMapped boundRenaming freeRenaming) =
      Formula.renameMapped (σ := HSignature σ)
        boundRenaming freeRenaming (liftFormula formula) := by
  induction formula generalizing targetBound targetFree <;>
    simp_all [liftFormula, Formula.renameMapped,
      liftTerm_renameMapped, liftArguments_renameMapped] <;> rfl

@[simp] theorem liftTerm_rename
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    liftTerm (term.rename ρ) =
      Term.rename (σ := HSignature σ) (liftRenaming ρ)
        (liftTerm term) := by
  cases ρ with
  | id => rfl
  | map boundRenaming freeRenaming =>
      exact liftTerm_renameMapped boundRenaming freeRenaming term

@[simp] theorem liftArguments_rename
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    liftArguments (arguments.rename ρ) =
      Arguments.rename (σ := HSignature σ) (liftRenaming ρ)
        (liftArguments arguments) := by
  cases ρ with
  | id => rfl
  | map boundRenaming freeRenaming =>
      exact liftArguments_renameMapped
        boundRenaming freeRenaming arguments

@[simp] theorem liftFormula_rename
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    liftFormula (formula.rename ρ) =
      Formula.rename (σ := HSignature σ) (liftRenaming ρ)
        (liftFormula formula) := by
  cases ρ with
  | id => rfl
  | map boundRenaming freeRenaming =>
      exact liftFormula_renameMapped
        boundRenaming freeRenaming formula

@[simp] theorem liftTerm_weakenBound
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol) (term : Term σ bound free sort) :
    liftTerm (term.weakenBound introduced) =
      Term.weakenBound (σ := HSignature σ) introduced
        (liftTerm term) := by
  change
    liftTerm (term.renameMapped
      (VariableRenaming.weaken introduced) VariableRenaming.id) =
    Term.renameMapped (σ := HSignature σ)
      (VariableRenaming.weaken introduced) VariableRenaming.id
      (liftTerm term)
  exact liftTerm_renameMapped
    (VariableRenaming.weaken introduced) VariableRenaming.id term

@[simp] theorem liftFormula_weakenBound
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (formula : Formula σ bound free) :
    liftFormula (formula.weakenBound introduced) =
      Formula.weakenBound (σ := HSignature σ) introduced
        (liftFormula formula) := by
  change
    liftFormula (formula.renameMapped
      (VariableRenaming.weaken introduced) VariableRenaming.id) =
    Formula.renameMapped (σ := HSignature σ)
      (VariableRenaming.weaken introduced) VariableRenaming.id
      (liftFormula formula)
  exact liftFormula_renameMapped
    (VariableRenaming.weaken introduced) VariableRenaming.id formula

@[simp] theorem liftVariableSubstitution_liftBound
    {source targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution :
      VariableSubstitution σ source targetBound targetFree) :
    (liftVariableSubstitution
        (VariableSubstitution.liftBound introduced substitution) :
      VariableSubstitution (HSignature σ) (introduced :: source)
        (introduced :: targetBound) targetFree) =
      (VariableSubstitution.liftBound (σ := HSignature σ) introduced
        (liftVariableSubstitution substitution) :
      VariableSubstitution (HSignature σ) (introduced :: source)
        (introduced :: targetBound) targetFree) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      exact liftTerm_weakenBound introduced (substitution previous)

@[simp] theorem liftVariableSubstitution_weakenBound
    {source targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution :
      VariableSubstitution σ source targetBound targetFree) :
    (liftVariableSubstitution
        (VariableSubstitution.weakenBound introduced substitution) :
      VariableSubstitution (HSignature σ) source
        (introduced :: targetBound) targetFree) =
      (VariableSubstitution.weakenBound (σ := HSignature σ) introduced
        (liftVariableSubstitution substitution) :
      VariableSubstitution (HSignature σ) source
        (introduced :: targetBound) targetFree) := by
  funext resultSort entry
  exact liftTerm_weakenBound introduced (substitution entry)

@[simp] theorem liftVariableSubstitution_boundId
    {bound free : SortContext σ} :
    (liftVariableSubstitution
        (VariableSubstitution.boundId (σ := σ)
          (bound := bound) (free := free)) :
      VariableSubstitution (HSignature σ) bound bound free) =
      (VariableSubstitution.boundId (σ := HSignature σ)
        (bound := bound) (free := free) :
      VariableSubstitution (HSignature σ) bound bound free) := by
  funext resultSort entry
  exact liftTerm_bvar entry

@[simp] theorem liftVariableSubstitution_freeId
    {bound free : SortContext σ} :
    (liftVariableSubstitution
        (VariableSubstitution.freeId (σ := σ)
          (bound := bound) (free := free)) :
      VariableSubstitution (HSignature σ) free bound free) =
      (VariableSubstitution.freeId (σ := HSignature σ)
        (bound := bound) (free := free) :
      VariableSubstitution (HSignature σ) free bound free) := by
  funext resultSort entry
  exact liftTerm_fvar entry

@[simp] theorem liftVariableSubstitution_instantiateTop
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    (liftVariableSubstitution
        (VariableSubstitution.instantiateTop replacement) :
      VariableSubstitution (HSignature σ) (sort :: bound) bound free) =
      (VariableSubstitution.instantiateTop (σ := HSignature σ)
        (liftTerm replacement) :
      VariableSubstitution (HSignature σ) (sort :: bound) bound free) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      exact liftTerm_bvar previous

@[simp] theorem liftVariableSubstitution_abstractBound
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (liftVariableSubstitution
        (VariableSubstitution.abstractBound (σ := σ)
          (bound := bound) (free := free) introduced) :
      VariableSubstitution (HSignature σ) bound
        (introduced :: bound) free) =
      (VariableSubstitution.abstractBound (σ := HSignature σ)
        (bound := bound) (free := free) introduced :
      VariableSubstitution (HSignature σ) bound
        (introduced :: bound) free) := by
  funext resultSort entry
  exact liftTerm_bvar (.there entry)

@[simp] theorem liftVariableSubstitution_abstractFreeTop
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    (liftVariableSubstitution
        (VariableSubstitution.abstractFreeTop (σ := σ)
          (bound := bound) (free := free) (sort := sort)) :
      VariableSubstitution (HSignature σ) (sort :: free)
        (sort :: bound) free) =
      (VariableSubstitution.abstractFreeTop (σ := HSignature σ)
        (bound := bound) (free := free) (sort := sort) :
      VariableSubstitution (HSignature σ) (sort :: free)
        (sort :: bound) free) := by
  funext resultSort entry
  cases entry with
  | here => rfl
  | there previous =>
      exact liftTerm_fvar previous

@[simp] theorem liftSubstitution_instantiateTop
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    liftSubstitution (Substitution.instantiateTop replacement) =
      Substitution.instantiateTop (σ := HSignature σ)
        (liftTerm replacement) := by
  change
    Substitution.map
        (liftVariableSubstitution
          (VariableSubstitution.instantiateTop replacement))
        (liftVariableSubstitution
          (VariableSubstitution.freeId (σ := σ))) =
      Substitution.map
        (VariableSubstitution.instantiateTop (σ := HSignature σ)
          (liftTerm replacement))
        (VariableSubstitution.freeId (σ := HSignature σ))
  rw [liftVariableSubstitution_instantiateTop,
    liftVariableSubstitution_freeId]

@[simp] theorem liftSubstitution_abstractFreeTop
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    liftSubstitution
        (Substitution.abstractFreeTop (σ := σ)
          (bound := bound) (free := free) (sort := sort)) =
      (Substitution.abstractFreeTop (σ := HSignature σ)
        (bound := bound) (free := free) (sort := sort)) := by
  change
    Substitution.map
        (liftVariableSubstitution
          (VariableSubstitution.abstractBound (σ := σ) sort))
        (liftVariableSubstitution
          (VariableSubstitution.abstractFreeTop (σ := σ))) =
      Substitution.map
        (VariableSubstitution.abstractBound (σ := HSignature σ) sort)
        (VariableSubstitution.abstractFreeTop (σ := HSignature σ))
  rw [liftVariableSubstitution_abstractBound,
    liftVariableSubstitution_abstractFreeTop]

@[simp] theorem liftSubstitution_free_map
    {bound sourceFree targetFree : SortContext σ}
    (substitution :
      VariableSubstitution σ sourceFree bound targetFree) :
    liftSubstitution (Substitution.free_map substitution) =
      Substitution.free_map (σ := HSignature σ)
        (liftVariableSubstitution substitution) := by
  change
    Substitution.map
        (liftVariableSubstitution
          (VariableSubstitution.boundId (σ := σ)))
        (liftVariableSubstitution substitution) =
      Substitution.map
        (VariableSubstitution.boundId (σ := HSignature σ))
        (liftVariableSubstitution substitution)
  rw [liftVariableSubstitution_boundId]

mutual

theorem liftTerm_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree)
    {sort : σ.SortSymbol}
    (term : Term σ sourceBound sourceFree sort) :
    liftTerm
        (term.substituteMapped boundSubstitution freeSubstitution) =
      Term.substituteMapped (σ := HSignature σ)
        (liftVariableSubstitution boundSubstitution)
        (liftVariableSubstitution freeSubstitution) (liftTerm term) := by

  match term with
  | .bvar _ | .fvar _ => rfl
  | .app function arguments =>
      simpa only [Term.substituteMapped, liftTerm_app] using
        congrArg (fun arguments => Term.app (σ := HSignature σ)
          (HenkinFunc.base function) arguments)
          (liftArguments_substituteMapped boundSubstitution freeSubstitution arguments)

theorem liftArguments_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    liftArguments
        (arguments.substituteMapped boundSubstitution freeSubstitution) =
      Arguments.substituteMapped (σ := HSignature σ)
        (liftVariableSubstitution boundSubstitution)
        (liftVariableSubstitution freeSubstitution)
        (liftArguments arguments) := by

  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp only [Arguments.substituteMapped, liftArguments_cons,
        liftTerm_substituteMapped, liftArguments_substituteMapped]

end

@[simp] theorem liftFormula_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    liftFormula
        (formula.substituteMapped boundSubstitution freeSubstitution) =
      Formula.substituteMapped (σ := HSignature σ)
        (liftVariableSubstitution boundSubstitution)
        (liftVariableSubstitution freeSubstitution)
        (liftFormula formula) := by
  induction formula generalizing targetBound targetFree <;>
    simp_all [liftFormula, Formula.substituteMapped, liftVariableSubstitution_liftBound,
      liftVariableSubstitution_weakenBound,
      liftTerm_substituteMapped, liftArguments_substituteMapped]

@[simp] theorem liftTerm_substitute
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    liftTerm (term.substitute τ) =
      Term.substitute (σ := HSignature σ) (liftSubstitution τ)
        (liftTerm term) := by
  cases τ with
  | id => rfl
  | map boundSubstitution freeSubstitution =>
      exact liftTerm_substituteMapped
        boundSubstitution freeSubstitution term

@[simp] theorem liftArguments_substitute
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    liftArguments (arguments.substitute τ) =
      Arguments.substitute (σ := HSignature σ) (liftSubstitution τ)
        (liftArguments arguments) := by
  cases τ with
  | id => rfl
  | map boundSubstitution freeSubstitution =>
      exact liftArguments_substituteMapped
        boundSubstitution freeSubstitution arguments

@[simp] theorem liftFormula_substitute
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    liftFormula (formula.substitute τ) =
      Formula.substitute (σ := HSignature σ) (liftSubstitution τ)
        (liftFormula formula) := by
  cases τ with
  | id => rfl
  | map boundSubstitution freeSubstitution =>
      exact liftFormula_substituteMapped
        boundSubstitution freeSubstitution formula

@[simp] theorem liftTerm_weakenFree
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol) (term : Term σ bound free sort) :
    liftTerm (term.weakenFree introduced) =
      Term.weakenFree (σ := HSignature σ) introduced
        (liftTerm term) := by
  change
    liftTerm (term.renameMapped VariableRenaming.id
      (VariableRenaming.weaken introduced)) =
    Term.renameMapped (σ := HSignature σ) VariableRenaming.id
      (VariableRenaming.weaken introduced) (liftTerm term)
  exact liftTerm_renameMapped VariableRenaming.id
    (VariableRenaming.weaken introduced) term

@[simp] theorem liftFormula_weakenFree
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (formula : Formula σ bound free) :
    liftFormula (formula.weakenFree introduced) =
      Formula.weakenFree (σ := HSignature σ) introduced
        (liftFormula formula) := by
  change
    liftFormula (formula.renameMapped VariableRenaming.id
      (VariableRenaming.weaken introduced)) =
    Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
      (VariableRenaming.weaken introduced) (liftFormula formula)
  exact liftFormula_renameMapped VariableRenaming.id
    (VariableRenaming.weaken introduced) formula

@[simp] theorem liftTerm_instantiateTop
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (term : Term σ (sort :: bound) free resultSort) :
    liftTerm (term.instantiateTop replacement) =
      Term.instantiateTop (σ := HSignature σ) (liftTerm term)
        (liftTerm replacement) := by
  simpa only [Term.instantiateTop,
    liftSubstitution_instantiateTop] using
    liftTerm_substitute
      (Substitution.instantiateTop replacement) term

@[simp] theorem liftFormula_instantiateTop
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (formula : Formula σ (sort :: bound) free) :
    liftFormula (formula.instantiateTop replacement) =
      Formula.instantiateTop (σ := HSignature σ) (liftTerm replacement)
        (liftFormula formula) := by
  simpa only [Formula.instantiateTop,
    liftSubstitution_instantiateTop] using
    liftFormula_substitute
      (Substitution.instantiateTop replacement) formula

@[simp] theorem liftFormula_substituteFree
    {sourceFree targetFree : SortContext σ}
    (substitution : VariableSubstitution σ sourceFree [] targetFree)
    (formula : OpenFormula σ sourceFree) :
    liftFormula (formula.substituteFree substitution) =
      Formula.substituteFree (σ := HSignature σ)
        (liftVariableSubstitution substitution) (liftFormula formula) := by
  simpa only [Formula.substituteFree,
    liftSubstitution_free_map] using
    liftFormula_substitute
      (Substitution.free_map substitution) formula

@[simp] theorem liftFormula_forallFreeTop
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : OpenFormula σ (sort :: free)) :
    liftFormula (body.forallFreeTop sort) =
      Formula.forallFreeTop (σ := HSignature σ) sort
        (liftFormula body) := by
  unfold Formula.forallFreeTop Formula.abstractFreeTop
  apply congrArg (Formula.forallE (σ := HSignature σ) sort)
  simpa only [liftSubstitution_abstractFreeTop] using
    liftFormula_substitute
      (Substitution.abstractFreeTop (σ := σ)) body

@[simp] theorem liftFormula_existsFreeTop
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : OpenFormula σ (sort :: free)) :
    liftFormula (body.existsFreeTop sort) =
      Formula.existsFreeTop (σ := HSignature σ) sort
        (liftFormula body) := by
  unfold Formula.existsFreeTop Formula.abstractFreeTop
  apply congrArg (Formula.existsE (σ := HSignature σ) sort)
  simpa only [liftSubstitution_abstractFreeTop] using
    liftFormula_substitute
      (Substitution.abstractFreeTop (σ := σ)) body

@[simp] theorem liftFormula_fromSentence
    {free : SortContext σ} (sentence : Sentence σ) :
    liftFormula (Formula.fromSentence (free := free) sentence) =
      Formula.fromSentence (σ := HSignature σ) (free := free)
        (liftFormula sentence) := by
  cases free with
  | nil => rfl
  | cons head tail =>
      change
        liftFormula (Formula.renameMapped VariableRenaming.id
          (VariableRenaming.empty : VariableRenaming [] (head :: tail))
          sentence) =
        Formula.renameMapped (σ := HSignature σ) VariableRenaming.id
          (VariableRenaming.empty : VariableRenaming [] (head :: tail))
          (liftFormula sentence)
      exact liftFormula_renameMapped VariableRenaming.id
        VariableRenaming.empty sentence

/-! ## 无见证性与理论提升 -/

mutual

theorem liftTerm_not_usesWitness
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    ¬ Term.usesWitness witnessSort witnessIndex (liftTerm term) := by

  match term with
  | .bvar _ | .fvar _ => simp [liftTerm, Term.usesWitness]
  | .app function arguments =>
      simpa [liftTerm, Term.usesWitness] using
        liftArguments_not_usesWitness witnessSort witnessIndex arguments

theorem liftArguments_not_usesWitness
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    ¬ Arguments.usesWitness witnessSort witnessIndex
      (liftArguments arguments) := by

  match arguments with
  | .nil => simp [liftArguments, Arguments.usesWitness]
  | .cons head tail =>
      simp only [liftArguments_cons, Arguments.usesWitness, not_or]
      exact ⟨liftTerm_not_usesWitness witnessSort witnessIndex head,
        liftArguments_not_usesWitness witnessSort witnessIndex tail⟩

end

theorem liftFormula_not_usesWitness
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    ¬ Formula.usesWitness witnessSort witnessIndex
      (liftFormula formula) := by
  induction formula <;>
    simp_all [liftFormula, Formula.usesWitness,
      liftTerm_not_usesWitness, liftArguments_not_usesWitness]

/-- 原理论在 Henkin 签名中的像。成员必须精确来自一条原理论闭句。 -/
def liftTheory (T : Theory σ) : Theory (HSignature σ) :=
  fun sentence =>
    ∃ source : Sentence σ, T source ∧ liftFormula source = sentence

@[simp] theorem mem_liftTheory_iff {T : Theory σ}
    {sentence : Sentence (HSignature σ)} :
    liftTheory T sentence ↔
      ∃ source : Sentence σ, T source ∧ liftFormula source = sentence :=
  Iff.rfl

theorem liftTheory_mem {T : Theory σ} {sentence : Sentence σ}
    (hSentence : T sentence) :
    liftTheory T (liftFormula sentence) :=
  ⟨sentence, hSentence, rfl⟩

theorem liftTheory_avoids
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {sentence : Sentence (HSignature σ)}
    (hSentence : liftTheory T sentence) :
    ∀ sort index, ¬ Formula.usesWitness sort index sentence := by
  rintro sort index
  rcases hSentence with ⟨source, _, rfl⟩
  exact liftFormula_not_usesWitness sort index source

/-! ## Hilbert 推导的正向提升 -/

namespace HilbertBaseAxiom

/-- 原签名逻辑公理逐构造提升为 Henkin 签名逻辑公理。 -/
def liftHenkin
    {free : SortContext σ} {formula : OpenFormula σ free}
    (hAxiom : HilbertBaseAxiom σ formula) :
    HilbertBaseAxiom (HSignature σ) (liftFormula formula) := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      exact .implication_distribution
        (liftFormula antecedent) (liftFormula middle)
        (liftFormula consequent)
  | self_implication formula =>
      exact .self_implication (liftFormula formula)
  | weakening formula extra =>
      exact .weakening (liftFormula formula) (liftFormula extra)
  | contradiction formula conclusion =>
      exact .contradiction (liftFormula formula) (liftFormula conclusion)
  | classical formula =>
      exact .classical (liftFormula formula)
  | explosion formula conclusion =>
      exact .explosion (liftFormula formula) (liftFormula conclusion)
  | case_analysis formula conclusion =>
      exact .case_analysis (liftFormula formula) (liftFormula conclusion)
  | truth_intro =>
      exact .truth_intro
  | falsum_elimination conclusion =>
      exact .falsum_elimination (liftFormula conclusion)
  | negation_intro formula =>
      exact .negation_intro (liftFormula formula)
  | negation_elimination formula =>
      exact .negation_elimination (liftFormula formula)
  | conjunction_intro left right =>
      exact .conjunction_intro (liftFormula left) (liftFormula right)
  | conjunction_elim_left left right =>
      exact .conjunction_elim_left (liftFormula left) (liftFormula right)
  | conjunction_elim_right left right =>
      exact .conjunction_elim_right (liftFormula left) (liftFormula right)
  | disjunction_intro_left left right =>
      exact .disjunction_intro_left (liftFormula left) (liftFormula right)
  | disjunction_intro_right left right =>
      exact .disjunction_intro_right (liftFormula left) (liftFormula right)
  | disjunction_elimination left right conclusion =>
      exact .disjunction_elimination
        (liftFormula left) (liftFormula right) (liftFormula conclusion)
  | biconditional_intro left right =>
      exact .biconditional_intro (liftFormula left) (liftFormula right)
  | biconditional_elim_left left right =>
      exact .biconditional_elim_left (liftFormula left) (liftFormula right)
  | biconditional_elim_right left right =>
      exact .biconditional_elim_right (liftFormula left) (liftFormula right)
  | forall_specialization sort body term =>
      have hFormula :
          liftFormula ((Formula.forallE sort body).imp
            (Formula.instantiateTop term body)) =
            Formula.imp
              (Formula.forallE (σ := HSignature σ) sort
                (liftFormula body))
              (Formula.instantiateTop (σ := HSignature σ)
                (liftTerm term) (liftFormula body)) := by
        simp only [liftFormula_imp, liftFormula_forallE,
          liftFormula_instantiateTop]
      exact HilbertBaseAxiom.castFormula hFormula.symm
        (HilbertBaseAxiom.forall_specialization
          (σ := HSignature σ) sort (liftFormula body) (liftTerm term))
  | forall_distribution sort antecedent consequent =>
      have hFormula :
          liftFormula
              ((Formula.forallFreeTop sort
                  (Formula.imp antecedent consequent)).imp
                ((Formula.forallFreeTop sort antecedent).imp
                  (Formula.forallFreeTop sort consequent))) =
            Formula.imp
              (Formula.forallFreeTop (σ := HSignature σ) sort
                (Formula.imp (liftFormula antecedent)
                  (liftFormula consequent)))
              (Formula.imp
                (Formula.forallFreeTop (σ := HSignature σ) sort
                  (liftFormula antecedent))
                (Formula.forallFreeTop (σ := HSignature σ) sort
                  (liftFormula consequent))) := by
        simp only [liftFormula_imp, liftFormula_forallFreeTop]

      exact HilbertBaseAxiom.castFormula hFormula.symm
        (HilbertBaseAxiom.forall_distribution
          (σ := HSignature σ) sort
          (liftFormula antecedent) (liftFormula consequent))
  | vacuous_forall sort formula =>
      have hFormula :
          liftFormula
              (Formula.imp formula
                (Formula.forallFreeTop sort
                  (Formula.weakenFree sort formula))) =
            Formula.imp (liftFormula formula)
              (Formula.forallFreeTop (σ := HSignature σ) sort
                (Formula.weakenFree (σ := HSignature σ) sort
                  (liftFormula formula))) := by
        simp only [liftFormula_imp, liftFormula_forallFreeTop]
        exact congrArg
          (fun inner => Formula.imp (liftFormula formula)
            (Formula.forallFreeTop (σ := HSignature σ) sort inner))
          (liftFormula_weakenFree (σ := σ) sort formula)
      exact HilbertBaseAxiom.castFormula hFormula.symm
        (HilbertBaseAxiom.vacuous_forall
          (σ := HSignature σ) sort (liftFormula formula))
  | exists_introduction sort body term =>
      have hFormula :
          liftFormula
              ((Formula.instantiateTop term body).imp
                (Formula.existsE sort body)) =
            Formula.imp
              (Formula.instantiateTop (σ := HSignature σ)
                (liftTerm term) (liftFormula body))
              (Formula.existsE (σ := HSignature σ) sort
                (liftFormula body)) := by
        simp only [liftFormula_imp, liftFormula_instantiateTop,
          liftFormula_existsE]
      exact HilbertBaseAxiom.castFormula hFormula.symm
        (HilbertBaseAxiom.exists_introduction
          (σ := HSignature σ) sort (liftFormula body) (liftTerm term))
  | exists_elimination sort body conclusion =>
      have hFormula :
          liftFormula
              ((Formula.forallFreeTop sort
                  (Formula.imp body
                    (Formula.weakenFree sort conclusion))).imp
                (Formula.imp (Formula.existsFreeTop sort body)
                  conclusion)) =
            Formula.imp
              (Formula.forallFreeTop (σ := HSignature σ) sort
                (Formula.imp (liftFormula body)
                  (Formula.weakenFree (σ := HSignature σ) sort
                    (liftFormula conclusion))))
              (Formula.imp
                (Formula.existsFreeTop (σ := HSignature σ) sort
                  (liftFormula body))
                (liftFormula conclusion)) := by
        simp only [liftFormula_imp, liftFormula_forallFreeTop,
          liftFormula_existsFreeTop]
        have hWeak :=
          liftFormula_weakenFree (σ := σ) sort conclusion
        have hInner :
            liftFormula
                (Formula.imp body (Formula.weakenFree sort conclusion)) =
              Formula.imp (liftFormula body)
                (Formula.weakenFree (σ := HSignature σ) sort
                  (liftFormula conclusion)) :=
          Eq.trans
            (liftFormula_imp (σ := σ) body
              (Formula.weakenFree sort conclusion))
            (congrArg (Formula.imp (liftFormula body)) hWeak)
        exact congrArg
          (fun inner => Formula.imp
            (Formula.forallFreeTop (σ := HSignature σ) sort inner)
            (Formula.imp
              (Formula.existsFreeTop (σ := HSignature σ) sort
                (liftFormula body))
              (liftFormula conclusion)))
          hInner
      exact HilbertBaseAxiom.castFormula hFormula.symm
        (HilbertBaseAxiom.exists_elimination
          (σ := HSignature σ) sort
          (liftFormula body) (liftFormula conclusion))
  | equality_substitution sort left right body =>
      have hFormula :
          liftFormula
              ((Formula.equal left right).imp
                ((Formula.instantiateTop left body).imp
                  (Formula.instantiateTop right body))) =
            Formula.imp
              (Formula.equal (σ := HSignature σ)
                (liftTerm left) (liftTerm right))
              (Formula.imp
                (Formula.instantiateTop (σ := HSignature σ)
                  (liftTerm left) (liftFormula body))
                (Formula.instantiateTop (σ := HSignature σ)
                  (liftTerm right) (liftFormula body))) := by
        simp only [liftFormula_imp, liftFormula_equal,
          liftFormula_instantiateTop]
      exact HilbertBaseAxiom.castFormula hFormula.symm
        (HilbertBaseAxiom.equality_substitution
          (σ := HSignature σ) sort
          (liftTerm left) (liftTerm right) (liftFormula body))
  | equality_reflexivity term =>
      exact .equality_reflexivity (liftTerm term)

end HilbertBaseAxiom

namespace HilbertDerivation

/-- 原签名 Hilbert 推导逐节点提升到 Henkin 签名。 -/
def liftHenkin {T : Theory σ}
    {free : SortContext σ} {formula : OpenFormula σ free} :
    HilbertDerivation T free formula →
      HilbertDerivation (liftTheory T) free (liftFormula formula)
  | .logical_axiom hAxiom =>
      .logical_axiom (HilbertBaseAxiom.liftHenkin hAxiom)
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.theory_axiom
      _ _ free sentence hTheory =>
      HilbertDerivation.castFormula
        (liftFormula_fromSentence (σ := σ) (free := free) sentence).symm
        (HilbertDerivation.theory_axiom
          (T := liftTheory T) (free := free)
          (liftTheory_mem hTheory))
  | .modus_ponens hAntecedent hImplication =>
      .modus_ponens (liftHenkin hAntecedent) (liftHenkin hImplication)
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.forall_generalization
      _ _ free sort formula hFormula =>
      HilbertDerivation.castFormula
        (liftFormula_forallFreeTop (σ := σ) sort formula).symm
        (HilbertDerivation.forall_generalization (liftHenkin hFormula))
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.free_strengthening
      _ _ free sort formula hFormula =>
      HilbertDerivation.free_strengthening
        (HilbertDerivation.castFormula
          (liftFormula_weakenFree (σ := σ) sort formula)
          (liftHenkin hFormula))
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.free_substitution
      _ _ sourceFree targetFree substitution formula hFormula =>
      HilbertDerivation.castFormula
        (liftFormula_substituteFree (σ := σ) substitution formula).symm
        (HilbertDerivation.free_substitution
          (liftVariableSubstitution substitution) (liftHenkin hFormula))

end HilbertDerivation

namespace Provable

/-- 原签名可证性提升到 Henkin 签名。 -/
theorem liftHenkin {T : Theory σ}
    {free : SortContext σ} {formula : OpenFormula σ free}
    (hFormula : Provable T formula) :
    Provable (liftTheory T) (liftFormula formula) := by
  rcases hFormula with ⟨proof⟩
  exact ⟨HilbertDerivation.liftHenkin proof⟩

end Provable

@[simp] theorem liftFormula_discharge
    {free : SortContext σ} (Γ : Context σ free)
    (formula : OpenFormula σ free) :
    liftFormula (Context.discharge Γ formula) =
      Context.discharge (Γ.map liftFormula) (liftFormula formula) := by
  induction Γ generalizing formula with
  | nil => rfl
  | cons assumption rest ih =>
      simpa [Context.discharge, liftFormula] using
        ih (.imp assumption formula)

namespace Derives

/-- 原签名局部推导提升到 Henkin 签名。 -/
theorem liftHenkin {T : Theory σ}
    {free : SortContext σ} {Γ : Context σ free}
    {formula : OpenFormula σ free}
    (hFormula : Derives T Γ formula) :
    Derives (liftTheory T) (Γ.map liftFormula) (liftFormula formula) := by
  change Provable T (Context.discharge Γ formula) at hFormula
  change Provable (liftTheory T)
    (Context.discharge (Γ.map liftFormula) (liftFormula formula))
  rw [← liftFormula_discharge]
  exact Provable.liftHenkin hFormula

end Derives

/-! ## 结构还原与语义保持 -/

/-- 忘掉 Henkin 见证常量，得到原签名结构。 -/
def henkinReduct
    (M : Structure.{u, max u v, w, x} (HSignature σ)) :
    Structure.{u, v, w, x} σ where
  Carrier := M.Carrier
  nonempty := M.nonempty
  funcInterp := fun function arguments =>
    M.funcInterp (.base function) arguments
  relInterp := M.relInterp

/-- Henkin 环境在原签名还原上的同载体环境。 -/
def henkinReductEnv
    {M : Structure.{u, max u v, w, x} (HSignature σ)}
    {bound free : SortContext σ} (env : Env M bound free) :
    Env (henkinReduct M) bound free where
  boundVal := env.boundVal
  freeVal := env.freeVal

@[simp] theorem henkinReductEnv_pushBound
    {M : Structure.{u, max u v, w, x} (HSignature σ)}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (env : Env M bound free) (value : M.Carrier sort) :
    henkinReductEnv (env.pushBound value) =
      (henkinReductEnv env).pushBound value :=
  by
    apply Env.ext
    · intro sort entry
      cases entry <;> rfl
    · intro sort entry
      rfl

@[simp] theorem henkinReductEnv_empty
    {M : Structure.{u, max u v, w, x} (HSignature σ)} :
    henkinReductEnv (Env.empty (M := M)) =
      Env.empty (M := henkinReduct M) :=
  by
    apply Env.ext
    · intro sort entry
      cases entry
    · intro sort entry
      cases entry

mutual

@[simp] theorem eval_liftTerm
    {M : Structure.{u, max u v, w, x} (HSignature σ)}
    {bound free : SortContext σ} (env : Env M bound free)
    {sort : σ.SortSymbol} (term : Term σ bound free sort) :
    Term.eval env (liftTerm term) =
      Term.eval (henkinReductEnv env) term := by

  match term with
  | .bvar _ | .fvar _ => rfl
  | .app function arguments =>
      change M.funcInterp (.base function) _ = M.funcInterp (.base function) _
      exact congrArg (M.funcInterp (.base function)) (eval_liftArguments env arguments)

@[simp] theorem eval_liftArguments
    {M : Structure.{u, max u v, w, x} (HSignature σ)}
    {bound free : SortContext σ} (env : Env M bound free)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    Arguments.eval env (liftArguments arguments) =
      Arguments.eval (henkinReductEnv env) arguments := by

  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp only [liftArguments_cons, Arguments.eval, eval_liftTerm, eval_liftArguments]
      rfl

end

@[simp] theorem satisfies_liftFormula
    {M : Structure.{u, max u v, w, x} (HSignature σ)}
    {bound free : SortContext σ} (env : Env M bound free)
    (formula : Formula σ bound free) :
    Formula.satisfies env (liftFormula formula) ↔
      Formula.satisfies (henkinReductEnv env) formula := by
  induction formula <;>
    simp_all only [liftFormula, Formula.satisfies, eval_liftTerm, eval_liftArguments,
      henkinReductEnv_pushBound] <;> rfl

@[simp] theorem trueIn_liftFormula
    {M : Structure.{u, max u v, w, x} (HSignature σ)}
    (sentence : Sentence σ) :
    Formula.TrueIn M (liftFormula sentence) ↔
      Formula.TrueIn (henkinReduct M) sentence := by
  change Formula.satisfies (Env.empty (M := M)) (liftFormula sentence) ↔
    Formula.satisfies (Env.empty (M := henkinReduct M)) sentence
  rw [satisfies_liftFormula, henkinReductEnv_empty]

/-- Henkin 模型满足提升理论时，其原签名还原满足原理论。 -/
theorem models_henkinReduct
    {T : Theory σ}
    {M : Structure.{u, max u v, w, x} (HSignature σ)}
    (hModels : Theory.Models M (liftTheory T)) :
    Theory.Models (henkinReduct M) T := by
  intro sentence hSentence
  exact (trueIn_liftFormula sentence).mp
    (hModels (liftFormula sentence) (liftTheory_mem hSentence))

/-- 原签名语义后承提升为 Henkin 签名语义后承。 -/
theorem semanticallyEntails_lift
    {T : Theory σ} {sentence : Sentence σ}
    (hEntails : Theory.SemanticallyEntails.{u, v, w, x} T sentence) :
    Theory.SemanticallyEntails.{u, max u v, w, x}
      (liftTheory T) (liftFormula sentence) := by
  intro M hModels
  exact (trueIn_liftFormula sentence).mpr
    (hEntails (henkinReduct M) (models_henkinReduct hModels))
end HenkinSignature
end FirstOrder
end Logic
end YesMetaZFC
