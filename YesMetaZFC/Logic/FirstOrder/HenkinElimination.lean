import YesMetaZFC.Logic.FirstOrder.HenkinSignature
import YesMetaZFC.Logic.FirstOrder.Derivation

/-!
# Henkin 见证常量消去

本模块把一个指定的 Henkin 常量直接消去为目标 free 上下文中的项。映射同时携带
bound/free 替换，因此后续可在不恢复自然数自由变量编号的前提下搬运推导。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}}
variable [DecidableEq σ.SortSymbol]

/-! ## 见证项与结构递归消去 -/

def witnessTerm (sort : σ.SortSymbol) (index : Nat) :
    OpenTerm (HSignature σ) [] sort :=
  Term.app (σ := HSignature σ) (HenkinFunc.witness sort index)
    (Arguments.nil : Arguments (HSignature σ) [] [] [])

omit [DecidableEq σ.SortSymbol] in
@[simp] theorem witnessTerm_def (sort : σ.SortSymbol) (index : Nat) :
    witnessTerm (σ := σ) sort index =
      (Term.app (σ := HSignature σ) (HenkinFunc.witness sort index)
        (Arguments.nil : Arguments (HSignature σ) [] [] [])) :=
  rfl

mutual

/-- 消去指定见证常量的项映射。 -/
def Term.eliminateWitness
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort) :
    {sort : σ.SortSymbol} →
      Term (HSignature σ) bound sourceFree sort →
        Term (HSignature σ) targetBound targetFree sort
  | _, .bvar entry => boundSubstitution entry
  | _, .fvar entry => freeSubstitution entry
  | _, .app function arguments =>
      match function with
      | .base baseFunction =>
          .app (HenkinFunc.base baseFunction)
            (Arguments.eliminateWitness witnessSort witnessIndex
              boundSubstitution freeSubstitution image arguments)
      | .witness sort index =>
          if h : sort = witnessSort ∧ index = witnessIndex then
            h.1 ▸ image
          else
            .app (HenkinFunc.witness sort index)
              (Arguments.eliminateWitness witnessSort witnessIndex
                boundSubstitution freeSubstitution image arguments)

/-- 消去指定见证常量的参数映射。 -/
def Arguments.eliminateWitness
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort) :
    {sorts : List σ.SortSymbol} →
      Arguments (HSignature σ) bound sourceFree sorts →
        Arguments (HSignature σ) targetBound targetFree sorts
  | _, .nil => .nil
  | _, .cons head tail =>
      .cons
        (Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image head)
        (Arguments.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image tail)

end

mutual

/-- 消去指定见证常量的公式映射。 -/
def Formula.eliminateWitness
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort) :
    Formula (HSignature σ) bound sourceFree →
      Formula (HSignature σ) targetBound targetFree
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments =>
      .rel relation (Arguments.eliminateWitness witnessSort witnessIndex
        boundSubstitution freeSubstitution image arguments)
  | .equal left right =>
      .equal
        (Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image left)
        (Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image right)
  | .neg body =>
      .neg (Formula.eliminateWitness witnessSort witnessIndex
        boundSubstitution freeSubstitution image body)
  | .conj left right =>
      .conj
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image left)
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image right)
  | .disj left right =>
      .disj
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image left)
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image right)
  | .imp left right =>
      .imp
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image left)
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image right)
  | .iff left right =>
      .iff
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image left)
        (Formula.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image right)
  | .forallE sort body =>
      .forallE sort
        (Formula.eliminateWitness witnessSort witnessIndex
          (VariableSubstitution.liftBound sort boundSubstitution)
          (VariableSubstitution.weakenBound sort freeSubstitution)
          (Term.weakenBound sort image) body)
  | .existsE sort body =>
      .existsE sort
        (Formula.eliminateWitness witnessSort witnessIndex
          (VariableSubstitution.liftBound sort boundSubstitution)
          (VariableSubstitution.weakenBound sort freeSubstitution)
          (Term.weakenBound sort image) body)

end

/-! ## 见证出现性与不变性合同 -/

mutual

def Term.usesWitness
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    {sort : σ.SortSymbol} → Term (HSignature σ) bound free sort → Prop
  | _, .bvar _ => False
  | _, .fvar _ => False
  | _, .app function arguments =>
      match function with
      | .base _ => Arguments.usesWitness witnessSort witnessIndex arguments
      | .witness sort index =>
          (sort = witnessSort ∧ index = witnessIndex) ∨
            Arguments.usesWitness witnessSort witnessIndex arguments

def Arguments.usesWitness
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    {sorts : List σ.SortSymbol} →
      Arguments (HSignature σ) bound free sorts → Prop
  | _, .nil => False
  | _, .cons head tail =>
      Term.usesWitness witnessSort witnessIndex head ∨
        Arguments.usesWitness witnessSort witnessIndex tail

end

def Formula.usesWitness
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    Formula (HSignature σ) bound free → Prop
  | .falsum => False
  | .truth => False
  | .rel _ arguments =>
      Arguments.usesWitness witnessSort witnessIndex arguments
  | .equal left right =>
      Term.usesWitness witnessSort witnessIndex left ∨
        Term.usesWitness witnessSort witnessIndex right
  | .neg body => Formula.usesWitness witnessSort witnessIndex body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      Formula.usesWitness witnessSort witnessIndex left ∨
        Formula.usesWitness witnessSort witnessIndex right
  | .forallE _ body
  | .existsE _ body =>
      Formula.usesWitness witnessSort witnessIndex body

/-! ## 见证编号的绝对结构上界 -/

mutual

/-- 项中全部 Henkin 见证编号的严格上界。 -/
def Term.witnessBound
    {bound free : SortContext (HSignature σ)} :
    {sort : σ.SortSymbol} → Term (HSignature σ) bound free sort → Nat
  | _, .bvar _ => 0
  | _, .fvar _ => 0
  | _, .app (HenkinFunc.base _) arguments =>
      Arguments.witnessBound arguments
  | _, .app (HenkinFunc.witness _ index) arguments =>
      Nat.max (index + 1) (Arguments.witnessBound arguments)

/-- 异质参数列中全部 Henkin 见证编号的严格上界。 -/
def Arguments.witnessBound
    {bound free : SortContext (HSignature σ)} :
    {sorts : List σ.SortSymbol} →
      Arguments (HSignature σ) bound free sorts → Nat
  | _, .nil => 0
  | _, .cons head tail =>
      Nat.max (Term.witnessBound head) (Arguments.witnessBound tail)

end

/-- 公式中全部 Henkin 见证编号的严格上界。 -/
def Formula.witnessBound
    {bound free : SortContext (HSignature σ)} :
    Formula (HSignature σ) bound free → Nat
  | .falsum => 0
  | .truth => 0
  | .rel _ arguments => Arguments.witnessBound arguments
  | .equal left right =>
      Nat.max (Term.witnessBound left) (Term.witnessBound right)
  | .neg body => Formula.witnessBound body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      Nat.max (Formula.witnessBound left) (Formula.witnessBound right)
  | .forallE _ body
  | .existsE _ body => Formula.witnessBound body

omit [DecidableEq σ.SortSymbol] in
mutual

/-- 达到项的结构上界后，任意排序的该编号见证都不再出现。 -/
theorem Term.not_usesWitness_of_witnessBound_le
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    {sort : σ.SortSymbol} →
      (term : Term (HSignature σ) bound free sort) →
      Term.witnessBound term ≤ witnessIndex →
        ¬ Term.usesWitness witnessSort witnessIndex term
  | _, .bvar _, _ => by
      simp [Term.usesWitness]
  | _, .fvar _, _ => by
      simp [Term.usesWitness]
  | _, .app (HenkinFunc.base _) arguments, hBound => by
      change ¬ Arguments.usesWitness witnessSort witnessIndex arguments
      exact Arguments.not_usesWitness_of_witnessBound_le
        witnessSort witnessIndex arguments hBound
  | _, .app (HenkinFunc.witness sort index) arguments, hBound => by
      intro hUses
      change (sort = witnessSort ∧ index = witnessIndex) ∨
        Arguments.usesWitness witnessSort witnessIndex arguments at hUses
      have hIndex : index < witnessIndex :=
        Nat.lt_of_succ_le
          (Nat.le_trans (Nat.le_max_left (index + 1)
            (Arguments.witnessBound arguments)) hBound)
      rcases hUses with hHead | hArguments
      · exact (Nat.ne_of_lt hIndex) hHead.2
      · exact Arguments.not_usesWitness_of_witnessBound_le
          witnessSort witnessIndex arguments
          (Nat.le_trans (Nat.le_max_right (index + 1)
            (Arguments.witnessBound arguments)) hBound) hArguments

/-- 达到参数列的结构上界后，任意排序的该编号见证都不再出现。 -/
theorem Arguments.not_usesWitness_of_witnessBound_le
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments (HSignature σ) bound free sorts) →
      Arguments.witnessBound arguments ≤ witnessIndex →
        ¬ Arguments.usesWitness witnessSort witnessIndex arguments
  | _, .nil, _ => by
      simp [Arguments.usesWitness]
  | _, .cons head tail, hBound => by
      intro hUses
      change Term.usesWitness witnessSort witnessIndex head ∨
        Arguments.usesWitness witnessSort witnessIndex tail at hUses
      rcases hUses with hHead | hTail
      · exact Term.not_usesWitness_of_witnessBound_le
          witnessSort witnessIndex head
          (Nat.le_trans (Nat.le_max_left (Term.witnessBound head)
            (Arguments.witnessBound tail)) hBound) hHead
      · exact Arguments.not_usesWitness_of_witnessBound_le
          witnessSort witnessIndex tail
          (Nat.le_trans (Nat.le_max_right (Term.witnessBound head)
            (Arguments.witnessBound tail)) hBound) hTail

end

omit [DecidableEq σ.SortSymbol] in
/-- 达到公式的结构上界后，任意排序的该编号见证都不再出现。 -/
theorem Formula.not_usesWitness_of_witnessBound_le
    {bound free : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat) :
    (formula : Formula (HSignature σ) bound free) →
    Formula.witnessBound formula ≤ witnessIndex →
      ¬ Formula.usesWitness witnessSort witnessIndex formula
  | .falsum, _ => by simp [Formula.usesWitness]
  | .truth, _ => by simp [Formula.usesWitness]
  | .rel _ arguments, hBound =>
      Arguments.not_usesWitness_of_witnessBound_le
        witnessSort witnessIndex arguments hBound
  | .equal left right, hBound => by
      intro hUses
      rcases hUses with hLeft | hRight
      · exact Term.not_usesWitness_of_witnessBound_le
          witnessSort witnessIndex left
          (Nat.le_trans (Nat.le_max_left (Term.witnessBound left)
            (Term.witnessBound right)) hBound) hLeft
      · exact Term.not_usesWitness_of_witnessBound_le
          witnessSort witnessIndex right
          (Nat.le_trans (Nat.le_max_right (Term.witnessBound left)
            (Term.witnessBound right)) hBound) hRight
  | .neg body, hBound =>
      Formula.not_usesWitness_of_witnessBound_le
        witnessSort witnessIndex body hBound
  | .conj left right, hBound
  | .disj left right, hBound
  | .imp left right, hBound
  | .iff left right, hBound => by
      intro hUses
      rcases hUses with hLeft | hRight
      · exact Formula.not_usesWitness_of_witnessBound_le
          witnessSort witnessIndex left
          (Nat.le_trans (Nat.le_max_left (Formula.witnessBound left)
            (Formula.witnessBound right)) hBound) hLeft
      · exact Formula.not_usesWitness_of_witnessBound_le
          witnessSort witnessIndex right
          (Nat.le_trans (Nat.le_max_right (Formula.witnessBound left)
            (Formula.witnessBound right)) hBound) hRight
  | .forallE _ body, hBound
  | .existsE _ body, hBound =>
      Formula.not_usesWitness_of_witnessBound_le
        witnessSort witnessIndex body hBound

/-! ## 见证出现性对重命名的不变性 -/

omit [DecidableEq σ.SortSymbol] in
mutual

@[simp] theorem Term.usesWitness_renameMapped
    {sourceBound sourceFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree) :
    {sort : σ.SortSymbol} →
      (term : Term (HSignature σ) sourceBound sourceFree sort) →
      Term.usesWitness witnessSort witnessIndex
          (term.renameMapped boundRenaming freeRenaming) ↔
        Term.usesWitness witnessSort witnessIndex term
  | _, .bvar _ => Iff.rfl
  | _, .fvar _ => Iff.rfl
  | _, .app (HenkinFunc.base function) arguments => by
      simp [Term.renameMapped, Term.usesWitness,
        Arguments.usesWitness_renameMapped]
  | _, .app (HenkinFunc.witness sort index) arguments => by
      simp [Term.renameMapped, Term.usesWitness,
        Arguments.usesWitness_renameMapped]

@[simp] theorem Arguments.usesWitness_renameMapped
    {sourceBound sourceFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments (HSignature σ) sourceBound sourceFree sorts) →
      Arguments.usesWitness witnessSort witnessIndex
          (arguments.renameMapped boundRenaming freeRenaming) ↔
        Arguments.usesWitness witnessSort witnessIndex arguments
  | _, .nil => Iff.rfl
  | _, .cons head tail => by
      simp [Arguments.renameMapped, Arguments.usesWitness,
        Term.usesWitness_renameMapped,
        Arguments.usesWitness_renameMapped]

end

omit [DecidableEq σ.SortSymbol] in
@[simp] theorem Formula.usesWitness_renameMapped
    {sourceBound sourceFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree) :
    (formula : Formula (HSignature σ) sourceBound sourceFree) →
    Formula.usesWitness witnessSort witnessIndex
        (formula.renameMapped boundRenaming freeRenaming) ↔
      Formula.usesWitness witnessSort witnessIndex formula
  | .falsum => Iff.rfl
  | .truth => Iff.rfl
  | .rel relation arguments => by
      simp [Formula.renameMapped, Formula.usesWitness]
  | .equal left right => by
      simp [Formula.renameMapped, Formula.usesWitness]
  | .neg body => by
      simp [Formula.renameMapped, Formula.usesWitness,
        Formula.usesWitness_renameMapped]
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right => by
      simp [Formula.renameMapped, Formula.usesWitness,
        Formula.usesWitness_renameMapped]
  | .forallE sort body
  | .existsE sort body => by
      simp [Formula.renameMapped, Formula.usesWitness,
        Formula.usesWitness_renameMapped]

mutual

theorem Term.eliminateWitness_eq_substituteMapped_of_not_uses
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {sort : σ.SortSymbol} (term : Term (HSignature σ) bound sourceFree sort)
    (hNoWitness : ¬ Term.usesWitness witnessSort witnessIndex term) :
    Term.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image term =
      term.substituteMapped boundSubstitution freeSubstitution := by
  match term with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app (HenkinFunc.base function) arguments =>
      simp only [Term.eliminateWitness, Term.substituteMapped]
      rw [Arguments.eliminateWitness_eq_substituteMapped_of_not_uses
        witnessSort witnessIndex _ _ _ arguments hNoWitness]
  | .app (HenkinFunc.witness termSort termIndex) arguments =>
      have hParts : ¬ (termSort = witnessSort ∧ termIndex = witnessIndex) ∧
          ¬ Arguments.usesWitness witnessSort witnessIndex arguments := by
        simpa only [Term.usesWitness, not_or] using hNoWitness
      simp only [Term.eliminateWitness, Term.substituteMapped, dif_neg hParts.1]
      rw [Arguments.eliminateWitness_eq_substituteMapped_of_not_uses
        witnessSort witnessIndex _ _ _ arguments hParts.2]

theorem Arguments.eliminateWitness_eq_substituteMapped_of_not_uses
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) bound sourceFree sorts)
    (hNoWitness : ¬ Arguments.usesWitness witnessSort witnessIndex arguments) :
    Arguments.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image arguments =
      arguments.substituteMapped boundSubstitution freeSubstitution := by
  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp only [Arguments.usesWitness, not_or] at hNoWitness
      simp only [Arguments.eliminateWitness, Arguments.substituteMapped]
      rw [Term.eliminateWitness_eq_substituteMapped_of_not_uses
        witnessSort witnessIndex _ _ _ head hNoWitness.1,
        Arguments.eliminateWitness_eq_substituteMapped_of_not_uses
        witnessSort witnessIndex _ _ _ tail hNoWitness.2]

end

theorem Formula.eliminateWitness_eq_substituteMapped_of_not_uses
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {formula : Formula (HSignature σ) bound sourceFree}
    (hNoWitness : ¬ Formula.usesWitness witnessSort witnessIndex formula) :
    Formula.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image formula =
      formula.substituteMapped boundSubstitution freeSubstitution := by
  induction formula generalizing targetBound targetFree image <;>
    simp_all [Formula.eliminateWitness, Formula.substituteMapped, Formula.usesWitness,
      Term.eliminateWitness_eq_substituteMapped_of_not_uses,
      Arguments.eliminateWitness_eq_substituteMapped_of_not_uses]

@[simp] theorem Formula.eliminateWitness_falsum
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort) :
    Formula.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image
      (.falsum : Formula (HSignature σ) bound sourceFree) =
      (.falsum : Formula (HSignature σ) targetBound targetFree) := by
  simp [Formula.eliminateWitness]

@[simp] theorem Formula.eliminateWitness_truth
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort) :
    Formula.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image
      (.truth : Formula (HSignature σ) bound sourceFree) =
      (.truth : Formula (HSignature σ) targetBound targetFree) := by
  simp [Formula.eliminateWitness]

/-- 见证消去穿过一个新 bound 变量；该自然性是所有公式 binder 融合的共同底座。 -/
theorem Term.eliminateWitness_weakenBound
    {sourceBound sourceFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      sourceBound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    (introduced : σ.SortSymbol) {sort : σ.SortSymbol}
    (term : Term (HSignature σ) sourceBound sourceFree sort) :
    Term.eliminateWitness witnessSort witnessIndex
      (VariableSubstitution.liftBound (σ := HSignature σ) introduced
        boundSubstitution)
      (VariableSubstitution.weakenBound (σ := HSignature σ) introduced
        freeSubstitution)
      (Term.weakenBound (σ := HSignature σ) introduced image)
      (Term.weakenBound (σ := HSignature σ) introduced term) =
      (Term.eliminateWitness witnessSort witnessIndex boundSubstitution
        freeSubstitution image term).weakenBound (σ := HSignature σ) introduced := by
  exact Term.rec
    (motive_1 := fun _ term =>
      ∀ {targetBound targetFree : SortContext (HSignature σ)}
        (boundSubstitution : VariableSubstitution (HSignature σ)
          sourceBound targetBound targetFree)
        (freeSubstitution : VariableSubstitution (HSignature σ)
          sourceFree targetBound targetFree)
        (image : Term (HSignature σ) targetBound targetFree witnessSort),
        Term.eliminateWitness witnessSort witnessIndex
          (VariableSubstitution.liftBound (σ := HSignature σ) introduced
            boundSubstitution)
          (VariableSubstitution.weakenBound (σ := HSignature σ) introduced
            freeSubstitution)
          (Term.weakenBound (σ := HSignature σ) introduced image)
          (Term.weakenBound (σ := HSignature σ) introduced term) =
          (Term.eliminateWitness witnessSort witnessIndex boundSubstitution
            freeSubstitution image term).weakenBound
              (σ := HSignature σ) introduced)
    (motive_2 := fun _ arguments =>
      ∀ {targetBound targetFree : SortContext (HSignature σ)}
        (boundSubstitution : VariableSubstitution (HSignature σ)
          sourceBound targetBound targetFree)
        (freeSubstitution : VariableSubstitution (HSignature σ)
          sourceFree targetBound targetFree)
        (image : Term (HSignature σ) targetBound targetFree witnessSort),
        Arguments.eliminateWitness witnessSort witnessIndex
          (VariableSubstitution.liftBound (σ := HSignature σ) introduced
            boundSubstitution)
          (VariableSubstitution.weakenBound (σ := HSignature σ) introduced
            freeSubstitution)
          (Term.weakenBound (σ := HSignature σ) introduced image)
          (Arguments.weakenBound (σ := HSignature σ) introduced arguments) =
          (Arguments.eliminateWitness witnessSort witnessIndex boundSubstitution
            freeSubstitution image arguments).weakenBound
              (σ := HSignature σ) introduced)
    (fun entry targetBound targetFree boundSubstitution freeSubstitution image => by
      simp [Term.eliminateWitness, VariableSubstitution.liftBound])
    (fun entry targetBound targetFree boundSubstitution freeSubstitution image => by
      simp [Term.eliminateWitness, VariableSubstitution.weakenBound])
    (fun function arguments ih targetBound targetFree boundSubstitution
        freeSubstitution image => by
      cases function with
      | base baseFunction =>
          simp [Term.eliminateWitness, ih]
      | witness termSort termIndex =>
          by_cases hMatch :
              termSort = witnessSort ∧ termIndex = witnessIndex
          · rcases hMatch with ⟨rfl, rfl⟩
            simp [Term.eliminateWitness]
          · simp [Term.eliminateWitness, hMatch, ih])
    (fun {targetBound targetFree} boundSubstitution freeSubstitution image => rfl)
    (fun {sort} {sorts} head tail ihHead ihTail
        {targetBound targetFree} boundSubstitution freeSubstitution image => by
      simp [Arguments.eliminateWitness, ihHead, ihTail])
    term boundSubstitution freeSubstitution image

mutual

theorem Term.eliminateWitness_instantiateTop
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {sort resultSort : σ.SortSymbol}
    (replacement : Term (HSignature σ) bound sourceFree sort)
    (body : Term (HSignature σ) (sort :: bound) sourceFree resultSort) :
    Term.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image (body.instantiateTop replacement) =
      (Term.eliminateWitness witnessSort witnessIndex
        (VariableSubstitution.liftBound (σ := HSignature σ) sort boundSubstitution)
        (VariableSubstitution.weakenBound (σ := HSignature σ) sort freeSubstitution)
        (Term.weakenBound (σ := HSignature σ) sort image) body).instantiateTop
        (Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image replacement) := by
  match body with
  | .bvar entry =>
      cases entry with
      | here => simp [Term.eliminateWitness, VariableSubstitution.liftBound]
      | there previous => simp [Term.eliminateWitness, VariableSubstitution.liftBound]
  | .fvar entry => simp [Term.eliminateWitness, VariableSubstitution.weakenBound]
  | .app (HenkinFunc.base function) arguments =>
      simp only [Term.eliminateWitness, Term.instantiateTop_app,
        Arguments.eliminateWitness_instantiateTop]
  | .app (HenkinFunc.witness termSort termIndex) arguments =>
      by_cases hMatch : termSort = witnessSort ∧ termIndex = witnessIndex
      · rcases hMatch with ⟨rfl, rfl⟩
        simp [Term.eliminateWitness, Term.instantiateTop_app]
      · simp only [Term.eliminateWitness, Term.instantiateTop_app, dif_neg hMatch,
          Arguments.eliminateWitness_instantiateTop]

theorem Arguments.eliminateWitness_instantiateTop
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (replacement : Term (HSignature σ) bound sourceFree sort)
    (arguments : Arguments (HSignature σ) (sort :: bound) sourceFree sorts) :
    Arguments.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image (arguments.instantiateTop replacement) =
      (Arguments.eliminateWitness witnessSort witnessIndex
        (VariableSubstitution.liftBound (σ := HSignature σ) sort boundSubstitution)
        (VariableSubstitution.weakenBound (σ := HSignature σ) sort freeSubstitution)
        (Term.weakenBound (σ := HSignature σ) sort image) arguments).instantiateTop
        (Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image replacement) := by
  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp only [Arguments.eliminateWitness, Arguments.instantiateTop_cons,
        Term.eliminateWitness_instantiateTop, Arguments.eliminateWitness_instantiateTop]

/-- 见证消去后继续执行普通替换，可融合为一次见证消去遍历。 -/
theorem Term.eliminateWitness_substituteMapped
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      sourceBound middleBound middleFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree middleBound middleFree)
    (image : Term (HSignature σ) middleBound middleFree witnessSort)
    (outerBound : VariableSubstitution (HSignature σ)
      middleBound targetBound targetFree)
    (outerFree : VariableSubstitution (HSignature σ)
      middleFree targetBound targetFree)
    {sort : σ.SortSymbol}
    (term : Term (HSignature σ) sourceBound sourceFree sort) :
    (Term.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image term).substituteMapped outerBound outerFree =
      Term.eliminateWitness witnessSort witnessIndex
        (fun entry => (boundSubstitution entry).substituteMapped
          outerBound outerFree)
        (fun entry => (freeSubstitution entry).substituteMapped
          outerBound outerFree)
        (image.substituteMapped outerBound outerFree) term := by
  match term with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app (HenkinFunc.base function) arguments =>
      simp only [Term.eliminateWitness, Term.substituteMapped,
        Arguments.eliminateWitness_substituteMapped]
  | .app (HenkinFunc.witness termSort termIndex) arguments =>
      by_cases hMatch : termSort = witnessSort ∧ termIndex = witnessIndex
      · rcases hMatch with ⟨rfl, rfl⟩
        simp [Term.eliminateWitness]
      · simp only [Term.eliminateWitness, Term.substituteMapped, dif_neg hMatch,
          Arguments.eliminateWitness_substituteMapped]

/-- 参数列上的见证消去同样与后续普通替换融合。 -/
theorem Arguments.eliminateWitness_substituteMapped
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      sourceBound middleBound middleFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree middleBound middleFree)
    (image : Term (HSignature σ) middleBound middleFree witnessSort)
    (outerBound : VariableSubstitution (HSignature σ)
      middleBound targetBound targetFree)
    (outerFree : VariableSubstitution (HSignature σ)
      middleFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) sourceBound sourceFree sorts) :
    (Arguments.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image arguments).substituteMapped outerBound outerFree =
      Arguments.eliminateWitness witnessSort witnessIndex
        (fun entry => (boundSubstitution entry).substituteMapped
          outerBound outerFree)
        (fun entry => (freeSubstitution entry).substituteMapped
          outerBound outerFree)
        (image.substituteMapped outerBound outerFree) arguments := by
  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp only [Arguments.eliminateWitness, Arguments.substituteMapped,
        Term.eliminateWitness_substituteMapped, Arguments.eliminateWitness_substituteMapped]

/-- 先执行普通替换再消去见证，可融合为一次见证消去遍历。 -/
theorem Term.eliminateWitness_substituteMapped_source
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (innerBound : VariableSubstitution (HSignature σ)
      sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution (HSignature σ)
      sourceFree middleBound middleFree)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      middleBound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      middleFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {sort : σ.SortSymbol}
    (term : Term (HSignature σ) sourceBound sourceFree sort) :
    Term.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image
      (term.substituteMapped innerBound innerFree) =
      Term.eliminateWitness witnessSort witnessIndex
        (fun entry => Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image (innerBound entry))
        (fun entry => Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image (innerFree entry))
        image term := by
  match term with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app (HenkinFunc.base function) arguments =>
      simp only [Term.eliminateWitness, Term.substituteMapped,
        Arguments.eliminateWitness_substituteMapped_source]
  | .app (HenkinFunc.witness termSort termIndex) arguments =>
      by_cases hMatch : termSort = witnessSort ∧ termIndex = witnessIndex
      · rcases hMatch with ⟨rfl, rfl⟩
        simp [Term.eliminateWitness, Term.substituteMapped]
      · simp only [Term.eliminateWitness, Term.substituteMapped, dif_neg hMatch,
          Arguments.eliminateWitness_substituteMapped_source]

/-- 参数列上先替换后消去的源端融合律。 -/
theorem Arguments.eliminateWitness_substituteMapped_source
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (innerBound : VariableSubstitution (HSignature σ)
      sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution (HSignature σ)
      sourceFree middleBound middleFree)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      middleBound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      middleFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) sourceBound sourceFree sorts) :
    Arguments.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image
      (arguments.substituteMapped innerBound innerFree) =
      Arguments.eliminateWitness witnessSort witnessIndex
        (fun entry => Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image (innerBound entry))
        (fun entry => Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image (innerFree entry))
        image arguments := by
  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp only [Arguments.eliminateWitness, Arguments.substituteMapped,
        Term.eliminateWitness_substituteMapped_source, Arguments.eliminateWitness_substituteMapped_source]

/-- 公式上先替换后消去的源端融合律。 -/
theorem Formula.eliminateWitness_substituteMapped_source
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (innerBound : VariableSubstitution (HSignature σ)
      sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution (HSignature σ)
      sourceFree middleBound middleFree)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      middleBound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      middleFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    (formula : Formula (HSignature σ) sourceBound sourceFree) :
    Formula.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image
      (formula.substituteMapped innerBound innerFree) =
      Formula.eliminateWitness witnessSort witnessIndex
        (fun entry => Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image (innerBound entry))
        (fun entry => Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image (innerFree entry))
        image formula := by
  induction formula generalizing middleBound middleFree targetBound targetFree with
  | falsum => rfl
  | truth => rfl
  | rel relation arguments =>
      simp [Formula.eliminateWitness, Formula.substituteMapped,
        Arguments.eliminateWitness_substituteMapped_source]
  | equal left right =>
      simp [Formula.eliminateWitness, Formula.substituteMapped,
        Term.eliminateWitness_substituteMapped_source]
  | neg body ih =>
      simp [Formula.eliminateWitness, Formula.substituteMapped, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [Formula.eliminateWitness, Formula.substituteMapped,
        ihLeft, ihRight]
  | forallE introduced body ih
  | existsE introduced body ih =>
      simp only [Formula.eliminateWitness, Formula.substituteMapped]
      congr 1
      rw [ih
        (VariableSubstitution.liftBound (σ := HSignature σ) introduced
          innerBound)
        (VariableSubstitution.weakenBound (σ := HSignature σ) introduced
          innerFree)
        (VariableSubstitution.liftBound (σ := HSignature σ) introduced
          boundSubstitution)
        (VariableSubstitution.weakenBound (σ := HSignature σ) introduced
          freeSubstitution)
        (Term.weakenBound (σ := HSignature σ) introduced image)]
      congr
      · funext resultSort entry
        cases entry with
        | here => rfl
        | there previous =>
            exact Term.eliminateWitness_weakenBound witnessSort witnessIndex
              boundSubstitution freeSubstitution image introduced
              (innerBound previous)
      · funext resultSort entry
        exact Term.eliminateWitness_weakenBound witnessSort witnessIndex
          boundSubstitution freeSubstitution image introduced (innerFree entry)

/-- 公式见证消去与后续普通替换融合，binder 情形由替换核的提升复合律统一处理。 -/
theorem Formula.eliminateWitness_substituteMapped
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      sourceBound middleBound middleFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree middleBound middleFree)
    (image : Term (HSignature σ) middleBound middleFree witnessSort)
    (outerBound : VariableSubstitution (HSignature σ)
      middleBound targetBound targetFree)
    (outerFree : VariableSubstitution (HSignature σ)
      middleFree targetBound targetFree)
    (formula : Formula (HSignature σ) sourceBound sourceFree) :
    (Formula.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image formula).substituteMapped outerBound outerFree =
      Formula.eliminateWitness witnessSort witnessIndex
        (fun entry => (boundSubstitution entry).substituteMapped
          outerBound outerFree)
        (fun entry => (freeSubstitution entry).substituteMapped
          outerBound outerFree)
        (image.substituteMapped outerBound outerFree) formula := by
  induction formula generalizing middleBound middleFree targetBound targetFree <;>
    simp_all [Formula.eliminateWitness, Formula.substituteMapped,
      Arguments.eliminateWitness_substituteMapped, Term.eliminateWitness_substituteMapped,
      VariableSubstitution.liftBound_substituteMapped,
      VariableSubstitution.weakenBound_substituteMapped, Term.substituteMapped_weakenBound]

/-- 见证消去与最外层 bound 实例化交换。 -/
theorem Formula.eliminateWitness_instantiateTop
    {bound sourceFree targetBound targetFree : SortContext (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (boundSubstitution : VariableSubstitution (HSignature σ)
      bound targetBound targetFree)
    (freeSubstitution : VariableSubstitution (HSignature σ)
      sourceFree targetBound targetFree)
    (image : Term (HSignature σ) targetBound targetFree witnessSort)
    {sort : σ.SortSymbol}
    (replacement : Term (HSignature σ) bound sourceFree sort)
    (body : Formula (HSignature σ) (sort :: bound) sourceFree) :
    Formula.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image (body.instantiateTop replacement) =
      (Formula.eliminateWitness witnessSort witnessIndex
        (VariableSubstitution.liftBound (σ := HSignature σ) sort
          boundSubstitution)
        (VariableSubstitution.weakenBound (σ := HSignature σ) sort
          freeSubstitution)
        (Term.weakenBound (σ := HSignature σ) sort image) body).instantiateTop
        (Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image replacement) := by
  change Formula.eliminateWitness witnessSort witnessIndex boundSubstitution
      freeSubstitution image
      (body.substituteMapped
        (VariableSubstitution.instantiateTop replacement)
        VariableSubstitution.freeId) =
    (Formula.eliminateWitness witnessSort witnessIndex
      (VariableSubstitution.liftBound (σ := HSignature σ) sort
        boundSubstitution)
      (VariableSubstitution.weakenBound (σ := HSignature σ) sort
        freeSubstitution)
      (Term.weakenBound (σ := HSignature σ) sort image) body).substituteMapped
      (VariableSubstitution.instantiateTop
        (Term.eliminateWitness witnessSort witnessIndex
          boundSubstitution freeSubstitution image replacement))
      VariableSubstitution.freeId
  rw [Formula.eliminateWitness_substituteMapped_source,
    Formula.eliminateWitness_substituteMapped]
  congr
  · funext resultSort entry
    cases entry with
    | here => rfl
    | there previous =>
        exact (Term.instantiateTop_weakenBound
          (σ := HSignature σ)
          (Term.eliminateWitness witnessSort witnessIndex
            boundSubstitution freeSubstitution image replacement)
          (boundSubstitution previous)).symm
  · funext resultSort entry
    exact (Term.instantiateTop_weakenBound
      (σ := HSignature σ)
      (Term.eliminateWitness witnessSort witnessIndex
        boundSubstitution freeSubstitution image replacement)
      (freeSubstitution entry)).symm
  · exact (Term.instantiateTop_weakenBound
      (σ := HSignature σ)
      (Term.eliminateWitness witnessSort witnessIndex
        boundSubstitution freeSubstitution image replacement)
      image).symm

end

end HenkinSignature
end FirstOrder
end Logic
end YesMetaZFC
