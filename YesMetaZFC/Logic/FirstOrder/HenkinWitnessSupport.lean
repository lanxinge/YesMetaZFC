import YesMetaZFC.Logic.FirstOrder.HenkinTransport

/-!
# Henkin 证明的有限见证支持

本模块精确收集一棵有限 Hilbert 证明中出现的 Henkin 常量。除各节点结论外，
`free_substitution` 保存的整个有限替换函数也纳入支持，因此不会漏掉公式未使用变量对应的
替换项。该支持将作为保守性证明一次性消去全部见证常量的递归参数。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}}

/-- 一个 Henkin 见证常量由其排序和自然数编号唯一确定。 -/
abbrev WitnessRef (σ : Signature.{u, v, w}) := σ.SortSymbol × Nat

mutual

/-- 项中见证常量的有限出现列表。 -/
def Term.witnessSupport
    {bound free : SortContext (HSignature σ)} :
    {sort : σ.SortSymbol} → Term (HSignature σ) bound free sort →
      List (WitnessRef σ)
  | _, .bvar _ => []
  | _, .fvar _ => []
  | _, .app function arguments =>
      match function with
      | .base _ => Arguments.witnessSupport arguments
      | .witness sort index =>
          (sort, index) :: Arguments.witnessSupport arguments

/-- 参数列中见证常量的有限出现列表。 -/
def Arguments.witnessSupport
    {bound free : SortContext (HSignature σ)} :
    {sorts : List σ.SortSymbol} →
      Arguments (HSignature σ) bound free sorts → List (WitnessRef σ)
  | _, .nil => []
  | _, .cons head tail =>
      Term.witnessSupport head ++ Arguments.witnessSupport tail

end

/-- 公式中见证常量的有限出现列表。 -/
def Formula.witnessSupport
    {bound free : SortContext (HSignature σ)} :
    Formula (HSignature σ) bound free → List (WitnessRef σ)
  | .falsum => []
  | .truth => []
  | .rel _ arguments => Arguments.witnessSupport arguments
  | .equal left right =>
      Term.witnessSupport left ++ Term.witnessSupport right
  | .neg body => Formula.witnessSupport body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      Formula.witnessSupport left ++ Formula.witnessSupport right
  | .forallE _ body
  | .existsE _ body => Formula.witnessSupport body

mutual

/-- 项支持成员关系与见证出现谓词完全一致。 -/
theorem Term.mem_witnessSupport_iff
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext (HSignature σ)} {sort : σ.SortSymbol}
    (term : Term (HSignature σ) bound free sort) :
    (witnessSort, witnessIndex) ∈ Term.witnessSupport term ↔
      Term.usesWitness witnessSort witnessIndex term := by
  match term with
  | .bvar _ | .fvar _ => simp [Term.witnessSupport, Term.usesWitness]
  | .app (HenkinFunc.base function) arguments =>
      simpa [Term.witnessSupport, Term.usesWitness] using
        Arguments.mem_witnessSupport_iff witnessSort witnessIndex arguments
  | .app (HenkinFunc.witness sort index) arguments =>
      simp [Term.witnessSupport, Term.usesWitness, Arguments.mem_witnessSupport_iff,
        Prod.mk.injEq, eq_comm, and_comm]

/-- 参数列支持成员关系与见证出现谓词完全一致。 -/
theorem Arguments.mem_witnessSupport_iff
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext (HSignature σ)}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) bound free sorts) :
    (witnessSort, witnessIndex) ∈ Arguments.witnessSupport arguments ↔
      Arguments.usesWitness witnessSort witnessIndex arguments := by
  match arguments with
  | .nil => simp [Arguments.witnessSupport, Arguments.usesWitness]
  | .cons head tail =>
      simp [Arguments.witnessSupport, Arguments.usesWitness,
        Term.mem_witnessSupport_iff, Arguments.mem_witnessSupport_iff]

end


/-- 公式支持成员关系与见证出现谓词完全一致。 -/
theorem Formula.mem_witnessSupport_iff
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext (HSignature σ)}
    (formula : Formula (HSignature σ) bound free) :
    (witnessSort, witnessIndex) ∈ Formula.witnessSupport formula ↔
      Formula.usesWitness witnessSort witnessIndex formula := by
  induction formula <;>
    simp_all [Formula.witnessSupport, Formula.usesWitness,
      Term.mem_witnessSupport_iff, Arguments.mem_witnessSupport_iff]

/-- 从有限支持中删除指定见证的全部出现。 -/
def withoutWitness [DecidableEq σ.SortSymbol]
    (witness : WitnessRef σ) (support : List (WitnessRef σ)) :
    List (WitnessRef σ) :=
  support.filter (· ≠ witness)

@[simp] theorem withoutWitness_append [DecidableEq σ.SortSymbol]
    (witness : WitnessRef σ) (left right : List (WitnessRef σ)) :
    withoutWitness witness (left ++ right) =
      withoutWitness witness left ++ withoutWitness witness right := by
  simp [withoutWitness, List.filter_append]

/-- 若指定见证不在支持中，过滤保持原列表。 -/
theorem withoutWitness_eq_self_of_not_mem [DecidableEq σ.SortSymbol]
    {witness : WitnessRef σ} {support : List (WitnessRef σ)}
    (hNotMem : witness ∉ support) :
    withoutWitness witness support = support := by
  simpa [withoutWitness] using
    (List.filter_bne_eq_self_of_not_mem hNotMem)

/-- 按给定次序从有限支持中删除一列见证。 -/
def withoutWitnesses [DecidableEq σ.SortSymbol] :
    List (WitnessRef σ) → List (WitnessRef σ) → List (WitnessRef σ)
  | [], support => support
  | witness :: witnesses, support =>
      withoutWitnesses witnesses (withoutWitness witness support)

/-- 连续过滤后的成员，恰为原支持中不属于删除列表的成员。 -/
theorem mem_withoutWitnesses_iff [DecidableEq σ.SortSymbol]
    (candidate : WitnessRef σ)
    (witnesses support : List (WitnessRef σ)) :
    candidate ∈ withoutWitnesses witnesses support ↔
      candidate ∈ support ∧ candidate ∉ witnesses := by
  induction witnesses generalizing support with
  | nil => simp [withoutWitnesses]
  | cons witness witnesses ih =>
      rw [withoutWitnesses, ih]
      have hFilter :
          candidate ∈ withoutWitness witness support ↔
            candidate ∈ support ∧ candidate ≠ witness := by
        simp only [withoutWitness, List.mem_filter, decide_eq_true_eq]
      rw [hFilter]
      constructor
      · rintro ⟨⟨hSupport, hNe⟩, hRest⟩
        exact ⟨hSupport, by
          simp only [List.mem_cons, not_or]
          exact ⟨hNe, hRest⟩⟩
      · rintro ⟨hSupport, hNotMem⟩
        have hParts : candidate ≠ witness ∧ candidate ∉ witnesses := by
          simpa only [List.mem_cons, not_or] using hNotMem
        exact ⟨⟨hSupport, hParts.1⟩, hParts.2⟩

/-- 用一个支持列表删除其自身全部成员，结果为空。 -/
@[simp] theorem withoutWitnesses_self [DecidableEq σ.SortSymbol]
    (support : List (WitnessRef σ)) :
    withoutWitnesses support support = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro candidate hCandidate
  have hMembership :=
    (mem_withoutWitnesses_iff candidate support support).mp hCandidate
  exact hMembership.2 hMembership.1

mutual

/-- 持久消去在项支持上精确删除指定见证。 -/
theorem Term.witnessSupport_eliminatePersistentWitness
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext (HSignature σ)} {sort : σ.SortSymbol}
    (term : Term (HSignature σ) bound free sort) :
    Term.witnessSupport
        (Term.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex term) =
      withoutWitness (witnessSort, witnessIndex)
        (Term.witnessSupport term) := by

  match term with
  | .bvar _ | .fvar _ => rfl
  | .app (HenkinFunc.base function) arguments =>
      simpa [Term.eliminatePersistentWitness, Arguments.eliminatePersistentWitness,
        Term.eliminateWitness, Term.witnessSupport] using
        Arguments.witnessSupport_eliminatePersistentWitness witnessSort witnessIndex arguments
  | .app (HenkinFunc.witness sort index) .nil =>
      by_cases h : sort = witnessSort ∧ index = witnessIndex
      · rcases h with ⟨rfl, rfl⟩
        simp [Term.eliminatePersistentWitness, Term.eliminateWitness,
          Term.witnessSupport, Arguments.witnessSupport, withoutWitness,
          persistentImage, FreshVariable.persistent]
      · simp [Term.eliminatePersistentWitness, Term.eliminateWitness,
          Arguments.eliminateWitness, Term.witnessSupport,
          Arguments.witnessSupport, withoutWitness, h, Prod.mk.injEq]

/-- 持久消去在参数支持上精确删除指定见证。 -/
theorem Arguments.witnessSupport_eliminatePersistentWitness
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext (HSignature σ)}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) bound free sorts) :
    Arguments.witnessSupport
        (Arguments.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex arguments) =
      withoutWitness (witnessSort, witnessIndex)
        (Arguments.witnessSupport arguments) := by
  match arguments with
  | .nil => rfl
  | .cons head tail =>
      change Term.witnessSupport (Term.eliminatePersistentWitness
          witnessSort witnessIndex head) ++
        Arguments.witnessSupport (Arguments.eliminatePersistentWitness
          witnessSort witnessIndex tail) = _
      rw [Term.witnessSupport_eliminatePersistentWitness, Arguments.witnessSupport_eliminatePersistentWitness]
      exact (withoutWitness_append _ _ _).symm

end

/-- 持久消去在公式支持上精确删除指定见证。 -/
theorem Formula.witnessSupport_eliminatePersistentWitness
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {bound free : SortContext (HSignature σ)}
    (formula : Formula (HSignature σ) bound free) :
    Formula.witnessSupport
        (Formula.eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex formula) =
      withoutWitness (witnessSort, witnessIndex)
        (Formula.witnessSupport formula) := by
  induction formula <;>
    simp_all only [Formula.eliminatePersistentWitness_falsum,
      Formula.eliminatePersistentWitness_truth, Formula.eliminatePersistentWitness_equal,
      Formula.eliminatePersistentWitness_neg, Formula.eliminatePersistentWitness_conj,
      Formula.eliminatePersistentWitness_disj, Formula.eliminatePersistentWitness_imp,
      Formula.eliminatePersistentWitness_iff, Formula.eliminatePersistentWitness_forallE,
      Formula.eliminatePersistentWitness_existsE, Formula.witnessSupport,
      Term.witnessSupport_eliminatePersistentWitness, withoutWitness_append]
  case falsum => rfl
  case truth => rfl
  case rel relation arguments =>
    exact Arguments.witnessSupport_eliminatePersistentWitness witnessSort witnessIndex arguments

mutual

/-- 变量重命名不改变项中的见证常量支持。 -/
theorem Term.witnessSupport_renameMapped
    {sourceBound sourceFree targetBound targetFree :
      SortContext (HSignature σ)}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    {sort : σ.SortSymbol}
    (term : Term (HSignature σ) sourceBound sourceFree sort) :
    Term.witnessSupport
        (term.renameMapped boundRenaming freeRenaming) =
      Term.witnessSupport term := by
  match term with
  | .bvar _ | .fvar _ => rfl
  | .app (HenkinFunc.base function) arguments
  | .app (HenkinFunc.witness sort index) arguments =>
      simpa [Term.renameMapped, Term.witnessSupport] using
        Arguments.witnessSupport_renameMapped boundRenaming freeRenaming arguments

/-- 变量重命名不改变参数列中的见证常量支持。 -/
theorem Arguments.witnessSupport_renameMapped
    {sourceBound sourceFree targetBound targetFree :
      SortContext (HSignature σ)}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) sourceBound sourceFree sorts) :
    Arguments.witnessSupport
        (arguments.renameMapped boundRenaming freeRenaming) =
      Arguments.witnessSupport arguments := by
  match arguments with
  | .nil => rfl
  | .cons head tail =>
      simp [Arguments.renameMapped, Arguments.witnessSupport,
        Term.witnessSupport_renameMapped, Arguments.witnessSupport_renameMapped]

end

/-- 变量重命名不改变公式中的见证常量支持。 -/
theorem Formula.witnessSupport_renameMapped
    {sourceBound sourceFree targetBound targetFree :
      SortContext (HSignature σ)}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (formula : Formula (HSignature σ) sourceBound sourceFree) :
    Formula.witnessSupport
        (formula.renameMapped boundRenaming freeRenaming) =
      Formula.witnessSupport formula := by
  induction formula generalizing targetBound <;>
    simp_all [Formula.renameMapped, Formula.witnessSupport,
      Term.witnessSupport_renameMapped, Arguments.witnessSupport_renameMapped]

/-- 闭句嵌入任意 free 上下文时不改变见证支持。 -/
theorem Formula.witnessSupport_fromSentence
    {free : SortContext (HSignature σ)}
    (sentence : Sentence (HSignature σ)) :
    Formula.witnessSupport (Formula.fromSentence (free := free) sentence) =
      Formula.witnessSupport sentence := by
  cases free with
  | nil => rfl
  | cons head tail =>
      change Formula.witnessSupport
          (sentence.renameMapped VariableRenaming.id
            (VariableRenaming.empty : VariableRenaming [] (head :: tail))) =
        Formula.witnessSupport sentence
      exact Formula.witnessSupport_renameMapped
        VariableRenaming.id VariableRenaming.empty sentence

/-- 有限源上下文上的统一替换所保存的全部见证常量。 -/
def VariableSubstitution.witnessSupport
    {bound free : SortContext (HSignature σ)} :
    {source : SortContext (HSignature σ)} →
      VariableSubstitution (HSignature σ) source bound free →
        List (WitnessRef σ)
  | [], _ => []
  | _ :: source, substitution =>
      Term.witnessSupport (substitution .here) ++
        VariableSubstitution.witnessSupport
          (source := source) (fun entry => substitution (.there entry))

/-- 持久消去在有限统一替换支持上精确删除指定见证。 -/
theorem VariableSubstitution.witnessSupport_eliminateSubstitution
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {source targetFree : SortContext (HSignature σ)}
    (substitution : VariableSubstitution (HSignature σ)
      source [] targetFree) :
    VariableSubstitution.witnessSupport
        (eliminateSubstitution (σ := σ) witnessSort witnessIndex
          substitution) =
      withoutWitness (witnessSort, witnessIndex)
        (VariableSubstitution.witnessSupport substitution) := by
  induction source generalizing targetFree with
  | nil =>
      change Term.witnessSupport
          (.fvar (Variable.last targetFree witnessSort) :
            OpenTerm (HSignature σ)
              (FreshVariable.persistentContext targetFree witnessSort)
              witnessSort) = []
      rfl
  | cons sourceSort source ih =>
      change
        Term.witnessSupport
              (Term.eliminatePersistentWitness (σ := σ)
                witnessSort witnessIndex (substitution .here)) ++
            VariableSubstitution.witnessSupport
              (eliminateSubstitution (σ := σ) witnessSort witnessIndex
                (fun entry => substitution (.there entry))) =
          withoutWitness (witnessSort, witnessIndex)
            (Term.witnessSupport (substitution .here) ++
              VariableSubstitution.witnessSupport
                (fun entry => substitution (.there entry)))
      rw [withoutWitness_append,
        Term.witnessSupport_eliminatePersistentWitness,
        ih]

end HenkinSignature

open HenkinSignature

variable {σ : Signature.{u, v, w}}

namespace HilbertBaseAxiom

/-- 基础 Hilbert 公理全部显式载荷中的有限见证支持。 -/
def witnessSupport
    {free : SortContext (HSignature σ)}
    {formula : OpenFormula (HSignature σ) free} :
    HilbertBaseAxiom (HSignature σ) formula → List (WitnessRef σ)
  | .implication_distribution antecedent middle consequent =>
      Formula.witnessSupport antecedent ++
        Formula.witnessSupport middle ++
        Formula.witnessSupport consequent
  | .self_implication formula => Formula.witnessSupport formula
  | .weakening formula extra
  | .contradiction formula extra
  | .explosion formula extra
  | .case_analysis formula extra =>
      Formula.witnessSupport formula ++ Formula.witnessSupport extra
  | .classical formula
  | .falsum_elimination formula
  | .negation_intro formula
  | .negation_elimination formula => Formula.witnessSupport formula
  | .truth_intro => []
  | .conjunction_intro left right
  | .conjunction_elim_left left right
  | .conjunction_elim_right left right
  | .disjunction_intro_left left right
  | .disjunction_intro_right left right
  | .biconditional_intro left right
  | .biconditional_elim_left left right
  | .biconditional_elim_right left right =>
      Formula.witnessSupport left ++ Formula.witnessSupport right
  | .disjunction_elimination left right conclusion =>
      Formula.witnessSupport left ++ Formula.witnessSupport right ++
        Formula.witnessSupport conclusion
  | .forall_specialization _ body term
  | .exists_introduction _ body term =>
      Formula.witnessSupport body ++ Term.witnessSupport term
  | .forall_distribution _ antecedent consequent =>
      Formula.witnessSupport antecedent ++
        Formula.witnessSupport consequent
  | .vacuous_forall _ formula => Formula.witnessSupport formula
  | .exists_elimination _ body conclusion =>
      Formula.witnessSupport body ++ Formula.witnessSupport conclusion
  | .equality_substitution _ left right body =>
      Term.witnessSupport left ++ Term.witnessSupport right ++
        Formula.witnessSupport body
  | .equality_reflexivity term => Term.witnessSupport term

/-- 显式运输基础公理的结论索引不改变其载荷支持。 -/
@[simp] theorem witnessSupport_castFormula
    {free : SortContext (HSignature σ)}
    {formula₁ formula₂ : OpenFormula (HSignature σ) free}
    (hFormula : formula₁ = formula₂)
    (hAxiom : HilbertBaseAxiom (HSignature σ) formula₁) :
    witnessSupport (castFormula hFormula hAxiom) = witnessSupport hAxiom := by
  cases hFormula
  rfl

/-- 公理载荷支持在持久见证消去下精确过滤。 -/
theorem witnessSupport_eliminatePersistentWitness
    [DecidableEq σ.SortSymbol]
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    {free : SortContext (HSignature σ)}
    {formula : OpenFormula (HSignature σ) free}
    (hAxiom : HilbertBaseAxiom (HSignature σ) formula) :
    witnessSupport
        (eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex hAxiom) =
      HenkinSignature.withoutWitness (witnessSort, witnessIndex)
        (witnessSupport hAxiom) := by
  cases hAxiom <;>
    simp only [eliminatePersistentWitness, witnessSupport_castFormula] <;>
    simp [witnessSupport,
      HenkinSignature.withoutWitness_append,
      HenkinSignature.Formula.witnessSupport_eliminatePersistentWitness,
      HenkinSignature.Term.witnessSupport_eliminatePersistentWitness] <;>
    simp [HenkinSignature.withoutWitness]

end HilbertBaseAxiom

namespace HilbertDerivation

/--
Hilbert 证明树的有限见证支持。叶节点结论计入支持；组合节点递归汇总子证明，
统一 free 替换还额外扫描替换函数在有限源上下文上的全部项像。
-/
def witnessSupport
    {T : Theory (HSignature σ)}
    {free : SortContext (HSignature σ)}
    {formula : OpenFormula (HSignature σ) free}
    (proof : HilbertDerivation T free formula) : List (WitnessRef σ) :=
  match proof with
    | .logical_axiom hAxiom => HilbertBaseAxiom.witnessSupport hAxiom
    | .theory_axiom _ => Formula.witnessSupport formula
    | .modus_ponens hAntecedent hImplication =>
        witnessSupport hAntecedent ++ witnessSupport hImplication
    | .forall_generalization hFormula => witnessSupport hFormula
    | .free_strengthening hFormula => witnessSupport hFormula
    | .free_substitution substitution hFormula =>
        VariableSubstitution.witnessSupport substitution ++
          witnessSupport hFormula

/-- 显式运输结论公式索引，不改变证明树的有限见证支持。 -/
@[simp] theorem witnessSupport_castFormula
    {T : Theory (HSignature σ)}
    {free : SortContext (HSignature σ)}
    {formula₁ formula₂ : OpenFormula (HSignature σ) free}
    (hFormula : formula₁ = formula₂)
    (proof : HilbertDerivation T free formula₁) :
    witnessSupport (castFormula hFormula proof) = witnessSupport proof := by
  cases hFormula
  rfl

/-- 持久消去在整棵 Hilbert 证明的有限支持上精确删除指定见证。 -/
theorem witnessSupport_eliminatePersistentWitness
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (hTheoryAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    {free : SortContext (HSignature σ)}
    {formula : OpenFormula (HSignature σ) free}
    (proof : HilbertDerivation T free formula) :
    witnessSupport
        (eliminatePersistentWitness (σ := σ)
          witnessSort witnessIndex hTheoryAvoids proof) =
      HenkinSignature.withoutWitness (witnessSort, witnessIndex)
        (witnessSupport proof) := by
  induction proof with
  | logical_axiom hAxiom =>
      simp [witnessSupport, eliminatePersistentWitness,
        HilbertBaseAxiom.witnessSupport_eliminatePersistentWitness]
  | @theory_axiom free sentence hTheory =>
      have hNotMem :
          (witnessSort, witnessIndex) ∉
            HenkinSignature.Formula.witnessSupport sentence := by
        intro hMem
        exact hTheoryAvoids hTheory
          ((HenkinSignature.Formula.mem_witnessSupport_iff
            witnessSort witnessIndex sentence).mp hMem)
      simpa [witnessSupport, eliminatePersistentWitness,
        HenkinSignature.Formula.witnessSupport_fromSentence] using
        (HenkinSignature.withoutWitness_eq_self_of_not_mem hNotMem).symm
  | modus_ponens hAntecedent hImplication ihAntecedent ihImplication =>
      simpa only [witnessSupport, eliminatePersistentWitness,
        HenkinSignature.withoutWitness_append, ihAntecedent] using!
        congrArg
          (fun support =>
            HenkinSignature.withoutWitness (witnessSort, witnessIndex)
                (witnessSupport hAntecedent) ++ support)
          ihImplication
  | forall_generalization hFormula ih =>
      simpa [witnessSupport, eliminatePersistentWitness] using ih
  | free_strengthening hFormula ih =>
      simpa [witnessSupport, eliminatePersistentWitness] using ih
  | free_substitution substitution hFormula ih =>
      simp [witnessSupport, eliminatePersistentWitness,
        HenkinSignature.withoutWitness_append,
        HenkinSignature.VariableSubstitution.witnessSupport_eliminateSubstitution,
        ih]

/-- 闭句见证消去同样在证明支持上精确删除指定见证。 -/
theorem witnessSupport_eliminateSentenceWitness
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (witnessSort : σ.SortSymbol) (witnessIndex : Nat)
    (hTheoryAvoids :
      ∀ {sentence : Sentence (HSignature σ)}, T sentence →
        ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    {sentence : Sentence (HSignature σ)}
    (hSentenceAvoids :
      ¬ Formula.usesWitness witnessSort witnessIndex sentence)
    (proof : HilbertDerivation T [] sentence) :
    witnessSupport
        (eliminateSentenceWitness (σ := σ)
          witnessSort witnessIndex hTheoryAvoids hSentenceAvoids proof) =
      HenkinSignature.withoutWitness (witnessSort, witnessIndex)
        (witnessSupport proof) := by
  simpa only [eliminateSentenceWitness, witnessSupport,
    witnessSupport_castFormula] using
    (witnessSupport_eliminatePersistentWitness (σ := σ)
      witnessSort witnessIndex hTheoryAvoids proof)

/-- 按有限列表逐个消去闭句证明中的全部指定见证。 -/
def eliminateSentenceWitnesses
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (hTheoryAvoids :
      ∀ witness : WitnessRef σ,
        ∀ {theorySentence : Sentence (HSignature σ)}, T theorySentence →
          ¬ Formula.usesWitness witness.1 witness.2 theorySentence)
    {sentence : Sentence (HSignature σ)}
    (hSentenceAvoids :
      ∀ witness : WitnessRef σ,
        ¬ Formula.usesWitness witness.1 witness.2 sentence) :
    (witnesses : List (WitnessRef σ)) →
      HilbertDerivation T [] sentence → HilbertDerivation T [] sentence
  | [], proof => proof
  | witness :: witnesses, proof =>
      eliminateSentenceWitnesses hTheoryAvoids hSentenceAvoids witnesses
        (eliminateSentenceWitness (σ := σ)
          witness.1 witness.2
          (hTheoryAvoids witness) (hSentenceAvoids witness) proof)

/-- 有限清洗器在证明支持上等于同序的连续过滤。 -/
theorem witnessSupport_eliminateSentenceWitnesses
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (hTheoryAvoids :
      ∀ witness : WitnessRef σ,
        ∀ {theorySentence : Sentence (HSignature σ)}, T theorySentence →
          ¬ Formula.usesWitness witness.1 witness.2 theorySentence)
    {sentence : Sentence (HSignature σ)}
    (hSentenceAvoids :
      ∀ witness : WitnessRef σ,
        ¬ Formula.usesWitness witness.1 witness.2 sentence)
    (witnesses : List (WitnessRef σ))
    (proof : HilbertDerivation T [] sentence) :
    witnessSupport
        (eliminateSentenceWitnesses hTheoryAvoids hSentenceAvoids
          witnesses proof) =
      HenkinSignature.withoutWitnesses witnesses (witnessSupport proof) := by
  induction witnesses generalizing proof with
  | nil => rfl
  | cons witness witnesses ih =>
      rw [eliminateSentenceWitnesses, ih,
        witnessSupport_eliminateSentenceWitness]
      rfl

/-- 直接按证明自身的有限支持消去全部见证。 -/
def eliminateOwnWitnessSupport
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (hTheoryAvoids :
      ∀ witness : WitnessRef σ,
        ∀ {theorySentence : Sentence (HSignature σ)}, T theorySentence →
          ¬ Formula.usesWitness witness.1 witness.2 theorySentence)
    {sentence : Sentence (HSignature σ)}
    (hSentenceAvoids :
      ∀ witness : WitnessRef σ,
        ¬ Formula.usesWitness witness.1 witness.2 sentence)
    (proof : HilbertDerivation T [] sentence) :
    HilbertDerivation T [] sentence :=
  eliminateSentenceWitnesses hTheoryAvoids hSentenceAvoids
    (witnessSupport proof) proof

/-- 按自身支持完成有限清洗后，证明树中不再含任何 Henkin 见证常量。 -/
@[simp] theorem witnessSupport_eliminateOwnWitnessSupport
    [DecidableEq σ.SortSymbol]
    {T : Theory (HSignature σ)}
    (hTheoryAvoids :
      ∀ witness : WitnessRef σ,
        ∀ {theorySentence : Sentence (HSignature σ)}, T theorySentence →
          ¬ Formula.usesWitness witness.1 witness.2 theorySentence)
    {sentence : Sentence (HSignature σ)}
    (hSentenceAvoids :
      ∀ witness : WitnessRef σ,
        ¬ Formula.usesWitness witness.1 witness.2 sentence)
    (proof : HilbertDerivation T [] sentence) :
    witnessSupport
        (eliminateOwnWitnessSupport hTheoryAvoids hSentenceAvoids proof) = [] := by
  rw [eliminateOwnWitnessSupport,
    witnessSupport_eliminateSentenceWitnesses,
    HenkinSignature.withoutWitnesses_self]

end HilbertDerivation

end FirstOrder
end Logic
end YesMetaZFC
