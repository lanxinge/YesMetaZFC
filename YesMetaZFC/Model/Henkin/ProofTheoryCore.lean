import YesMetaZFC.Logic.FirstOrder.Derivation

/-!
# 内在句子理论的完备性证明论核心

本模块只承载已经迁移到索引语法后的证明论事实：理论公理是 `Sentence`，有限理论支持
直接沿 `HilbertDerivation` 递归提取，有限一致性只对闭句上下文定义。Henkin 的新常量
扩张与典范模型暂不在此模块伪造兼容接口；它们将在对应数学内容迁移后接管旧消费者。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace Theory

/-- 有限闭句列表诱导的理论。列表顺序和重复成员不影响成员关系。 -/
def ofList {σ : Signature.{u, v, w}} (sentences : List (Sentence σ)) : Theory σ :=
  fun sentence => sentence ∈ sentences

@[simp]
theorem mem_ofList {σ : Signature.{u, v, w}}
    {sentences : List (Sentence σ)} {sentence : Sentence σ} :
    ofList sentences sentence ↔ sentence ∈ sentences :=
  Iff.rfl

/-- 列表头插入与理论插入严格给出同一个有限闭句理论。 -/
@[simp] theorem ofList_cons {σ : Signature.{u, v, w}}
    (sentence : Sentence σ) (sentences : List (Sentence σ)) :
    ofList (sentence :: sentences) =
      Theory.insert sentence (ofList sentences) := by
  funext candidate
  simp [ofList, Theory.insert]

end Theory

namespace Derives

/-- Hilbert 证明实际使用的有限闭句公理支持。 -/
structure FiniteProvableSupport {σ : Signature.{u, v, w}}
    (T : Theory σ) {free : SortContext σ} (formula : OpenFormula σ free) where
  sentences : List (Sentence σ)
  subset : ∀ sentence, sentence ∈ sentences → T sentence
  derivation : HilbertDerivation (Theory.ofList sentences) free formula

namespace HilbertDerivation

/-- 沿 Hilbert 推导递归提取有限理论支持，不经过 raw/check/checked 层。 -/
def finiteSupport {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {formula : OpenFormula σ free} :
    HilbertDerivation T free formula → FiniteProvableSupport T formula
  | .logical_axiom hAxiom =>
      {
        sentences := []
        subset := by simp
        derivation := .logical_axiom hAxiom
      }
  | .theory_axiom (sentence := sentence) hTheory =>
      {
        sentences := [sentence]
        subset := by
          intro candidate hCandidate
          have hEqual : candidate = sentence := by
            simpa using hCandidate
          simpa [hEqual] using hTheory
        derivation := .theory_axiom (by simp [Theory.ofList])
      }
  | .modus_ponens hAntecedent hImplication =>
      let antecedentSupport := finiteSupport hAntecedent
      let implicationSupport := finiteSupport hImplication
      {
        sentences := antecedentSupport.sentences ++ implicationSupport.sentences
        subset := by
          intro sentence hSentence
          rcases List.mem_append.mp hSentence with hAntecedent | hImplication
          · exact antecedentSupport.subset sentence hAntecedent
          · exact implicationSupport.subset sentence hImplication
        derivation :=
            .modus_ponens
            (antecedentSupport.derivation.theoryWeakening (fun {sentence} hSentence =>
              List.mem_append.mpr (Or.inl hSentence)))
            (implicationSupport.derivation.theoryWeakening (fun {sentence} hSentence =>
              List.mem_append.mpr (Or.inr hSentence)))
      }
  | .forall_generalization hFormula =>
      let support := finiteSupport hFormula
      {
        sentences := support.sentences
        subset := support.subset
        derivation := .forall_generalization support.derivation
      }
  | .free_strengthening hFormula =>
      let support := finiteSupport hFormula
      {
        sentences := support.sentences
        subset := support.subset
        derivation := .free_strengthening support.derivation
      }
  | .free_substitution substitution hFormula =>
      let support := finiteSupport hFormula
      {
        sentences := support.sentences
        subset := support.subset
        derivation := .free_substitution substitution support.derivation
      }

end HilbertDerivation

/-- 有限理论支持中的推导可回到原理论。 -/
structure FiniteTheorySupport {σ : Signature.{u, v, w}}
    (T : Theory σ) {free : SortContext σ}
    (Γ : Context σ free) (formula : OpenFormula σ free) where
  sentences : List (Sentence σ)
  subset : ∀ sentence, sentence ∈ sentences → T sentence
  derivation : Derives (Theory.ofList sentences) Γ formula

namespace FiniteTheorySupport

theorem toDerives {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (support : FiniteTheorySupport T Γ formula) :
    Derives T Γ formula :=
  support.derivation.theory_weaken (fun {sentence} hSentence =>
    support.subset sentence hSentence)

end FiniteTheorySupport

/-- 每个有限 Hilbert 推导只使用原理论中的有限多个闭句公理。 -/
theorem finiteTheorySupport {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hDerives : Derives T Γ formula) :
    Nonempty (FiniteTheorySupport T Γ formula) := by
  change Provable T (Context.discharge Γ formula) at hDerives
  rcases hDerives with ⟨derivation⟩
  let support := HilbertDerivation.finiteSupport derivation
  exact ⟨{
    sentences := support.sentences
    subset := support.subset
    derivation := ⟨support.derivation⟩
  }⟩

/-- 有限闭句候选理论相对背景理论的一致性。 -/
def FinitelyConsistent {σ : Signature.{u, v, w}}
    (T Δ : Theory σ) : Prop :=
  ∀ Γ : Context σ [],
    (∀ sentence, sentence ∈ Γ → Δ sentence) →
      Consistent T Γ

namespace FinitelyConsistent

/-- 有限一致性沿候选理论子集向下保持。 -/
theorem mono {σ : Signature.{u, v, w}}
    {T Δ U : Theory σ}
    (hConsistent : FinitelyConsistent T Δ)
    (hSubset : ∀ sentence, U sentence → Δ sentence) :
    FinitelyConsistent T U := by
  intro Γ hΓ
  exact hConsistent Γ (fun sentence hSentence =>
    hSubset sentence (hΓ sentence hSentence))

/-- 有限闭句列表理论有限一致，当且仅当该列表作为闭句上下文一致。 -/
theorem ofList_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {sentences : List (Sentence σ)} :
    FinitelyConsistent T (Theory.ofList sentences) ↔
      Consistent T sentences := by
  constructor
  · intro hConsistent
    exact hConsistent sentences (by
      intro sentence hSentence
      exact hSentence)
  · intro hConsistent Γ hSubset
    exact Consistent.mono hConsistent hSubset

/-- 候选理论不有限一致，当且仅当存在一个有限闭句反证上下文。 -/
theorem not_iff_exists_inconsistent_context
    {σ : Signature.{u, v, w}}
    {T Δ : Theory σ} :
    ¬ FinitelyConsistent T Δ ↔
      ∃ Γ : Context σ [],
        (∀ sentence, sentence ∈ Γ → Δ sentence) ∧
          Inconsistent T Γ := by
  constructor
  · intro hNotConsistent
    apply Classical.byContradiction
    intro hNoWitness
    apply hNotConsistent
    intro Γ hΓ hFalse
    exact hNoWitness ⟨Γ, hΓ, hFalse⟩
  · rintro ⟨Γ, hΓ, hFalse⟩ hConsistent
    exact hConsistent Γ hΓ hFalse

/-- 插入一个闭句后的有限反证可还原为原候选理论上的反证。 -/
theorem exists_inconsistent_cons_of_insert
    {σ : Signature.{u, v, w}}
    {T Δ : Theory σ} {sentence : Sentence σ} {Γ : Context σ []}
    (hΓ : ∀ candidate, candidate ∈ Γ → Theory.insert sentence Δ candidate)
    (hInconsistent : Inconsistent T Γ) :
    ∃ Γ' : Context σ [],
      (∀ candidate, candidate ∈ Γ' → Δ candidate) ∧
        Inconsistent T (sentence :: Γ') := by
  classical
  let Γ' := Γ.filter (fun candidate => decide (candidate ≠ sentence))
  refine ⟨Γ', ?_, ?_⟩
  · intro candidate hCandidate
    have hFiltered : candidate ∈ Γ ∧ candidate ≠ sentence := by
      simpa [Γ'] using hCandidate
    rcases hΓ candidate hFiltered.1 with hEqual | hOriginal
    · exact False.elim (hFiltered.2 hEqual)
    · exact hOriginal
  · exact .context_weaken (by
      intro candidate hCandidate
      by_cases hEqual : candidate = sentence
      · subst candidate
        exact List.mem_cons_self
      · have hFiltered : candidate ∈ Γ' := by
          simp [Γ', hCandidate, hEqual]
        exact List.mem_cons_of_mem sentence hFiltered) hInconsistent

/-- Lindenbaum 二分：闭句或其否定至少一侧保持有限一致。 -/
theorem extend_or_neg {σ : Signature.{u, v, w}}
    {T Δ : Theory σ}
    (hConsistent : FinitelyConsistent T Δ)
    (sentence : Sentence σ) :
    FinitelyConsistent T (Theory.insert sentence Δ) ∨
      FinitelyConsistent T (Theory.insert (.neg sentence) Δ) := by
  classical
  by_cases hPositive : FinitelyConsistent T (Theory.insert sentence Δ)
  · exact Or.inl hPositive
  · right
    apply Classical.byContradiction
    intro hNegative
    rcases not_iff_exists_inconsistent_context.mp hPositive with
      ⟨positiveContext, hPositiveContext, hPositiveFalse⟩
    rcases exists_inconsistent_cons_of_insert
        hPositiveContext hPositiveFalse with
      ⟨positiveBase, hPositiveBase, hPositiveConsFalse⟩
    rcases not_iff_exists_inconsistent_context.mp hNegative with
      ⟨negativeContext, hNegativeContext, hNegativeFalse⟩
    rcases exists_inconsistent_cons_of_insert
        hNegativeContext hNegativeFalse with
      ⟨negativeBase, hNegativeBase, hNegativeConsFalse⟩
    have hNegSentence : Derives T positiveBase (.neg sentence) :=
      (inconsistent_cons_iff.mp hPositiveConsFalse)
    have hDoubleNeg : Derives T negativeBase (.neg (.neg sentence)) :=
      inconsistent_cons_iff.mp hNegativeConsFalse
    have hSentence : Derives T negativeBase sentence :=
      neg_neg_elim hDoubleNeg
    have hCombinedConsistent :
        Consistent T (positiveBase ++ negativeBase) :=
      hConsistent _ (by
        intro candidate hCandidate
        rcases List.mem_append.mp hCandidate with hPositiveMem | hNegativeMem
        · exact hPositiveBase candidate hPositiveMem
        · exact hNegativeBase candidate hNegativeMem)
    apply hCombinedConsistent
    exact .neg_elim
      (.context_weaken (by
        intro candidate hCandidate
        simp [hCandidate]) hSentence)
      (.context_weaken (by
        intro candidate hCandidate
        simp [hCandidate]) hNegSentence)

end FinitelyConsistent

/-! 句子候选的轻量证明载体；良构性已由句法索引保证。 -/
structure WF_Candidate {σ : Signature.{u, v, w}}
    (T Δ : Theory σ) : Prop where
  wf_consistent : FinitelyConsistent T Δ

namespace WF_Candidate

theorem wf_extend_or_neg {σ : Signature.{u, v, w}}
    {T Δ : Theory σ} (hCandidate : WF_Candidate T Δ)
    (sentence : Sentence σ) :
    WF_Candidate T (Theory.insert sentence Δ) ∨
      WF_Candidate T (Theory.insert (.neg sentence) Δ) := by
  rcases FinitelyConsistent.extend_or_neg
      hCandidate.wf_consistent sentence with
    hPositive | hNegative
  · exact Or.inl ⟨hPositive⟩
  · exact Or.inr ⟨hNegative⟩

end WF_Candidate

end Derives
end FirstOrder
end Logic
end YesMetaZFC
