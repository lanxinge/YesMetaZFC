import YesMetaZFC.Model.ZFC.Pure.PureSetIterations

/-! # 传递闭包的纯定义与无条件存在性

从给定集合开始内部迭代并集，再并其值域，得到包含源集的最小传递集。
最小性使用实际子集公式的内部自然数归纳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTransitiveClosure
open PureModel PureNaturalInduction PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

def Subset (left right : Carrier ℳ) : Prop := ∀ element, membership ℳ element left → membership ℳ element right
def Transitive (set : Carrier ℳ) : Prop := ∀ member, membership ℳ member set → ∀ element, membership ℳ element member → membership ℳ element set

def Closure (source output : Carrier ℳ) : Prop :=
  (Subset source output ∧ Transitive output) ∧ ∀ lower, Subset source lower ∧ Transitive lower → Subset output lower

def subsetValues : Formula S [] [s,s,s] :=
  Nonlogical.BasicSetTheory.subset_formula
    (Nonlogical.BasicSetTheory.function_application_term (.fvar (.there .here)) (.fvar .here))
    (.fvar (.there (.there .here)))

/-- 并集迭代的所有项都包含于任意给定的传递上界。 -/
theorem iterations_bounded (hℳ : Theory.Models ℳ theory) {sequence source lower : Carrier ℳ}
    (hIteration : PureOmegaIteration.Iterates hℳ PureSetIterations.Union sequence source)
    (hSource : Subset source lower) (hLower : Transitive lower) :
    ∀ input, membership ℳ input (omega hℳ) → Subset (value hℳ sequence input) lower := by
  apply source_induction hℳ subsetValues (.cons sequence (.cons lower .nil))
  · change Subset (value hℳ sequence (zero hℳ)) lower
    rw [hIteration.2.2.1]
    exact hSource
  · intro input hInput hPrevious element hElement
    obtain ⟨member,hMember,hElementMember⟩ := (hIteration.2.2.2 input hInput element).mp hElement
    exact hLower member (hPrevious member hMember) element hElementMember

/-- 任意集合都存在包含它的最小传递集。 -/
theorem exists_closure (hℳ : Theory.Models ℳ theory) (source : Carrier ℳ) : ∃ output, Closure source output := by
  obtain ⟨sequence,hSequence,_⟩ := PureOmegaIteration.functional hℳ PureSetIterations.union_rep (PureSetIterations.union_total hℳ) source
  have hIteration := PureOmegaIteration.iterates_of_graph hℳ PureSetIterations.union_rep (PureSetIterations.union_total hℳ) hSequence
  obtain ⟨range,hRange⟩ := PureRelationCoordinates.exists_coordinate hℳ .range sequence
  have hRange := (PureRelationCoordinates.range_correct range sequence).mp hRange
  obtain ⟨output,hOutput⟩ := PureModel.union hℳ range
  have hMember (element : Carrier ℳ) : membership ℳ element output ↔
      ∃ input, membership ℳ input (omega hℳ) ∧ membership ℳ element (value hℳ sequence input) := by
    rw [hOutput element]
    constructor
    · rintro ⟨member,hMember,hElement⟩
      obtain ⟨input,hPair⟩ := (hRange member).mp hMember
      have hInput := (hIteration.2.1 input).mpr ⟨member,hPair⟩
      have hValue := (PureRelationFunctions.application_spec hIteration.1 ((hIteration.2.1 input).mp hInput) _).mp
        (((PureDifferenceStage.realizes hℳ).function .application (.cons sequence (.cons input .nil)) _).mpr rfl)
      have hEqual : member = value hℳ sequence input := hIteration.1.2 input member _ hPair hValue
      exact ⟨input,hInput,hEqual ▸ hElement⟩
    · rintro ⟨input,hInput,hElement⟩
      have hValue := (PureRelationFunctions.application_spec hIteration.1 ((hIteration.2.1 input).mp hInput) _).mp
        (((PureDifferenceStage.realizes hℳ).function .application (.cons sequence (.cons input .nil)) _).mpr rfl)
      exact ⟨value hℳ sequence input,(hRange _).mpr ⟨input,hValue⟩,hElement⟩
  refine ⟨output,⟨?_,?_⟩,?_⟩
  · intro element hElement
    exact (hMember element).mpr ⟨zero hℳ,zero_mem hℳ,hIteration.2.2.1.symm ▸ hElement⟩
  · intro member hMemberOutput element hElement
    obtain ⟨input,hInput,hMemberValue⟩ := (hMember member).mp hMemberOutput
    exact (hMember element).mpr ⟨succ hℳ input,succ_mem hℳ hInput,
      (hIteration.2.2.2 input hInput element).mpr ⟨member,hMemberValue,hElement⟩⟩
  · intro lower hLower element hElement
    obtain ⟨input,hInput,hElementValue⟩ := (hMember element).mp hElement
    exact iterations_bounded hℳ hIteration hLower.1 hLower.2 input hInput element hElementValue

theorem unique (hℳ : Theory.Models ℳ theory) {source first second : Carrier ℳ}
    (hFirst : Closure source first) (hSecond : Closure source second) : first = second :=
  extensionality hℳ first second (fun element => ⟨hFirst.2 second hSecond.1 element,hSecond.2 first hFirst.1 element⟩)

def specification : Formula S [] [s,s] :=
  Nonlogical.BasicSetTheory.transitive_closure_spec (.fvar (.there .here)) (.fvar .here)
def graph : Formula ℒ [] [setSort,setSort] := openFormula PureArithmeticStage.interpretation specification

theorem transitive_correct (hℳ : Theory.Models ℳ theory) (set : Carrier ℳ) :
    (PureArithmeticStage.expansion hℳ).relation .isTransitiveSet (.cons set .nil) ↔ Transitive set := by
  have hDef := realizes_definition (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ)
    .isTransitiveSet (PureRoundOneRelations.condition .isTransitiveSet) rfl (.cons set .nil)
  apply hDef.trans
  simp only [PureRoundOneRelations.condition,Nonlogical.BasicSetTheory.is_transitive_set_condition,
    Formula.satisfies_forallFreeTop,Formula.satisfies]
  rfl

theorem specification_correct (hℳ : Theory.Models ℳ theory) (source output : Carrier ℳ) :
    specification.satisfies (templateEnv (.cons output (.cons source .nil)) : Env (PureArithmeticStage.expansion hℳ).model [] [s,s]) ↔
      Closure source output := by
  simp only [specification,Nonlogical.BasicSetTheory.transitive_closure_spec,
    Formula.satisfies_forallFreeTop,Formula.satisfies]
  change (_ ∧ (PureArithmeticStage.expansion hℳ).relation .isTransitiveSet (.cons output .nil)) ∧
    (∀ lower, (_ ∧ (PureArithmeticStage.expansion hℳ).relation .isTransitiveSet (.cons lower .nil)) → _) ↔ _
  simp only [transitive_correct hℳ]
  rfl

theorem graph_correct (hℳ : Theory.Models ℳ theory) (source output : Carrier ℳ) :
    graph.satisfies (templateEnv (.cons output (.cons source .nil))) ↔ Closure source output :=
  (openFormula_correct (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ)
    specification (.cons output (.cons source .nil))).trans (specification_correct hℳ source output)

theorem functional (hℳ : Theory.Models ℳ theory) (source : Carrier ℳ) :
    ∃ output, graph.satisfies (templateEnv (.cons output (.cons source .nil))) ∧
      ∀ other, graph.satisfies (templateEnv (.cons other (.cons source .nil))) → other = output := by
  obtain ⟨output,hOutput⟩ := exists_closure hℳ source
  exact ⟨output,(graph_correct hℳ source output).mpr hOutput,
    fun other hOther => unique hℳ ((graph_correct hℳ source other).mp hOther) hOutput⟩

theorem dependencies_covered : formulaCovered PureArithmeticStage.functionCovered
    PureNaturalRelations.relationCovered specification = true := rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTransitiveClosure
