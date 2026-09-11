import YesMetaZFC.Model.ZFC.Pure.PureProjectTemplate
import YesMetaZFC.Model.ZFC.Pure.PureRelationFunctions
import YesMetaZFC.SetTheory.Ord.Natural

/-! # 最小归纳集与有序对反转的纯图

ω 的存在性直接来自裸 ZF 的最小归纳集构造，模型与对象参数均显式传入。
有序对反转对任意输入先取两个总投影，再按相反次序组成有序对；这精确保留原无 guard 定义。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOmegaAndReverse
open PureModel PureRelationDefinitions
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureFunctionDefinitions.parameterSorts
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

def omegaBody : Project.Formula 1 1 := Project.Formula.isOmega (.bound 0)

theorem omegaBody_closed : omegaBody.FreeClosed := by
  simp [omegaBody, Project.Formula.isOmega, Project.Formula.isInductive, Project.Formula.isEmpty,
    Project.Formula.isSuccessor, Project.Formula.forallMem, Project.Formula.extensionalEq,
    Project.Formula.subset, _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.newest]

def omegaGraph : Formula ℒ [] [setSort] := PureProjectTemplate.toPure omegaBody omegaBody_closed

theorem omega_correct (hℳ : Theory.Models ℳ theory) (output : Carrier ℳ) :
    omegaGraph.satisfies (templateEnv (.cons output .nil)) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsOmega output :=
  (PureProjectTemplate.correct hℳ omegaBody omegaBody_closed (.cons output .nil) output).trans
    (Project.Formula.satisfies_isOmega_iff _ (.bound 0))

/-- “属于每个归纳集”与最小归纳集图等价；原归纳核规格见 PureRoundOneSpecifications。 -/
theorem omega_membership_spec (hℳ : Theory.Models ℳ theory) (output : Carrier ℳ) :
    omegaGraph.satisfies (templateEnv (.cons output .nil)) ↔
      ∀ element, membership ℳ element output ↔ ∀ inductiveSet,
        (Project.FirstOrderSemantics.reduct ℳ).IsInductive inductiveSet → membership ℳ element inductiveSet := by
  rw [omega_correct hℳ]
  constructor
  · intro hOmega element
    exact ⟨fun hMember inductiveSet hInductive => hOmega.2 inductiveSet hInductive element hMember,
      fun hMember => hMember output hOmega.1⟩
  · intro hSpec
    obtain ⟨omega, hOmega⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_omega (project_modelsZF hℳ)
    have hEq : output = omega := extensionality hℳ output omega (fun element =>
      (hSpec element).trans ⟨fun h => h omega hOmega.1,
        fun h inductiveSet hInductive => hOmega.2 inductiveSet hInductive element h⟩)
    exact hEq ▸ hOmega

def reverseBody : Formula ℒ [] [setSort, setSort] :=
  .existsE setSort <| .existsE setSort <|
    .conj (code (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (code (.fvar .here) (.bvar .here) (.bvar (.there .here)))

theorem reverseBody_correct (output input : Carrier ℳ) :
    reverseBody.satisfies (templateEnv (.cons output (.cons input .nil))) ↔
      ∃ left right, PureKuratowski.Code ℳ input left right ∧ PureKuratowski.Code ℳ output right left := by
  simp only [reverseBody, Formula.satisfies, code_satisfies]
  rfl

/-- 原反转定义没有有序对 guard；总投影的任意输入值都必须进入反转结果。 -/
def reverseGraph : Formula ℒ [] [setSort, setSort] :=
  .existsE setSort <| .existsE setSort <|
    .conj (applyTemplate (PureRelationFunctions.graph .leftProjection)
      (.cons (.bvar (.there .here)) (.cons (.fvar (.there .here)) .nil))) <|
    .conj (applyTemplate (PureRelationFunctions.graph .rightProjection)
      (.cons (.bvar .here) (.cons (.fvar (.there .here)) .nil)))
      (code (.fvar .here) (.bvar .here) (.bvar (.there .here)))

theorem reverse_graph_correct (output input : Carrier ℳ) :
    reverseGraph.satisfies (templateEnv (.cons output (.cons input .nil))) ↔
      ∃ left right,
        (PureRelationFunctions.graph .leftProjection).satisfies (templateEnv (.cons left (.cons input .nil))) ∧
        (PureRelationFunctions.graph .rightProjection).satisfies (templateEnv (.cons right (.cons input .nil))) ∧
        PureKuratowski.Code ℳ output right left := by
  simp only [reverseGraph, Formula.satisfies, applyTemplate_satisfies, code_satisfies]
  rfl

theorem reverse_correct (_hℳ : Theory.Models ℳ theory) {input left right : Carrier ℳ}
    (hCode : PureKuratowski.Code ℳ input left right) (output : Carrier ℳ) :
    reverseGraph.satisfies (templateEnv (.cons output (.cons input .nil))) ↔
      PureKuratowski.Code ℳ output right left := by
  rw [reverse_graph_correct]
  constructor
  · rintro ⟨selectedLeft, selectedRight, hLeft, hRight, hOutput⟩
    have hLeftEq := (PureRelationFunctions.left_value hCode selectedLeft).mp hLeft
    have hRightEq := (PureRelationFunctions.right_value hCode selectedRight).mp hRight
    subst selectedLeft; subst selectedRight
    exact hOutput
  · intro hOutput
    exact ⟨left, right, (PureRelationFunctions.left_value hCode left).mpr rfl,
      (PureRelationFunctions.right_value hCode right).mpr rfl, hOutput⟩

inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | omega : Primitive .omega
  | orderedPairReverse : Primitive .orderedPairReverse

def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match primitive with
  | .omega => omegaGraph
  | .orderedPairReverse => reverseGraph

theorem functional (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output : Carrier ℳ, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  cases primitive with
  | omega =>
    cases args
    obtain ⟨omega, hOmega⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_omega (project_modelsZF hℳ)
    refine ⟨omega, (omega_correct hℳ omega).mpr hOmega, ?_⟩
    intro other hOther
    have hOtherOmega := (omega_correct hℳ other).mp hOther
    exact extensionality hℳ other omega (fun element =>
      ⟨hOtherOmega.2 omega hOmega.1 element, hOmega.2 other hOtherOmega.1 element⟩)
  | orderedPairReverse =>
    cases args with | cons input tail =>
    cases tail
    obtain ⟨left, hLeft, hLeftUnique⟩ := PureRelationFunctions.functional hℳ .leftProjection (.cons input .nil)
    obtain ⟨right, hRight, hRightUnique⟩ := PureRelationFunctions.functional hℳ .rightProjection (.cons input .nil)
    obtain ⟨output, hOutput⟩ := PureKuratowski.exists_code hℳ right left
    refine ⟨output, (reverse_graph_correct output input).mpr ⟨left, right, hLeft, hRight, hOutput⟩, ?_⟩
    intro other hOther
    obtain ⟨otherLeft, otherRight, hOtherLeft, hOtherRight, hOtherCode⟩ := (reverse_graph_correct other input).mp hOther
    have hLeftEq := hLeftUnique otherLeft hOtherLeft
    have hRightEq := hRightUnique otherRight hOtherRight
    subst otherLeft; subst otherRight
    exact PureKuratowski.code_unique hℳ hOtherCode hOutput

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOmegaAndReverse
