import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureProjectTemplate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRelationCoordinates
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureMappingOperations
import YesMetaZFC.SetTheory.Ord.Natural

/-! # 第一轮的七个分离构造

每个图都是纯隶属公式；存在性由明确母集上的分离给出，唯一性来自外延性。
复合成员规格采用“先第一关系，再第二关系”；函数图按原项 `second ∘ first` 接线。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationSetOperations
open PureModel
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
open PureProjectTemplate
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureFunctionDefinitions.parameterSorts
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

def binaryUnionMember (ℳ : Structure.{0, 0, 0, x} ℒ) (left right element : Carrier ℳ) : Prop :=
  membership ℳ element left ∨ membership ℳ element right

def binaryUnionSchema : Project.UnarySchema 2 where
  body := .disj (.mem (.bound 0) (.bound 1)) (.mem (.bound 0) (.bound 2))
theorem binaryUnionSchema_correct (_hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 2) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) binaryUnionSchema.body ↔
      binaryUnionMember ℳ (env.bound 0) (env.bound 1) element := by
  simp only [binaryUnionSchema,
    Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff]
  rfl

def binaryUnionGraph : Formula ℒ [] (Project.fo_bound_context 3) := setGraph binaryUnionSchema

theorem binaryUnion_correct (hℳ : Theory.Models ℳ theory) (output left right : Carrier ℳ) :
    binaryUnionGraph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      ∀ element, membership ℳ element output ↔ binaryUnionMember ℳ left right element := by
  apply Iff.trans (setGraph_correct hℳ binaryUnionSchema (.cons left (.cons right .nil)) output left)
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (binaryUnionSchema_correct hℳ (parameterEnv (.cons left (.cons right .nil)) left) element)

def symmetricDifferenceMember (ℳ : Structure.{0, 0, 0, x} ℒ) (left right element : Carrier ℳ) : Prop :=
  (membership ℳ element left ∧ ¬ membership ℳ element right) ∨
    (membership ℳ element right ∧ ¬ membership ℳ element left)

def symmetricDifferenceSchema : Project.UnarySchema 2 where
  body := .disj (.conj (.mem (.bound 0) (.bound 1)) (.neg (.mem (.bound 0) (.bound 2))))
    (.conj (.mem (.bound 0) (.bound 2)) (.neg (.mem (.bound 0) (.bound 1))))
theorem symmetricDifferenceSchema_correct (_hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 2) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) symmetricDifferenceSchema.body ↔
      symmetricDifferenceMember ℳ (env.bound 0) (env.bound 1) element := by
  simp only [symmetricDifferenceSchema,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff]
  rfl

def symmetricDifferenceGraph : Formula ℒ [] (Project.fo_bound_context 3) := setGraph symmetricDifferenceSchema

theorem symmetricDifference_correct (hℳ : Theory.Models ℳ theory) (output left right : Carrier ℳ) :
    symmetricDifferenceGraph.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      ∀ element, membership ℳ element output ↔ symmetricDifferenceMember ℳ left right element := by
  apply Iff.trans (setGraph_correct hℳ symmetricDifferenceSchema (.cons left (.cons right .nil)) output left)
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (symmetricDifferenceSchema_correct hℳ (parameterEnv (.cons left (.cons right .nil)) left) element)

def relationConverseMember (ℳ : Structure.{0, 0, 0, x} ℒ) (relation element : Carrier ℳ) : Prop :=
  ∃ left right, PureKuratowski.Code ℳ element left right ∧ PureKuratowski.PairMember ℳ right left relation

def relationConverseSchema : Project.UnarySchema 1 where
  body := .existsE <| .existsE <| .conj
    (PureKuratowskiProject.convention.code (.bound 2) (.bound 1) (.bound 0))
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 1) (.bound 3))
theorem relationConverseSchema_correct (hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) relationConverseSchema.body ↔
      relationConverseMember ℳ (env.bound 0) element := by
  simp only [relationConverseSchema,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_orderedPairMem_iff (PureKuratowskiProject.interpretation hℳ),
    (PureKuratowskiProject.interpretation hℳ).satisfies_code_iff,
    Project.Term.eval_bound_zero_push,
    Project.Term.eval_bound_one_push,
    Project.Term.eval_bound_two_push,
    Project.Term.eval_bound_three_push]
  rfl

def relationConverseGraph : Formula ℒ [] (Project.fo_bound_context 2) := setGraph relationConverseSchema

theorem relationConverse_correct (hℳ : Theory.Models ℳ theory) (output relation : Carrier ℳ) :
    relationConverseGraph.satisfies (templateEnv (.cons output (.cons relation .nil))) ↔
      ∀ element, membership ℳ element output ↔ relationConverseMember ℳ relation element := by
  apply Iff.trans (setGraph_correct hℳ relationConverseSchema (.cons relation .nil) output relation)
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (relationConverseSchema_correct hℳ (parameterEnv (.cons relation .nil) relation) element)

def relationCompositionMember (ℳ : Structure.{0, 0, 0, x} ℒ) (first second element : Carrier ℳ) : Prop :=
  ∃ left right middle, PureKuratowski.Code ℳ element left right ∧
    PureKuratowski.PairMember ℳ left middle first ∧ PureKuratowski.PairMember ℳ middle right second

def relationCompositionSchema : Project.UnarySchema 2 where
  body := .existsE <| .existsE <| .existsE <| .conj
    (PureKuratowskiProject.convention.code (.bound 3) (.bound 2) (.bound 1)) <| .conj
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 2) (.bound 0) (.bound 4))
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 1) (.bound 5))
theorem relationCompositionSchema_correct (hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 2) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) relationCompositionSchema.body ↔
      relationCompositionMember ℳ (env.bound 0) (env.bound 1) element := by
  simp only [relationCompositionSchema,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_orderedPairMem_iff (PureKuratowskiProject.interpretation hℳ),
    (PureKuratowskiProject.interpretation hℳ).satisfies_code_iff,
    Project.Term.eval_bound_zero_push,
    Project.Term.eval_bound_one_push,
    Project.Term.eval_bound_two_push,
    Project.Term.eval_bound_three_push,
    Project.Term.eval_bound_four_push,
    Project.Term.eval_bound_five_push]
  rfl

/-- 原函数项的两个槽是外层关系、内层关系；成员规格的执行顺序相反。 -/
def relationCompositionGraph : Formula ℒ [] (Project.fo_bound_context 3) :=
  applyTemplate (setGraph relationCompositionSchema)
    (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there .here)) .nil)))

theorem relationComposition_order (output second first : Carrier ℳ) :
    relationCompositionGraph.satisfies (templateEnv (.cons output (.cons second (.cons first .nil)))) ↔
      (setGraph relationCompositionSchema).satisfies (templateEnv (.cons output (.cons first (.cons second .nil)))) := by
  rw [relationCompositionGraph, applyTemplate_satisfies]
  rfl

theorem relationComposition_correct (hℳ : Theory.Models ℳ theory) (output first second : Carrier ℳ) :
    relationCompositionGraph.satisfies (templateEnv (.cons output (.cons second (.cons first .nil)))) ↔
      ∀ element, membership ℳ element output ↔ relationCompositionMember ℳ first second element := by
  rw [relationComposition_order]
  apply Iff.trans (setGraph_correct hℳ relationCompositionSchema (.cons first (.cons second .nil)) output first)
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (relationCompositionSchema_correct hℳ (parameterEnv (.cons first (.cons second .nil)) first) element)

def membershipRelationMember (ℳ : Structure.{0, 0, 0, x} ℒ) (source element : Carrier ℳ) : Prop :=
  ∃ left right, membership ℳ left source ∧ membership ℳ right source ∧
    PureKuratowski.Code ℳ element left right ∧ membership ℳ left right

def membershipRelationSchema : Project.UnarySchema 1 where
  body := .existsE <| .existsE <| .conj (.mem (.bound 1) (.bound 3)) <|
    .conj (.mem (.bound 0) (.bound 3)) <| .conj
    (PureKuratowskiProject.convention.code (.bound 2) (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))
theorem membershipRelationSchema_correct (hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) membershipRelationSchema.body ↔
      membershipRelationMember ℳ (env.bound 0) element := by
  simp only [membershipRelationSchema,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    (PureKuratowskiProject.interpretation hℳ).satisfies_code_iff,
    Project.Term.eval_bound_zero_push,
    Project.Term.eval_bound_one_push,
    Project.Term.eval_bound_two_push,
    Project.Term.eval_bound_three_push]
  rfl

def membershipRelationGraph : Formula ℒ [] (Project.fo_bound_context 2) := setGraph membershipRelationSchema

theorem membershipRelation_correct (hℳ : Theory.Models ℳ theory) (output source : Carrier ℳ) :
    membershipRelationGraph.satisfies (templateEnv (.cons output (.cons source .nil))) ↔
      ∀ element, membership ℳ element output ↔ membershipRelationMember ℳ source element := by
  apply Iff.trans (setGraph_correct hℳ membershipRelationSchema (.cons source .nil) output source)
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (membershipRelationSchema_correct hℳ (parameterEnv (.cons source .nil) source) element)

def imageMember (ℳ : Structure.{0, 0, 0, x} ℒ) (function source element : Carrier ℳ) : Prop :=
  ∃ input, membership ℳ input source ∧ PureKuratowski.PairMember ℳ input element function

def imageSchema : Project.UnarySchema 2 where
  body := .existsE <| .conj (.mem (.bound 0) (.bound 3))
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 1) (.bound 2))
theorem imageSchema_correct (hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 2) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) imageSchema.body ↔
      imageMember ℳ (env.bound 0) (env.bound 1) element := by
  simp only [imageSchema,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (PureKuratowskiProject.interpretation hℳ),
    Project.Term.eval_bound_zero_push,
    Project.Term.eval_bound_one_push,
    Project.Term.eval_bound_two_push,
    Project.Term.eval_bound_three_push]
  rfl

def imageGraph : Formula ℒ [] (Project.fo_bound_context 3) := setGraph imageSchema

theorem image_correct (hℳ : Theory.Models ℳ theory) (output function source : Carrier ℳ) :
    imageGraph.satisfies (templateEnv (.cons output (.cons function (.cons source .nil)))) ↔
      ∀ element, membership ℳ element output ↔ imageMember ℳ function source element := by
  apply Iff.trans (setGraph_correct hℳ imageSchema (.cons function (.cons source .nil)) output function)
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (imageSchema_correct hℳ (parameterEnv (.cons function (.cons source .nil)) function) element)

def inductiveCoreMember (ℳ : Structure.{0, 0, 0, x} ℒ) (source element : Carrier ℳ) : Prop :=
  membership ℳ element source ∧
    ∀ inductiveSet, (Project.FirstOrderSemantics.reduct ℳ).IsInductive inductiveSet → membership ℳ element inductiveSet

def inductiveCoreSchema : Project.UnarySchema 1 where
  body := .conj (.mem (.bound 0) (.bound 1)) <| .forallE <|
    .imp (Project.Formula.isInductive (.bound 0)) (.mem (.bound 1) (.bound 0))
theorem inductiveCoreSchema_correct (_hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) inductiveCoreSchema.body ↔
      inductiveCoreMember ℳ (env.bound 0) element := by
  simp only [inductiveCoreSchema,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isInductive_iff,
    Project.Term.eval_bound_zero_push,
    Project.Term.eval_bound_one_push]
  rfl

def inductiveCoreGraph : Formula ℒ [] (Project.fo_bound_context 2) := setGraph inductiveCoreSchema

theorem inductiveCore_correct (hℳ : Theory.Models ℳ theory) (output source : Carrier ℳ) :
    inductiveCoreGraph.satisfies (templateEnv (.cons output (.cons source .nil))) ↔
      ∀ element, membership ℳ element output ↔ inductiveCoreMember ℳ source element := by
  apply Iff.trans (setGraph_correct hℳ inductiveCoreSchema (.cons source .nil) output source)
  apply forall_congr'
  intro element
  exact iff_congr Iff.rfl (inductiveCoreSchema_correct hℳ (parameterEnv (.cons source .nil) source) element)

inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | binaryUnion : Primitive .binaryUnion
  | symmetricDifference : Primitive .symmetricDifference
  | relationConverse : Primitive .relationConverse
  | relationComposition : Primitive .relationComposition
  | membershipRelation : Primitive .membershipRelation
  | image : Primitive .image
  | inductiveCore : Primitive .inductiveCore

def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match primitive with
  | .binaryUnion => binaryUnionGraph
  | .symmetricDifference => symmetricDifferenceGraph
  | .relationConverse => relationConverseGraph
  | .relationComposition => relationCompositionGraph
  | .membershipRelation => membershipRelationGraph
  | .image => imageGraph
  | .inductiveCore => inductiveCoreGraph

/-- 七个函数在裸 ZFC 模型中对任意参数都有唯一输出。 -/
theorem functional (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output : Carrier ℳ, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  cases primitive with
  | binaryUnion =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    obtain ⟨ambient, hAmbient⟩ := _root_.YesMetaZFC.SetTheory.KP.exists_unionOfTwo
      (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ)) left right
    apply bounded_functional hℳ binaryUnionSchema (.cons left (.cons right .nil)) left ambient
    intro element hElement
    exact (hAmbient element).mpr ((binaryUnionSchema_correct hℳ _ element).mp hElement)
  | symmetricDifference =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    obtain ⟨ambient, hAmbient⟩ := _root_.YesMetaZFC.SetTheory.KP.exists_unionOfTwo
      (_root_.YesMetaZFC.SetTheory.ZF.modelsKP (project_modelsZF hℳ)) left right
    apply bounded_functional hℳ symmetricDifferenceSchema (.cons left (.cons right .nil)) left ambient
    intro element hElement
    have h := (symmetricDifferenceSchema_correct hℳ _ element).mp hElement
    exact (hAmbient element).mpr (h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  | relationConverse =>
    cases args with | cons relation tail =>
    cases tail
    obtain ⟨domain, hDomain⟩ := PureRelationCoordinates.exists_coordinate hℳ .domain relation
    obtain ⟨range, hRange⟩ := PureRelationCoordinates.exists_coordinate hℳ .range relation
    obtain ⟨ambient, hAmbient⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_cartesianProduct
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) range domain
    apply bounded_functional hℳ relationConverseSchema (.cons relation .nil) relation ambient
    intro element hElement
    obtain ⟨left, right, hCode, hPair⟩ := (relationConverseSchema_correct hℳ _ element).mp hElement
    exact (hAmbient element).mpr ⟨left,
      ((PureRelationCoordinates.coordinate_correct .range range relation).mp hRange left).mpr ⟨right, hPair⟩,
      right, ((PureRelationCoordinates.coordinate_correct .domain domain relation).mp hDomain right).mpr
        ⟨left, hPair⟩, hCode⟩
  | relationComposition =>
    cases args with | cons second tail =>
    cases tail with | cons first tail =>
    cases tail
    obtain ⟨domain, hDomain⟩ := PureRelationCoordinates.exists_coordinate hℳ .domain first
    obtain ⟨range, hRange⟩ := PureRelationCoordinates.exists_coordinate hℳ .range second
    obtain ⟨ambient, hAmbient⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_cartesianProduct
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) domain range
    have hNative := bounded_functional hℳ relationCompositionSchema
      (.cons first (.cons second .nil)) first ambient (by
        intro element hElement
        obtain ⟨left, right, middle, hCode, hFirst, hSecond⟩ :=
          (relationCompositionSchema_correct hℳ _ element).mp hElement
        exact (hAmbient element).mpr ⟨left,
          ((PureRelationCoordinates.coordinate_correct .domain domain first).mp hDomain left).mpr ⟨middle, hFirst⟩,
          right, ((PureRelationCoordinates.coordinate_correct .range range second).mp hRange right).mpr
            ⟨middle, hSecond⟩, hCode⟩)
    obtain ⟨output, hOutput, hUnique⟩ := hNative
    exact ⟨output, (relationComposition_order output second first).mpr hOutput,
      fun other hOther => hUnique other ((relationComposition_order other second first).mp hOther)⟩
  | membershipRelation =>
    cases args with | cons source tail =>
    cases tail
    obtain ⟨ambient, hAmbient⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_cartesianProduct
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) source source
    apply bounded_functional hℳ membershipRelationSchema (.cons source .nil) source ambient
    intro element hElement
    obtain ⟨left, right, hLeft, hRight, hCode, _⟩ := (membershipRelationSchema_correct hℳ _ element).mp hElement
    exact (hAmbient element).mpr ⟨left, hLeft, right, hRight, hCode⟩
  | image =>
    cases args with | cons function tail =>
    cases tail with | cons source tail =>
    cases tail
    obtain ⟨range, hRange⟩ := PureRelationCoordinates.exists_coordinate hℳ .range function
    apply bounded_functional hℳ imageSchema (.cons function (.cons source .nil)) source range
    intro element hElement
    obtain ⟨input, _, hPair⟩ := (imageSchema_correct hℳ _ element).mp hElement
    exact ((PureRelationCoordinates.coordinate_correct .range range function).mp hRange element).mpr ⟨input, hPair⟩
  | inductiveCore =>
    cases args with | cons source tail =>
    cases tail
    apply bounded_functional hℳ inductiveCoreSchema (.cons source .nil) source source
    intro element hElement
    exact ((inductiveCoreSchema_correct hℳ _ element).mp hElement).1

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationSetOperations
