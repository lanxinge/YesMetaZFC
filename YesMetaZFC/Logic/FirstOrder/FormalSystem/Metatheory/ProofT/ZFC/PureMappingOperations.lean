import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureMappingDefinitions

/-! # 恒等映射和函数限制的纯定义

两个运算直接由分离构造：恒等图从源集的平方中筛出对角线，限制图从原集合中
筛出第一坐标属于给定子集的有序对。输出存在唯一对任意输入成立。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMappingOperations
open PureModel PureRelationDefinitions
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
attribute [local implicit_reducible] PureFunctionDefinitions.parameterSorts
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

def identityBody : Formula ℒ [] [setSort, setSort] :=
  .existsE setSort <| .conj (mem (.bvar .here) (.fvar (.there .here)))
    (code (.fvar .here) (.bvar .here) (.bvar .here))

def restrictionBody : Formula ℒ [] [setSort, setSort, setSort] :=
  .conj (mem (.fvar .here) (.fvar (.there .here))) <|
    .existsE setSort <| .existsE setSort <|
      .conj (mem (.bvar (.there .here)) (.fvar (.there (.there .here))))
        (code (.fvar .here) (.bvar (.there .here)) (.bvar .here))

inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | identity : Primitive .identity
  | restriction : Primitive .restriction

def body {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match primitive with
  | .identity => identityBody
  | .restriction => restrictionBody

def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  PureFunctionDefinitions.comprehension (body primitive)

theorem identity_correct (output source : Carrier ℳ) :
    (graph .identity).satisfies (templateEnv (.cons output (.cons source .nil))) ↔
      ∀ pair, membership ℳ pair output ↔
        ∃ input, membership ℳ input source ∧ PureKuratowski.Code ℳ pair input input := by
  rw [graph, PureFunctionDefinitions.comprehension_correct]
  simp only [body, identityBody, Formula.satisfies, code_satisfies]
  rfl

/-- 此成员规格就是原限制公理的正文，不依赖映射及子集 guard。 -/
theorem restriction_correct (output function source : Carrier ℳ) :
    (graph .restriction).satisfies (templateEnv (.cons output (.cons function (.cons source .nil)))) ↔
      ∀ pair, membership ℳ pair output ↔ membership ℳ pair function ∧
        ∃ input value, membership ℳ input source ∧ PureKuratowski.Code ℳ pair input value := by
  rw [graph, PureFunctionDefinitions.comprehension_correct]
  simp only [body, restrictionBody, Formula.satisfies, code_satisfies]
  rfl

private def identitySchema : Project.UnarySchema 1 where
  body := .existsE <| .conj (.mem (.bound 0) (.bound 2))
    (PureKuratowskiProject.convention.code (.bound 1) (.bound 0) (.bound 0))
private theorem identitySchema_correct (hℳ : Theory.Models ℳ theory)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1) (pair : Carrier ℳ) :
    Project.Formula.satisfies (env.push pair) identitySchema.body ↔
      ∃ input, membership ℳ input (env.bound 0) ∧ PureKuratowski.Code ℳ pair input input := by
  simp only [identitySchema, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, (PureKuratowskiProject.interpretation hℳ).satisfies_code_iff,
    Project.Term.eval_bound_zero_push, Project.Term.eval_bound_one_push, Project.Term.eval_bound_two_push]
  rfl

theorem exists_output (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output : Carrier ℳ, (graph primitive).satisfies (templateEnv (.cons output args)) := by
  cases primitive with
  | identity =>
    cases args with | cons source tail =>
    cases tail
    obtain ⟨product, hProduct⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_cartesianProduct
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) source source
    let env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1 :=
      { bound := fun _ => source, free := fun _ => source }
    obtain ⟨output, hOutput⟩ := _root_.YesMetaZFC.SetTheory.ZF.separation_exists_d
      (project_modelsZF hℳ) identitySchema env product
    refine ⟨output, (identity_correct output source).mpr ?_⟩
    intro pair
    have hCondition := identitySchema_correct hℳ env pair
    have hBound (h : ∃ input, membership ℳ input source ∧ PureKuratowski.Code ℳ pair input input) :
        membership ℳ pair product := by
      obtain ⟨input, hInput, hCode⟩ := h
      exact (hProduct pair).mpr ⟨input, hInput, input, hInput, hCode⟩
    exact (hOutput pair).trans ⟨fun h => hCondition.mp h.2, fun h =>
      ⟨hBound h, hCondition.mpr h⟩⟩
  | restriction =>
    cases args with | cons function tail =>
    cases tail with | cons source tail =>
    cases tail
    let env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1 :=
      { bound := fun _ => source, free := fun _ => source }
    obtain ⟨output, hOutput⟩ := _root_.YesMetaZFC.SetTheory.ZF.separation_exists_d (project_modelsZF hℳ)
      (Project.UnarySchema.restrictionMember PureKuratowskiProject.convention) env function
    refine ⟨output, (restriction_correct output function source).mpr ?_⟩
    intro pair
    have hCondition := Project.Formula.satisfies_restrictionMember_iff
      (PureKuratowskiProject.interpretation hℳ) env pair
    exact (hOutput pair).trans (and_congr Iff.rfl (hCondition.trans
      ⟨fun ⟨input, value, hCode, hInput⟩ => ⟨input, value, hInput, hCode⟩,
        fun ⟨input, value, hInput, hCode⟩ => ⟨input, value, hCode, hInput⟩⟩))

theorem functional (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output : Carrier ℳ, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  obtain ⟨output, hOutput⟩ := exists_output hℳ primitive args
  exact ⟨output, hOutput, fun other hOther =>
    PureFunctionDefinitions.comprehension_unique hℳ (body primitive) args other output hOther hOutput⟩

/-- 恒等图自动包含于源集平方，故保留原恒等公理的母集限制。 -/
theorem identity_spec (output source product : Carrier ℳ)
    (hProduct : (PureMappingDefinitions.graph .cartesianProduct).satisfies
      (templateEnv (.cons product (.cons source (.cons source .nil))))) :
    (graph .identity).satisfies (templateEnv (.cons output (.cons source .nil))) ↔
      ∀ pair, membership ℳ pair output ↔ membership ℳ pair product ∧
        ∃ input, membership ℳ input source ∧ PureKuratowski.Code ℳ pair input input := by
  rw [identity_correct]
  have hBound (pair : Carrier ℳ) (h : ∃ input, membership ℳ input source ∧ PureKuratowski.Code ℳ pair input input) :
      membership ℳ pair product := by
    obtain ⟨input, hInput, hCode⟩ := h
    exact ((PureMappingDefinitions.cartesian_correct product source source).mp hProduct pair).mpr
      ⟨input, hInput, input, hInput, hCode⟩
  exact ⟨fun h pair => (h pair).trans ⟨fun h => ⟨hBound pair h, h⟩, And.right⟩,
    fun h pair => (h pair).trans ⟨And.right, fun h => ⟨hBound pair h, h⟩⟩⟩

/-- 限制纯图实现集合构造库的关系限制语义，后续函数定理可直接复用。 -/
theorem restriction_project (hℳ : Theory.Models ℳ theory) (output function source : Carrier ℳ)
    (hGraph : (graph .restriction).satisfies (templateEnv (.cons output (.cons function (.cons source .nil))))) :
    (Project.FirstOrderSemantics.reduct ℳ).IsRestrictionOf (PureKuratowskiProject.interpretation hℳ)
      output function source := by
  have hSpec := (restriction_correct output function source).mp hGraph
  constructor
  · intro pair hPair
    obtain ⟨_, input, value, _, hCode⟩ := (hSpec pair).mp hPair
    exact ⟨input, value, hCode⟩
  · intro input value
    constructor
    · rintro ⟨pair, hCode, hPair⟩
      obtain ⟨hFunction, selectedInput, selectedValue, hInput, hSelected⟩ := (hSpec pair).mp hPair
      have hEq := (PureKuratowski.code_injective hCode hSelected).1
      exact ⟨hEq ▸ hInput, pair, hCode, hFunction⟩
    · rintro ⟨hInput, pair, hCode, hPair⟩
      exact ⟨pair, hCode, (hSpec pair).mpr ⟨hPair, input, value, hInput, hCode⟩⟩

/-- 映射限制到其源集的子集后仍是到原目标集的映射。 -/
theorem restriction_mapping (hℳ : Theory.Models ℳ theory) (output function source target subset : Carrier ℳ)
    (hGraph : (graph .restriction).satisfies (templateEnv (.cons output (.cons function (.cons subset .nil)))))
    (hMapping : PureMappingDefinitions.IsMapping ℳ function source target)
    (hSubset : ∀ input, membership ℳ input subset → membership ℳ input source) :
    PureMappingDefinitions.IsMapping ℳ output subset target :=
  (restriction_project hℳ output function subset hGraph).isSetFunctionFromTo hMapping hSubset

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMappingOperations
