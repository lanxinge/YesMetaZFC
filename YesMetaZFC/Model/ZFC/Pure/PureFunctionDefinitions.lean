import YesMetaZFC.Model.ZFC.Pure.PureModel
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Language
import YesMetaZFC.Model.Interpretation.RelationalExpansion

/-! # 基础支撑函数的实际纯隶属定义

空集、配对、单集、并集、幂集及后继直接定义为纯语言 ℒ 中的关系图。
每张图的任意对象参数存在唯一性由裸 ZFC 的模型公理证明；不把定义作为新公理假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFunctionDefinitions
open _root_.YesMetaZFC.Automation.RelationalTranslation
open PureModel
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x

private def mem {bound free : SortContext ℒ}
    (left right : Term ℒ bound free setSort) : Formula ℒ bound free :=
  .rel _root_.YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))

/-- 从“候选元素、参数”正文进入“输出、参数”关系图内部。 -/
def conditionSubstitution {parameters : SortContext ℒ} :
    VariableSubstitution ℒ (setSort :: parameters) [setSort] (setSort :: parameters) :=
  fun entry => match entry with
  | .here => .bvar .here
  | .there previous => .fvar (.there previous)

def comprehension {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: parameters)) :
    Formula ℒ [] (setSort :: parameters) :=
  .forallE setSort (.iff (mem (.bvar .here) (.fvar .here))
    (body.substituteMapped VariableSubstitution.empty conditionSubstitution))

private theorem condition_correct {M : Structure.{0, 0, 0, x} ℒ} {parameters : SortContext ℒ}
    (body : Formula ℒ [] (setSort :: parameters)) (args : Values M.Carrier parameters) (output element : Carrier M) :
    (body.substituteMapped VariableSubstitution.empty conditionSubstitution).satisfies
        ((templateEnv (.cons output args)).pushBound element) ↔
      body.satisfies (templateEnv (.cons element args)) := by
  have h := Formula.satisfies_substitute ((templateEnv (.cons output args)).pushBound element)
    (Substitution.map VariableSubstitution.empty conditionSubstitution) body
  change (body.substituteMapped VariableSubstitution.empty conditionSubstitution).satisfies _ ↔ _ at h
  have hEnv : ((templateEnv (.cons output args)).pushBound element).pullback
      (Substitution.map VariableSubstitution.empty conditionSubstitution) = templateEnv (.cons element args) := by
    apply Env.ext
    · intro sort entry
      exact nomatch entry
    · intro sort entry
      cases entry <;> rfl
  rwa [hEnv] at h

/-- 定义图准确表达按成员条件指定一个集合。 -/
theorem comprehension_correct {M : Structure.{0, 0, 0, x} ℒ} {parameters : SortContext ℒ}
    (body : Formula ℒ [] (setSort :: parameters)) (args : Values M.Carrier parameters) (output : Carrier M) :
    (comprehension body).satisfies (templateEnv (.cons output args)) ↔
      ∀ element, membership M element output ↔ body.satisfies (templateEnv (.cons element args)) := by
  constructor
  · intro h element
    exact (h element).trans (condition_correct body args output element)
  · intro h element
    exact (h element).trans (condition_correct body args output element).symm

/-- 任意成员条件的图由裸 ZFC 外延性保证输出唯一。 -/
theorem comprehension_unique {M : Structure.{0, 0, 0, x} ℒ} (hM : Theory.Models M PureModel.theory)
    {parameters : SortContext ℒ} (body : Formula ℒ [] (setSort :: parameters))
    (args : Values M.Carrier parameters) (left right : Carrier M)
    (hLeft : (comprehension body).satisfies (templateEnv (.cons left args)))
    (hRight : (comprehension body).satisfies (templateEnv (.cons right args))) : left = right :=
  PureModel.extensionality hM left right (fun element =>
    ((comprehension_correct body args left).mp hLeft element).trans
      ((comprehension_correct body args right).mp hRight element).symm)

private def emptyBody : Formula ℒ [] [setSort] := .falsum
private def pairBody : Formula ℒ [] [setSort, setSort, setSort] :=
  .disj (.equal (.fvar .here) (.fvar (.there .here)))
    (.equal (.fvar .here) (.fvar (.there (.there .here))))
private def singletonBody : Formula ℒ [] [setSort, setSort] :=
  .equal (.fvar .here) (.fvar (.there .here))
private def unionBody : Formula ℒ [] [setSort, setSort] :=
  .existsE setSort (.conj (mem (.bvar .here) (.fvar (.there .here))) (mem (.fvar .here) (.bvar .here)))
private def powerBody : Formula ℒ [] [setSort, setSort] :=
  .forallE setSort (.imp (mem (.bvar .here) (.fvar .here)) (mem (.bvar .here) (.fvar (.there .here))))
private def successorBody : Formula ℒ [] [setSort, setSort] :=
  .disj (mem (.fvar .here) (.fvar (.there .here))) (.equal (.fvar .here) (.fvar (.there .here)))

/-- 已具体消去的函数，索引就是原支撑签名的函数符号。 -/
inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | emptySet : Primitive .emptySet
  | unorderedPair : Primitive .unorderedPair
  | singleton : Primitive .singleton
  | union : Primitive .union
  | powerSet : Primitive .powerSet
  | successor : Primitive .successor

def parameterSorts (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) : SortContext ℒ :=
  (Nonlogical.BasicSetTheory.signature.funcDomain symbol).map (fun _ => setSort)

attribute [local implicit_reducible] parameterSorts

/-- 可直接填入全语言关系解释的实际函数定义图。 -/
def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: parameterSorts symbol) :=
  match primitive with
  | .emptySet => comprehension emptyBody
  | .unorderedPair => comprehension pairBody
  | .singleton => comprehension singletonBody
  | .union => comprehension unionBody
  | .powerSet => comprehension powerBody
  | .successor => comprehension successorBody

/-- 三个基础图的直接成员规格，供复合集合定义复用。 -/
theorem empty_correct {M : Structure.{0, 0, 0, x} ℒ} (output : Carrier M) :
    (graph .emptySet).satisfies (templateEnv (.cons output .nil)) ↔
      ∀ element, ¬ membership M element output := by
  rw [graph, comprehension_correct]
  simp only [emptyBody, Formula.satisfies, iff_false]

theorem pair_correct {M : Structure.{0, 0, 0, x} ℒ} (output left right : Carrier M) :
    (graph .unorderedPair).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      ∀ element, membership M element output ↔ element = left ∨ element = right := by
  rw [graph, comprehension_correct]
  rfl

theorem singleton_correct {M : Structure.{0, 0, 0, x} ℒ} (output element : Carrier M) :
    (graph .singleton).satisfies (templateEnv (.cons output (.cons element .nil))) ↔
      ∀ member, membership M member output ↔ member = element := by
  rw [graph, comprehension_correct]
  rfl

theorem union_correct {M : Structure.{0, 0, 0, x} ℒ} (output input : Carrier M) :
    (graph .union).satisfies (templateEnv (.cons output (.cons input .nil))) ↔
      ∀ element, membership M element output ↔ ∃ member, membership M member input ∧ membership M element member := by
  rw [graph, comprehension_correct]
  rfl

theorem successor_correct {M : Structure.{0, 0, 0, x} ℒ} (output input : Carrier M) :
    (graph .successor).satisfies (templateEnv (.cons output (.cons input .nil))) ↔
      ∀ element, membership M element output ↔ membership M element input ∨ element = input := by
  rw [graph, comprehension_correct]
  rfl

/-- 各图的存在性来自裸 ZFC 公理或配对、并集构造。 -/
theorem exists_output {M : Structure.{0, 0, 0, x} ℒ} (hM : Theory.Models M PureModel.theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values M.Carrier (parameterSorts symbol)) :
    ∃ output : Carrier M, (graph primitive).satisfies (templateEnv (.cons output args)) := by
  cases primitive with
  | emptySet =>
    cases args
    obtain ⟨output, hOutput⟩ := PureModel.empty hM
    refine ⟨output, (comprehension_correct emptyBody .nil output).mpr ?_⟩
    intro element
    exact ⟨fun h => hOutput element h, False.elim⟩
  | unorderedPair =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    obtain ⟨output, hOutput⟩ := PureModel.pair hM left right
    exact ⟨output, (comprehension_correct pairBody _ output).mpr hOutput⟩
  | singleton =>
    cases args with | cons input tail =>
    cases tail
    obtain ⟨output, hOutput⟩ := PureModel.singleton hM input
    exact ⟨output, (comprehension_correct singletonBody _ output).mpr hOutput⟩
  | union =>
    cases args with | cons input tail =>
    cases tail
    obtain ⟨output, hOutput⟩ := PureModel.union hM input
    exact ⟨output, (comprehension_correct unionBody _ output).mpr hOutput⟩
  | powerSet =>
    cases args with | cons input tail =>
    cases tail
    obtain ⟨output, hOutput⟩ := PureModel.power hM input
    exact ⟨output, (comprehension_correct powerBody _ output).mpr hOutput⟩
  | successor =>
    cases args with | cons input tail =>
    cases tail
    obtain ⟨output, hOutput⟩ := PureModel.successor hM input
    exact ⟨output, (comprehension_correct successorBody _ output).mpr hOutput⟩

/-- 六种实际基础函数对任意参数都有唯一输出，不依赖支撑理论的一致性或模型。 -/
theorem functional {M : Structure.{0, 0, 0, x} ℒ} (hM : Theory.Models M PureModel.theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values M.Carrier (parameterSorts symbol)) :
    ∃ output : Carrier M, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  obtain ⟨output, hOutput⟩ := exists_output hM primitive args
  refine ⟨output, hOutput, ?_⟩
  intro other hOther
  cases primitive <;> exact comprehension_unique hM _ args other output hOther hOutput

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFunctionDefinitions
