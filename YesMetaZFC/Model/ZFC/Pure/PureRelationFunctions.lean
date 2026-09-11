import YesMetaZFC.Model.ZFC.Pure.PureRelationDefinitions

/-! # 有序对、投影及函数求值的实际总函数图

新图直接以原支撑签名的函数符号为索引。有序对无条件定义；投影和求值在原规格
有输出时保留该唯一输出，其余输入取空集。这种总化选择不加入原支撑理论。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationFunctions
open PureModel PureRelationDefinitions
open _root_.YesMetaZFC.Automation
open RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureFunctionDefinitions.parameterSorts
universe x

private theorem templateEnv_cons {ℳ : Structure.{0, 0, 0, x} ℒ} {parameters : SortContext ℒ}
    (args : Values ℳ.Carrier parameters) (output : Carrier ℳ) :
    templateEnv (.cons output args) = (templateEnv args).pushFree output := by
  apply Env.ext
  · intro sort entry
    exact nomatch entry
  · intro sort entry
    cases entry <;> rfl

def emptyFallback {parameters : SortContext ℒ} : Formula ℒ [] (setSort :: parameters) :=
  applyTemplate (PureFunctionDefinitions.graph .emptySet) (.cons (.fvar .here) .nil)

theorem emptyFallback_correct {ℳ : Structure.{0, 0, 0, x} ℒ} {parameters : SortContext ℒ}
    (args : Values ℳ.Carrier parameters) (output : Carrier ℳ) :
    (emptyFallback (parameters := parameters)).satisfies (templateEnv (.cons output args)) ↔
      ∀ element, ¬ membership ℳ element output :=
  (applyTemplate_satisfies _ _ _).trans (PureFunctionDefinitions.empty_correct output)

private theorem fallback_functional {ℳ : Structure.{0, 0, 0, x} ℒ}
    (hℳ : Theory.Models ℳ theory) {parameters : SortContext ℒ} (args : Values ℳ.Carrier parameters) :
    ∃ output, emptyFallback.satisfies ((templateEnv args).pushFree output) ∧
      ∀ other, emptyFallback.satisfies ((templateEnv args).pushFree other) → other = output := by
  obtain ⟨output, hOutput⟩ := empty hℳ
  have hCorrect := fun value => (templateEnv_cons args value) ▸ emptyFallback_correct args value
  refine ⟨output, (hCorrect output).mpr hOutput, ?_⟩
  intro other hOther
  have hEmpty := (hCorrect other).mp hOther
  exact extensionality hℳ other output (fun element =>
    ⟨fun h => False.elim (hEmpty element h), fun h => False.elim (hOutput element h)⟩)

theorem totalized_functional {ℳ : Structure.{0, 0, 0, x} ℒ}
    (hℳ : Theory.Models ℳ theory) {parameters : SortContext ℒ}
    (body : Formula ℒ [] (setSort :: parameters)) (args : Values ℳ.Carrier parameters)
    (hUnique : ∀ first second, body.satisfies (templateEnv (.cons first args)) →
      body.satisfies (templateEnv (.cons second args)) → first = second) :
    ∃ output, (TotalizedGraph.formula body emptyFallback).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (TotalizedGraph.formula body emptyFallback).satisfies (templateEnv (.cons other args)) → other = output := by
  simp only [templateEnv_cons] at hUnique ⊢
  exact TotalizedGraph.functional (templateEnv args) body emptyFallback hUnique (fallback_functional hℳ args)

theorem totalized_agrees {ℳ : Structure.{0, 0, 0, x} ℒ} {parameters : SortContext ℒ}
    (body : Formula ℒ [] (setSort :: parameters)) (args : Values ℳ.Carrier parameters)
    (hExists : ∃ output, body.satisfies (templateEnv (.cons output args))) (output : Carrier ℳ) :
    (TotalizedGraph.formula body emptyFallback).satisfies (templateEnv (.cons output args)) ↔
      body.satisfies (templateEnv (.cons output args)) := by
  simp only [templateEnv_cons] at hExists ⊢
  exact TotalizedGraph.agrees (templateEnv args) body emptyFallback hExists output

inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | orderedPair : Primitive .orderedPair
  | leftProjection : Primitive .leftProjection
  | rightProjection : Primitive .rightProjection
  | application : Primitive .application

def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match primitive with
  | .orderedPair => orderedPairGraph
  | .leftProjection => TotalizedGraph.formula leftBody emptyFallback
  | .rightProjection => TotalizedGraph.formula rightBody emptyFallback
  | .application => TotalizedGraph.formula applicationBody emptyFallback

theorem functional {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  cases primitive with
  | orderedPair =>
      cases args with | cons left tail =>
      cases tail with | cons right tail =>
      cases tail
      obtain ⟨output, hOutput⟩ := PureKuratowski.exists_code hℳ left right
      exact ⟨output, (orderedPair_correct output left right).mpr hOutput,
        fun other hOther => PureKuratowski.code_unique hℳ ((orderedPair_correct other left right).mp hOther) hOutput⟩
  | leftProjection =>
      cases args with | cons input tail =>
      cases tail
      exact totalized_functional hℳ leftBody _ (fun first second hFirst hSecond =>
        PureKuratowski.left_unique ((left_correct first input).mp hFirst) ((left_correct second input).mp hSecond))
  | rightProjection =>
      cases args with | cons input tail =>
      cases tail
      exact totalized_functional hℳ rightBody _ (fun first second hFirst hSecond =>
        PureKuratowski.right_unique ((right_correct first input).mp hFirst) ((right_correct second input).mp hSecond))
  | application =>
      cases args with | cons function tail =>
      cases tail with | cons input tail =>
      cases tail
      exact totalized_functional hℳ applicationBody _ (fun first second hFirst hSecond =>
        PureKuratowski.application_unique ((application_correct first function input).mp hFirst)
          ((application_correct second function input).mp hSecond))

/-- 合法有序对上左投影精确返回左坐标。 -/
theorem left_value {ℳ : Structure.{0, 0, 0, x} ℒ} {pair left right : Carrier ℳ}
    (hCode : PureKuratowski.Code ℳ pair left right) (output : Carrier ℳ) :
    (graph .leftProjection).satisfies (templateEnv (.cons output (.cons pair .nil))) ↔ output = left := by
  have hLeft : PureKuratowski.Left ℳ left pair := ⟨right, hCode⟩
  have hAgrees := totalized_agrees leftBody (.cons pair .nil)
    ⟨left, (left_correct left pair).mpr hLeft⟩ output
  exact hAgrees.trans ((left_correct output pair).trans
    ⟨fun h => PureKuratowski.left_unique h hLeft, fun h => h ▸ hLeft⟩)

/-- 合法有序对上右投影精确返回右坐标。 -/
theorem right_value {ℳ : Structure.{0, 0, 0, x} ℒ} {pair left right : Carrier ℳ}
    (hCode : PureKuratowski.Code ℳ pair left right) (output : Carrier ℳ) :
    (graph .rightProjection).satisfies (templateEnv (.cons output (.cons pair .nil))) ↔ output = right := by
  have hRight : PureKuratowski.Right ℳ right pair := ⟨left, hCode⟩
  have hAgrees := totalized_agrees rightBody (.cons pair .nil)
    ⟨right, (right_correct right pair).mpr hRight⟩ output
  exact hAgrees.trans ((right_correct output pair).trans
    ⟨fun h => PureKuratowski.right_unique h hRight, fun h => h ▸ hRight⟩)

/-- 函数定义域内的求值精确保留原图中的唯一值。 -/
theorem application_value {ℳ : Structure.{0, 0, 0, x} ℒ} {function input value : Carrier ℳ}
    (hFunction : PureKuratowski.IsFunction ℳ function)
    (hValue : PureKuratowski.PairMember ℳ input value function) (output : Carrier ℳ) :
    (graph .application).satisfies (templateEnv (.cons output (.cons function (.cons input .nil)))) ↔ output = value := by
  have hBody : PureKuratowski.Application ℳ value function input := ⟨hFunction, hValue⟩
  have hAgrees := totalized_agrees applicationBody (.cons function (.cons input .nil))
    ⟨value, (application_correct value function input).mpr hBody⟩ output
  exact hAgrees.trans ((application_correct output function input).trans
    ⟨fun h => PureKuratowski.application_unique h hBody, fun h => h ▸ hBody⟩)

/-- 原左投影的“公共成员恰为指定坐标”规格。 -/
theorem left_spec {ℳ : Structure.{0, 0, 0, x} ℒ} {pair : Carrier ℳ}
    (hPair : ∃ left right, PureKuratowski.Code ℳ pair left right) (output : Carrier ℳ) :
    (graph .leftProjection).satisfies (templateEnv (.cons output (.cons pair .nil))) ↔
      ∀ element, (∀ member, membership ℳ member pair → membership ℳ element member) ↔ element = output := by
  obtain ⟨left, right, hCode⟩ := hPair
  rw [left_value hCode]
  constructor
  · intro h
    subst output
    exact PureKuratowski.code_intersection hCode
  · intro h
    exact ((h left).mp ((PureKuratowski.code_intersection hCode left).mpr rfl)).symm

/-- 原右投影的“存在左坐标组成此有序对”规格。 -/
theorem right_spec {ℳ : Structure.{0, 0, 0, x} ℒ} {pair : Carrier ℳ}
    (hPair : ∃ left right, PureKuratowski.Code ℳ pair left right) (output : Carrier ℳ) :
    (graph .rightProjection).satisfies (templateEnv (.cons output (.cons pair .nil))) ↔
      ∃ left, PureKuratowski.Code ℳ pair left output := by
  obtain ⟨left, right, hCode⟩ := hPair
  exact (totalized_agrees rightBody (.cons pair .nil)
    ⟨right, (right_correct right pair).mpr ⟨left, hCode⟩⟩ output).trans (right_correct output pair)

/-- 函数及定义域成员条件下，总化求值图精确表达原函数图成员关系。 -/
theorem application_spec {ℳ : Structure.{0, 0, 0, x} ℒ} {function input : Carrier ℳ}
    (hFunction : PureKuratowski.IsFunction ℳ function)
    (hDomain : ∃ value, PureKuratowski.PairMember ℳ input value function) (output : Carrier ℳ) :
    (graph .application).satisfies (templateEnv (.cons output (.cons function (.cons input .nil)))) ↔
      PureKuratowski.PairMember ℳ input output function := by
  obtain ⟨value, hValue⟩ := hDomain
  rw [application_value hFunction hValue]
  exact ⟨fun h => h ▸ hValue, fun h => hFunction.2 input output value h hValue⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationFunctions
