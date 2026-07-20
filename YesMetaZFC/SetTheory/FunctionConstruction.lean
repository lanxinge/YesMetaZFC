import YesMetaZFC.SetTheory.Replacement
import YesMetaZFC.SetTheory.ProductConstruction

/-!
# 可定义关系的函数图构造

本层把对象语言可定义的单值二元关系统一收集为模型内部函数图。上层只需证明值关系在
给定源集上全定义、单值并落入目标集，即可得到真正的集合编码函数；单射和满射性质
继续由同一值关系验证。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Definitional
namespace Project

namespace FunctionGraphEmbedding

/-- 值关系进入函数图成员公式后的 bound 变量重排。 -/
def value {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 3) :=
  Fin.cases 0 <| Fin.cases 2 fun parameter =>
    ⟨parameter.val + 3, by omega⟩

end FunctionGraphEmbedding

namespace RelationGraphEmbedding

/-- 关系图成员公式中，原二元模式的输出、输入与参数位置。 -/
def value {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 3) :=
  Fin.cases 0 <| Fin.cases 1 fun parameter =>
    ⟨parameter.val + 3, by omega⟩

end RelationGraphEmbedding

namespace BinarySchema

/-- 恒等值关系。 -/
def identityValue : BinarySchema 0 where
  body := Formula.extensionalEq (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.extensionalEq, Formula.FreeClosed]

/-- 固定参数给出的常值关系。 -/
def constantValue : BinarySchema 1 where
  body := Formula.extensionalEq (.bound 0) (.bound 2)
  freeClosed := by
    simp [Formula.extensionalEq, Formula.FreeClosed]

/-- 给定函数图的逆值关系。 -/
def inverseValue
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := Formula.orderedPairMem 𝒞
    (.bound 0) (.bound 1) (.bound 2)
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed, Term.newest]

/-- 两个函数图依次作用得到的复合值关系。 -/
def compositionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (Formula.orderedPairMem 𝒞
      (.bound 2) (.bound 0) (.bound 3))
    (Formula.orderedPairMem 𝒞
      (.bound 0) (.bound 1) (.bound 4))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed, Term.newest]

/--
把输入输出值关系提升为函数图成员关系。

新模式的输出是编码对；存在量词绑定原值关系的输出。
-/
def functionGraph (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (schema : BinarySchema parameterCount) :
    BinarySchema parameterCount where
  body := .existsE <| .conj
    (schema.body.rename FunctionGraphEmbedding.value)
    (𝒞.code (.bound 1) (.bound 2) (.bound 0))
  freeClosed := by
    simp [Formula.FreeClosed, schema.freeClosed]

end BinarySchema

namespace Formula

/-- 恒等值关系的解释就是对象相等。 -/
theorem denote_identityValue_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    (env : Env ℳ 0) (input output : ℳ.Domain) :
    BinarySchema.identityValue.denote env input output ↔
      input = output := by
  simp only [BinarySchema.identityValue, BinarySchema.denote,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

/-- 常值关系的解释就是输出等于固定参数。 -/
theorem denote_constantValue_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    (env : Env ℳ 1) (input output : ℳ.Domain) :
    BinarySchema.constantValue.denote env input output ↔
      output = env.bound 0 := by
  simp only [BinarySchema.constantValue, BinarySchema.denote,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_two_push]
  rfl

/-- 逆值关系交换原函数图中的输入输出。 -/
theorem denote_inverseValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (input output : ℳ.Domain) :
    (BinarySchema.inverseValue 𝒞).denote env input output ↔
      ℳ.PairMember 𝕀 output input (env.bound 0) := by
  simp only [BinarySchema.inverseValue, BinarySchema.denote,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]
  rfl

/-- 复合值关系的解释就是存在一个中间函数值。 -/
theorem denote_compositionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.compositionValue 𝒞).denote env input output ↔
      ∃ middle,
        ℳ.PairMember 𝕀 input middle (env.bound 0) ∧
          ℳ.PairMember 𝕀 middle output (env.bound 1) := by
  simp only [BinarySchema.compositionValue, BinarySchema.denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push]
  rfl

private theorem reindex_functionGraphValue
    {ℳ : Structure.{u}} {parameterCount : Nat}
    (env : Env ℳ parameterCount)
    (input pair output : ℳ.Domain) :
    (((env.push input).push pair).push output).reindex
        (FunctionGraphEmbedding.value
          (parameterCount := parameterCount)) =
      (env.push input).push output := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry
    · rfl
    · refine Fin.cases ?_ (fun parameter => ?_) previous <;> rfl
  · rfl

/-- 函数图成员模式恰好编码原值关系中的一个输入输出对。 -/
theorem denote_functionGraph_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (schema : BinarySchema parameterCount)
    (env : Env ℳ parameterCount) (input pair : ℳ.Domain) :
    (schema.functionGraph 𝒞).denote env input pair ↔
      ∃ output,
        schema.denote env input output ∧
          𝕀.Codes pair input output := by
  simp only [BinarySchema.functionGraph, BinarySchema.denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    𝕀.satisfies_code_iff, Term.eval_bound_zero_push,
    Term.eval_bound_one_push, Term.eval_bound_two_push]
  constructor
  · rintro ⟨output, hValue, hCode⟩
    rw [Formula.satisfies_rename] at hValue
    exact ⟨output, by
      simpa only [reindex_functionGraphValue] using hValue, hCode⟩
  · rintro ⟨output, hValue, hCode⟩
    refine ⟨output, ?_, hCode⟩
    rw [Formula.satisfies_rename]
    simpa only [reindex_functionGraphValue] using hValue

end Formula

namespace UnarySchema

/-- 从笛卡尔积中筛出满足给定可定义二元关系的有序对。 -/
def relationMember
    (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (schema : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .existsE <| .existsE <| .conj
    (𝒞.code (.bound 2) (.bound 1) (.bound 0))
    (schema.body.rename RelationGraphEmbedding.value)
  freeClosed := by
    simp [Formula.FreeClosed, schema.freeClosed]

/-- 从关系集合中筛出第一坐标属于固定源集的有序对。 -/
def restrictionMember
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .existsE <| .existsE <| .conj
    (𝒞.code (.bound 2) (.bound 1) Term.newest)
    (.mem (.bound 1) (.bound 3))
  freeClosed := by
    simp [Formula.FreeClosed,
      Term.newest]

end UnarySchema

namespace Formula

private theorem reindex_relationGraphValue
    {ℳ : Structure.{u}} {parameterCount : Nat}
    (env : Env ℳ parameterCount)
    (pair left right : ℳ.Domain) :
    (((env.push pair).push left).push right).reindex
        (RelationGraphEmbedding.value
          (parameterCount := parameterCount)) =
      (env.push left).push right := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry
    · rfl
    · refine Fin.cases ?_ (fun parameter => ?_) previous <;> rfl
  · rfl

/-- 关系图成员模式精确表达一个编码坐标对满足原二元模式。 -/
theorem satisfies_relationMember_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (schema : BinarySchema parameterCount)
    (env : Env ℳ parameterCount) (pair : ℳ.Domain) :
    satisfies (env.push pair)
        (UnarySchema.relationMember 𝒞 schema).body ↔
      ∃ left right,
        𝕀.Codes pair left right ∧
          schema.denote env left right := by
  simp only [UnarySchema.relationMember, satisfies_exists_iff,
    satisfies_conj_iff, 𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]
  constructor
  · rintro ⟨left, right, hCode, hValue⟩
    rw [satisfies_rename] at hValue
    have hCode' : 𝕀.Codes pair left right := by
      simpa using hCode
    exact ⟨left, right, hCode', by
      simpa only [reindex_relationGraphValue] using hValue⟩
  · rintro ⟨left, right, hCode, hValue⟩
    refine ⟨left, right, ?_, ?_⟩
    · simpa using hCode
    rw [satisfies_rename]
    simpa only [reindex_relationGraphValue] using hValue

/-- 限制成员模式恰好筛出第一坐标属于固定源集的编码对。 -/
theorem satisfies_restrictionMember_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (pair : ℳ.Domain) :
    satisfies (env.push pair)
        (UnarySchema.restrictionMember 𝒞).body ↔
      ∃ input output,
        𝕀.Codes pair input output ∧
          ℳ.mem input (env.bound 0) := by
  simp only [UnarySchema.restrictionMember,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_mem_iff, 𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push]
  rfl

end Formula

end Project
end Definitional

open Definitional.Project

namespace ZF

/-- 可定义二元关系在给定载体上可集合化为精确的有序对关系。 -/
theorem exists_setRelationOn_of_denote
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount)
    (env : Env ℳ parameterCount) (carrier : ℳ.Domain) :
    ∃ relation,
      ℳ.IsSetRelationOn 𝕀 relation carrier ∧
        ∀ left right,
          ℳ.PairMember 𝕀 left right relation ↔
            ℳ.mem left carrier ∧
              ℳ.mem right carrier ∧
                schema.denote env left right := by
  rcases exists_cartesianProduct hZF 𝕀 carrier carrier with
    ⟨product, hProduct⟩
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.relationMember 𝒞 schema) env product with
    ⟨relation, hRelation⟩
  have hRelationMember (pair : ℳ.Domain) :
      ℳ.mem pair relation ↔
        ∃ left, ℳ.mem left carrier ∧
          ∃ right, ℳ.mem right carrier ∧
            𝕀.Codes pair left right ∧
              schema.denote env left right := by
    rw [hRelation pair, hProduct pair,
      Definitional.Project.Formula.satisfies_relationMember_iff
        𝕀 schema env pair]
    constructor
    · rintro ⟨⟨left, hLeft, right, hRight, hCode⟩,
        selectedLeft, selectedRight, hSelectedCode, hValue⟩
      rcases 𝕀.injective hCode hSelectedCode with
        ⟨hLeftEq, hRightEq⟩
      subst selectedLeft
      subst selectedRight
      exact ⟨left, hLeft, right, hRight, hCode, hValue⟩
    · rintro ⟨left, hLeft, right, hRight, hCode, hValue⟩
      exact ⟨⟨left, hLeft, right, hRight, hCode⟩,
        left, right, hCode, hValue⟩
  have hSetRelation : ℳ.IsSetRelation 𝕀 relation := by
    intro pair hPair
    rcases (hRelationMember pair).mp hPair with
      ⟨left, _, right, _, hCode, _⟩
    exact ⟨left, right, hCode⟩
  have hRelationOn :
      ℳ.IsSetRelationOn 𝕀 relation carrier := by
    refine ⟨hSetRelation, ?_⟩
    intro left right hPair
    rcases hPair with ⟨pair, hCode, hPair⟩
    rcases (hRelationMember pair).mp hPair with
      ⟨selectedLeft, hLeft, selectedRight, hRight,
        hSelectedCode, _⟩
    rcases 𝕀.injective hCode hSelectedCode with
      ⟨hLeftEq, hRightEq⟩
    simpa [hLeftEq, hRightEq] using ⟨hLeft, hRight⟩
  refine ⟨relation, hRelationOn, ?_⟩
  intro left right
  constructor
  · rintro ⟨pair, hCode, hPair⟩
    rcases (hRelationMember pair).mp hPair with
      ⟨selectedLeft, hLeft, selectedRight, hRight,
        hSelectedCode, hValue⟩
    rcases 𝕀.injective hCode hSelectedCode with
      ⟨hLeftEq, hRightEq⟩
    simpa [hLeftEq, hRightEq] using ⟨hLeft, hRight, hValue⟩
  · rintro ⟨hLeft, hRight, hValue⟩
    rcases 𝕀.total left right with ⟨pair, hCode⟩
    exact ⟨pair, hCode, (hRelationMember pair).mpr
      ⟨left, hLeft, right, hRight, hCode, hValue⟩⟩

/-- ZF 中任意集合编码关系在任意源集上的限制都存在。 -/
theorem exists_restriction {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation source : ℳ.Domain) :
    ∃ restriction,
      ℳ.IsRestrictionOf 𝕀
        restriction relation source := by
  let env : Env ℳ 1 := {
    bound := fun _ => source
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.restrictionMember 𝒞) env relation with
    ⟨restriction, hRestriction⟩
  have hRestrictionSemantic :
      ∀ pair,
        ℳ.mem pair restriction ↔
          ℳ.mem pair relation ∧
            ∃ input output,
              𝕀.Codes pair input output ∧
                ℳ.mem input source := by
    intro pair
    rw [hRestriction pair]
    rw [Definitional.Project.Formula.satisfies_restrictionMember_iff 𝕀]
  have hRestrictionRelation :
      ℳ.IsSetRelation 𝕀 restriction := by
    intro pair hPair
    rcases (hRestrictionSemantic pair).mp hPair with
      ⟨_, input, output, hCode, _⟩
    exact ⟨input, output, hCode⟩
  refine ⟨restriction, hRestrictionRelation, ?_⟩
  intro input output
  constructor
  · rintro ⟨pair, hCode, hPair⟩
    rcases (hRestrictionSemantic pair).mp hPair with
      ⟨hPairRelation, selectedInput, selectedOutput,
        hSelectedCode, hSelectedInput⟩
    rcases 𝕀.injective hCode hSelectedCode with
      ⟨hInputEq, hOutputEq⟩
    subst selectedInput
    subst selectedOutput
    exact ⟨hSelectedInput, pair, hCode, hPairRelation⟩
  · rintro ⟨hInput, pair, hCode, hPair⟩
    exact
      ⟨pair, hCode,
        (hRestrictionSemantic pair).mpr
          ⟨hPair, input, output, hCode, hInput⟩⟩

/-- 全定义且单值的可定义二元关系可收集为模型内部函数图。 -/
theorem exists_setFunctionFromTo_of_denote
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount)
    (env : Env ℳ parameterCount)
    {source target : ℳ.Domain}
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output, schema.denote env input output)
    (hUnique : ∀ input, ℳ.mem input source → ∀ first second,
      schema.denote env input first →
      schema.denote env input second →
      first = second)
    (hTarget : ∀ input output,
      ℳ.mem input source →
      schema.denote env input output →
      ℳ.mem output target) :
    ∃ function,
      ℳ.IsSetFunctionFromTo 𝕀 function source target ∧
        ∀ input output,
          ℳ.PairMember 𝕀 input output function ↔
            ℳ.mem input source ∧
              schema.denote env input output := by
  have hGraphTotal :
      ∀ input, ℳ.mem input source →
        ∃ pair, (schema.functionGraph 𝒞).denote env input pair := by
    intro input hInput
    rcases hTotal input hInput with ⟨output, hOutput⟩
    rcases 𝕀.total input output with ⟨pair, hCode⟩
    exact ⟨pair,
      (Definitional.Project.Formula.denote_functionGraph_iff
        𝕀 schema env input pair).mpr
        ⟨output, hOutput, hCode⟩⟩
  have hGraphUnique :
      ∀ input, ℳ.mem input source → ∀ first second,
        (schema.functionGraph 𝒞).denote env input first →
        (schema.functionGraph 𝒞).denote env input second →
        first = second := by
    intro input hInput first second hFirst hSecond
    rcases
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input first).mp hFirst with
      ⟨firstOutput, hFirstValue, hFirstCode⟩
    rcases
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input second).mp hSecond with
      ⟨secondOutput, hSecondValue, hSecondCode⟩
    have hOutputEq :=
      hUnique input hInput firstOutput secondOutput hFirstValue hSecondValue
    subst secondOutput
    exact 𝕀.unique hFirstCode hSecondCode
  rcases exists_functionalImageOn hZF
      (schema.functionGraph 𝒞) env source hGraphTotal hGraphUnique with
    ⟨function, hFunctionMembers⟩
  have hPairMember (input output : ℳ.Domain) :
      ℳ.PairMember 𝕀 input output function ↔
        ℳ.mem input source ∧ schema.denote env input output := by
    constructor
    · rintro ⟨pair, hPairCode, hPairMem⟩
      rcases (hFunctionMembers pair).mp hPairMem with
        ⟨sourceInput, hSourceInput, hGraph⟩
      rcases
          (Definitional.Project.Formula.denote_functionGraph_iff
            𝕀 schema env sourceInput pair).mp hGraph with
        ⟨graphOutput, hValue, hGraphCode⟩
      rcases 𝕀.injective hPairCode hGraphCode with
        ⟨hInputEq, hOutputEq⟩
      subst sourceInput
      subst graphOutput
      exact ⟨hSourceInput, hValue⟩
    · rintro ⟨hInput, hValue⟩
      rcases 𝕀.total input output with ⟨pair, hPairCode⟩
      refine ⟨pair, hPairCode, (hFunctionMembers pair).mpr ?_⟩
      exact ⟨input, hInput,
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input pair).mpr
          ⟨output, hValue, hPairCode⟩⟩
  have hRelation : ℳ.IsSetRelation 𝕀 function := by
    intro pair hPair
    rcases (hFunctionMembers pair).mp hPair with
      ⟨input, _, hGraph⟩
    rcases
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input pair).mp hGraph with
      ⟨output, _, hCode⟩
    exact ⟨input, output, hCode⟩
  have hSetFunction : ℳ.IsSetFunction 𝕀 function := by
    refine ⟨hRelation, ?_⟩
    intro input first second hFirst hSecond
    exact hUnique input
      ((hPairMember input first).mp hFirst).1 first second
      ((hPairMember input first).mp hFirst).2
      ((hPairMember input second).mp hSecond).2
  have hDomain : ℳ.IsDomainOf 𝕀 source function := by
    intro input
    constructor
    · intro hInput
      rcases hTotal input hInput with ⟨output, hOutput⟩
      exact ⟨output, (hPairMember input output).mpr ⟨hInput, hOutput⟩⟩
    · rintro ⟨output, hOutput⟩
      exact ((hPairMember input output).mp hOutput).1
  have hIntoTarget :
      ∀ input, ℳ.mem input source →
        ∃ output, ℳ.mem output target ∧
          ℳ.PairMember 𝕀 input output function := by
    intro input hInput
    rcases hTotal input hInput with ⟨output, hOutput⟩
    exact ⟨output, hTarget input output hInput hOutput,
      (hPairMember input output).mpr ⟨hInput, hOutput⟩⟩
  exact ⟨function, ⟨⟨hSetFunction, hDomain, hIntoTarget⟩, hPairMember⟩⟩

/-- 两个模型内部函数的复合仍可收集为模型内部函数。 -/
theorem exists_compositionFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second source middle target : ℳ.Domain}
    (hFirst :
      ℳ.IsSetFunctionFromTo 𝕀 first source middle)
    (hSecond :
      ℳ.IsSetFunctionFromTo 𝕀 second middle target) :
    ∃ composition,
      ℳ.IsSetFunctionFromTo 𝕀 composition source target ∧
        ∀ input output,
          ℳ.PairMember 𝕀 input output composition ↔
            ℳ.mem input source ∧
              ∃ middleValue,
                ℳ.PairMember 𝕀 input middleValue first ∧
                  ℳ.PairMember 𝕀 middleValue output second := by
  let env : Env ℳ 2 := {
    bound := Fin.cases first <| Fin.cases second Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_setFunctionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.compositionValue 𝒞) env
      (by
        intro input hInput
        rcases hFirst.2.2 input hInput with
          ⟨middleValue, hMiddle, hFirstPair⟩
        rcases hSecond.2.2 middleValue hMiddle with
          ⟨output, _, hSecondPair⟩
        exact ⟨output,
          (Definitional.Project.Formula.denote_compositionValue_iff
            𝕀 env input output).mpr
              ⟨middleValue, hFirstPair, hSecondPair⟩⟩)
      (by
        intro input _ firstOutput secondOutput hFirstValue hSecondValue
        rw [Definitional.Project.Formula.denote_compositionValue_iff 𝕀]
          at hFirstValue hSecondValue
        rcases hFirstValue with
          ⟨firstMiddle, hInputFirst, hFirstOutput⟩
        rcases hSecondValue with
          ⟨secondMiddle, hInputSecond, hSecondOutput⟩
        have hMiddleEq :=
          hFirst.1.2 input firstMiddle secondMiddle
            hInputFirst hInputSecond
        subst secondMiddle
        exact hSecond.1.2 firstMiddle firstOutput secondOutput
          hFirstOutput hSecondOutput)
      (by
        intro input output _ hValue
        rw [Definitional.Project.Formula.denote_compositionValue_iff 𝕀] at hValue
        rcases hValue with ⟨middleValue, _, hOutput⟩
        exact hSecond.output_mem_of_pairMember hOutput) with
    ⟨composition, hComposition, hPairs⟩
  refine ⟨composition, hComposition, fun input output => ?_⟩
  rw [hPairs input output,
    Definitional.Project.Formula.denote_compositionValue_iff 𝕀]
  rfl

/-- 两个模型内部单射的复合仍是模型内部单射。 -/
theorem exists_compositionInjection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second source middle target : ℳ.Domain}
    (hFirst :
      ℳ.IsSetInjectionFromTo 𝕀 first source middle)
    (hSecond :
      ℳ.IsSetInjectionFromTo 𝕀 second middle target) :
    ∃ composition,
      ℳ.IsSetInjectionFromTo 𝕀 composition source target := by
  rcases exists_compositionFunction hZF 𝕀 hFirst.1 hSecond.1 with
    ⟨composition, hComposition, hPairs⟩
  refine ⟨composition, hComposition, ?_⟩
  intro firstInput secondInput output hFirstPair hSecondPair
  rcases (hPairs firstInput output).mp hFirstPair with
    ⟨_, firstMiddle, hFirstInput, hFirstOutput⟩
  rcases (hPairs secondInput output).mp hSecondPair with
    ⟨_, secondMiddle, hSecondInput, hSecondOutput⟩
  have hMiddleEq :=
    hSecond.2 firstMiddle secondMiddle output
      hFirstOutput hSecondOutput
  subst secondMiddle
  exact hFirst.2 firstInput secondInput firstMiddle
    hFirstInput hSecondInput

/-- 可定义值关系若还满足输入单射性，就生成模型内部单射。 -/
theorem exists_setInjectionFromTo_of_denote
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount)
    (env : Env ℳ parameterCount)
    {source target : ℳ.Domain}
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output, schema.denote env input output)
    (hUnique : ∀ input, ℳ.mem input source → ∀ first second,
      schema.denote env input first →
      schema.denote env input second →
      first = second)
    (hTarget : ∀ input output,
      ℳ.mem input source →
      schema.denote env input output →
      ℳ.mem output target)
    (hInjective : ∀ first second output,
      ℳ.mem first source →
      ℳ.mem second source →
      schema.denote env first output →
      schema.denote env second output →
      first = second) :
    ∃ function,
      ℳ.IsSetInjectionFromTo 𝕀 function source target := by
  rcases exists_setFunctionFromTo_of_denote
      hZF 𝕀 schema env hTotal hUnique hTarget with
    ⟨function, hFunction, hPairMember⟩
  refine ⟨function, hFunction, ?_⟩
  intro first second output hFirst hSecond
  exact hInjective first second output
    ((hPairMember first output).mp hFirst).1
    ((hPairMember second output).mp hSecond).1
    ((hPairMember first output).mp hFirst).2
    ((hPairMember second output).mp hSecond).2

/-- 可定义值关系若在目标上满射，就生成模型内部双射。 -/
theorem exists_setBijectionFromTo_of_denote
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount)
    (env : Env ℳ parameterCount)
    {source target : ℳ.Domain}
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output, schema.denote env input output)
    (hUnique : ∀ input, ℳ.mem input source → ∀ first second,
      schema.denote env input first →
      schema.denote env input second →
      first = second)
    (hTarget : ∀ input output,
      ℳ.mem input source →
      schema.denote env input output →
      ℳ.mem output target)
    (hInjective : ∀ first second output,
      ℳ.mem first source →
      ℳ.mem second source →
      schema.denote env first output →
      schema.denote env second output →
      first = second)
    (hSurjective : ∀ output, ℳ.mem output target →
      ∃ input, ℳ.mem input source ∧
        schema.denote env input output) :
    ∃ function,
      ℳ.IsSetBijectionFromTo 𝕀 function source target := by
  rcases exists_setFunctionFromTo_of_denote
      hZF 𝕀 schema env hTotal hUnique hTarget with
    ⟨function, hFunction, hPairMember⟩
  refine ⟨function, ⟨hFunction, ?_⟩, ?_⟩
  · intro first second output hFirst hSecond
    exact hInjective first second output
      ((hPairMember first output).mp hFirst).1
      ((hPairMember second output).mp hSecond).1
      ((hPairMember first output).mp hFirst).2
      ((hPairMember second output).mp hSecond).2
  · intro output hOutput
    rcases hSurjective output hOutput with ⟨input, hInput, hValue⟩
    exact ⟨input, hInput,
      (hPairMember input output).mpr ⟨hInput, hValue⟩⟩

/-- 任意集合上的恒等关系可收集为模型内部双射。 -/
theorem exists_identityBijection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ) (set : ℳ.Domain) :
    ∃ function,
      ℳ.IsSetBijectionFromTo 𝕀 function set set := by
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 Definitional.Project.BinarySchema.identityValue env
  · intro input _
    exact ⟨input,
      (Definitional.Project.Formula.denote_identityValue_iff
        hZF.1 env input input).mpr rfl⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_identityValue_iff hZF.1]
      at hFirst hSecond
    exact hFirst.symm.trans hSecond
  · intro input output hInput hValue
    rw [Definitional.Project.Formula.denote_identityValue_iff hZF.1] at hValue
    simpa [hValue] using hInput
  · intro first second output _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_identityValue_iff hZF.1]
      at hFirst hSecond
    exact hFirst.trans hSecond.symm
  · intro output hOutput
    exact ⟨output, hOutput,
      (Definitional.Project.Formula.denote_identityValue_iff
        hZF.1 env output output).mpr rfl⟩

/-- 子集包含映射可由恒等函数图实现为模型内部单射。 -/
theorem exists_inclusionInjection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target : ℳ.Domain}
    (hSubset : ∀ value, ℳ.mem value source → ℳ.mem value target) :
    ∃ function,
      ℳ.IsSetInjectionFromTo 𝕀 function source target := by
  rcases exists_identityBijection hZF 𝕀 source with
    ⟨function, hIdentity⟩
  refine ⟨function, ⟨⟨hIdentity.1.1.1, hIdentity.1.1.2.1, ?_⟩,
    hIdentity.1.2⟩⟩
  intro input hInput
  rcases hIdentity.1.1.2.2 input hInput with
    ⟨output, hOutput, hPair⟩
  exact ⟨output, hSubset output hOutput, hPair⟩

/-- 任意固定目标值都给出从源集到目标集的常值函数。 -/
theorem exists_constantFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target value : ℳ.Domain}
    (hValue : ℳ.mem value target) :
    ∃ function,
      ℳ.IsSetFunctionFromTo 𝕀 function source target ∧
        ∀ input output,
          ℳ.PairMember 𝕀 input output function ↔
            ℳ.mem input source ∧ output = value := by
  let env : Env ℳ 1 := {
    bound := fun _ => value
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_setFunctionFromTo_of_denote
      hZF 𝕀 Definitional.Project.BinarySchema.constantValue env
      (by
        intro input _
        exact ⟨value,
          (Definitional.Project.Formula.denote_constantValue_iff
            hZF.1 env input value).mpr rfl⟩)
      (by
        intro input _ first second hFirst hSecond
        rw [Definitional.Project.Formula.denote_constantValue_iff hZF.1]
          at hFirst hSecond
        exact hFirst.trans hSecond.symm)
      (by
        intro input output _ hOutput
        rw [Definitional.Project.Formula.denote_constantValue_iff hZF.1] at hOutput
        simpa [hOutput] using hValue) with
    ⟨function, hFunction, hPairs⟩
  refine ⟨function, hFunction, fun input output => ?_⟩
  rw [hPairs input output,
    Definitional.Project.Formula.denote_constantValue_iff hZF.1]

/-- 任意两个单元素集之间都有模型内部双射。 -/
theorem exists_bijectionBetweenSingletons
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target sourceValue targetValue : ℳ.Domain}
    (hSource : ℳ.IsSingletonOf source sourceValue)
    (hTarget : ℳ.IsSingletonOf target targetValue) :
    ∃ function,
      ℳ.IsSetBijectionFromTo 𝕀 function source target := by
  have hTargetValue : ℳ.mem targetValue target :=
    (hTarget targetValue).mpr rfl
  rcases exists_constantFunction hZF 𝕀 hTargetValue with
    ⟨function, hFunction, hPairs⟩
  refine ⟨function, ⟨hFunction, ?_⟩, ?_⟩
  · intro first second output hFirst hSecond
    have hFirstSource :=
      hFunction.input_mem_of_pairMember hFirst
    have hSecondSource :=
      hFunction.input_mem_of_pairMember hSecond
    exact ((hSource first).mp hFirstSource).trans <|
      ((hSource second).mp hSecondSource).symm
  · intro output hOutput
    have hOutputEq := (hTarget output).mp hOutput
    have hSourceValue : ℳ.mem sourceValue source :=
      (hSource sourceValue).mpr rfl
    refine ⟨sourceValue, hSourceValue, (hPairs sourceValue output).mpr ?_⟩
    exact ⟨hSourceValue, hOutputEq⟩

/-- 模型内部双射的逆关系可收集，并保留精确的反向图刻画。 -/
theorem exists_inverseBijectionWithPairs
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function source target : ℳ.Domain}
    (hFunction :
      ℳ.IsSetBijectionFromTo 𝕀 function source target) :
    ∃ inverse,
      ℳ.IsSetBijectionFromTo 𝕀 inverse target source ∧
        ∀ output input,
          ℳ.PairMember 𝕀 output input inverse ↔
            ℳ.PairMember 𝕀 input output function := by
  let env : Env ℳ 1 := {
    bound := fun _ => function
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_setFunctionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.inverseValue 𝒞) env
      (by
        intro output hOutput
        rcases hFunction.2 output hOutput with
          ⟨input, _, hPair⟩
        exact ⟨input,
          (Definitional.Project.Formula.denote_inverseValue_iff
            𝕀 env output input).mpr hPair⟩)
      (by
        intro output _ first second hFirst hSecond
        rw [Definitional.Project.Formula.denote_inverseValue_iff 𝕀]
          at hFirst hSecond
        exact hFunction.1.2 first second output hFirst hSecond)
      (by
        intro output input _ hValue
        rw [Definitional.Project.Formula.denote_inverseValue_iff 𝕀] at hValue
        exact (hFunction.1.1.2.1 input).mpr ⟨output, hValue⟩) with
    ⟨inverse, hInverse, hPairs⟩
  have hInjective : ℳ.IsSetInjective 𝕀 inverse := by
    intro first second input hFirst hSecond
    have hFirstData := (hPairs first input).mp hFirst
    have hSecondData := (hPairs second input).mp hSecond
    rw [Definitional.Project.Formula.denote_inverseValue_iff 𝕀]
      at hFirstData hSecondData
    exact hFunction.1.1.1.2 input first second
      hFirstData.2 hSecondData.2
  have hSurjective :
      ℳ.IsSetSurjectiveOnto 𝕀 inverse target source := by
    intro input hInput
    rcases hFunction.1.1.2.2 input hInput with
      ⟨output, hOutput, hPair⟩
    exact ⟨output, hOutput, (hPairs output input).mpr
      ⟨hOutput,
        (Definitional.Project.Formula.denote_inverseValue_iff
          𝕀 env output input).mpr hPair⟩⟩
  refine ⟨inverse, ⟨⟨hInverse, hInjective⟩, hSurjective⟩, ?_⟩
  intro output input
  rw [hPairs output input,
    Definitional.Project.Formula.denote_inverseValue_iff 𝕀]
  constructor
  · exact fun h => h.2
  · intro hPair
    exact ⟨hFunction.1.1.output_mem_of_pairMember hPair, hPair⟩

/-- 模型内部双射的逆关系仍可收集为模型内部双射。 -/
theorem exists_inverseBijection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function source target : ℳ.Domain}
    (hFunction :
      ℳ.IsSetBijectionFromTo 𝕀 function source target) :
    ∃ inverse,
      ℳ.IsSetBijectionFromTo 𝕀 inverse target source := by
  rcases exists_inverseBijectionWithPairs hZF 𝕀 hFunction with
    ⟨inverse, hInverse, _⟩
  exact ⟨inverse, hInverse⟩

/-- 两个模型内部双射的复合仍可收集为模型内部双射。 -/
theorem exists_compositionBijection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {first second source middle target : ℳ.Domain}
    (hFirst :
      ℳ.IsSetBijectionFromTo 𝕀 first source middle)
    (hSecond :
      ℳ.IsSetBijectionFromTo 𝕀 second middle target) :
    ∃ composition,
      ℳ.IsSetBijectionFromTo 𝕀 composition source target := by
  let env : Env ℳ 2 := {
    bound := Fin.cases first <| Fin.cases second Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.compositionValue 𝒞) env
  · intro input hInput
    rcases hFirst.1.1.2.2 input hInput with
      ⟨middleValue, hMiddle, hFirstPair⟩
    rcases hSecond.1.1.2.2 middleValue hMiddle with
      ⟨output, _, hSecondPair⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_compositionValue_iff
        𝕀 env input output).mpr
          ⟨middleValue, hFirstPair, hSecondPair⟩⟩
  · intro input _ firstOutput secondOutput hFirstValue hSecondValue
    rw [Definitional.Project.Formula.denote_compositionValue_iff 𝕀]
      at hFirstValue hSecondValue
    rcases hFirstValue with
      ⟨firstMiddle, hInputFirst, hFirstOutput⟩
    rcases hSecondValue with
      ⟨secondMiddle, hInputSecond, hSecondOutput⟩
    have hMiddleEq :=
      hFirst.1.1.1.2 input firstMiddle secondMiddle
        hInputFirst hInputSecond
    subst secondMiddle
    exact hSecond.1.1.1.2 firstMiddle
      firstOutput secondOutput hFirstOutput hSecondOutput
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_compositionValue_iff 𝕀] at hValue
    rcases hValue with ⟨middleValue, _, hOutput⟩
    rcases hSecond.1.1.2.2 middleValue
        ((hSecond.1.1.2.1 middleValue).mpr ⟨output, hOutput⟩) with
      ⟨selected, hSelectedTarget, hSelectedPair⟩
    have hEq := hSecond.1.1.1.2 middleValue
      output selected hOutput hSelectedPair
    simpa [hEq] using hSelectedTarget
  · intro firstInput secondInput output _ _
      hFirstValue hSecondValue
    rw [Definitional.Project.Formula.denote_compositionValue_iff 𝕀]
      at hFirstValue hSecondValue
    rcases hFirstValue with
      ⟨firstMiddle, hFirstPair, hFirstOutput⟩
    rcases hSecondValue with
      ⟨secondMiddle, hSecondPair, hSecondOutput⟩
    have hMiddleEq :=
      hSecond.1.2 firstMiddle secondMiddle output
        hFirstOutput hSecondOutput
    subst secondMiddle
    exact hFirst.1.2 firstInput secondInput firstMiddle
      hFirstPair hSecondPair
  · intro output hOutput
    rcases hSecond.2 output hOutput with
      ⟨middleValue, hMiddle, hSecondPair⟩
    rcases hFirst.2 middleValue hMiddle with
      ⟨input, hInput, hFirstPair⟩
    exact ⟨input, hInput,
      (Definitional.Project.Formula.denote_compositionValue_iff
        𝕀 env input output).mpr
          ⟨middleValue, hFirstPair, hSecondPair⟩⟩

end ZF

namespace Structure.IsUnionOfTwo

/-- 定义域不交的两个函数图之并仍是到同一目标集的函数。 -/
theorem functionFromTo_of_disjoint
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {function leftFunction rightFunction
      source left right target : ℳ.Domain}
    (hFunctionUnion :
      ℳ.IsUnionOfTwo function leftFunction rightFunction)
    (hSourceUnion :
      ℳ.IsUnionOfTwo source left right)
    (hDisjoint : ℳ.IsDisjoint left right)
    (hLeft :
      ℳ.IsSetFunctionFromTo 𝕀 leftFunction left target)
    (hRight :
      ℳ.IsSetFunctionFromTo 𝕀 rightFunction right target) :
    ℳ.IsSetFunctionFromTo 𝕀 function source target := by
  have hPairs (input output : ℳ.Domain) :
      ℳ.PairMember 𝕀 input output function ↔
        ℳ.PairMember 𝕀 input output leftFunction ∨
          ℳ.PairMember 𝕀 input output rightFunction := by
    constructor
    · rintro ⟨pair, hCode, hPair⟩
      rcases (hFunctionUnion pair).mp hPair with
        hPairLeft | hPairRight
      · exact Or.inl ⟨pair, hCode, hPairLeft⟩
      · exact Or.inr ⟨pair, hCode, hPairRight⟩
    · intro hPair
      rcases hPair with hPairLeft | hPairRight
      · rcases hPairLeft with ⟨pair, hCode, hPair⟩
        exact ⟨pair, hCode,
          (hFunctionUnion pair).mpr <| Or.inl hPair⟩
      · rcases hPairRight with ⟨pair, hCode, hPair⟩
        exact ⟨pair, hCode,
          (hFunctionUnion pair).mpr <| Or.inr hPair⟩
  have hRelation : ℳ.IsSetRelation 𝕀 function := by
    intro pair hPair
    rcases (hFunctionUnion pair).mp hPair with
      hPairLeft | hPairRight
    · exact hLeft.1.1 pair hPairLeft
    · exact hRight.1.1 pair hPairRight
  have hSingleValued :
      ∀ input first second,
        ℳ.PairMember 𝕀 input first function →
        ℳ.PairMember 𝕀 input second function →
        first = second := by
    intro input first second hFirst hSecond
    rw [hPairs input first] at hFirst
    rw [hPairs input second] at hSecond
    rcases hFirst with hFirstLeft | hFirstRight
    · rcases hSecond with hSecondLeft | hSecondRight
      · exact hLeft.1.2 input first second hFirstLeft hSecondLeft
      · exact False.elim <| hDisjoint input
          ⟨hLeft.input_mem_of_pairMember hFirstLeft,
            hRight.input_mem_of_pairMember hSecondRight⟩
    · rcases hSecond with hSecondLeft | hSecondRight
      · exact False.elim <| hDisjoint input
          ⟨hLeft.input_mem_of_pairMember hSecondLeft,
            hRight.input_mem_of_pairMember hFirstRight⟩
      · exact hRight.1.2 input first second hFirstRight hSecondRight
  have hDomain : ℳ.IsDomainOf 𝕀 source function := by
    intro input
    constructor
    · intro hInput
      rcases (hSourceUnion input).mp hInput with
        hInputLeft | hInputRight
      · rcases hLeft.2.2 input hInputLeft with
          ⟨output, _, hPair⟩
        exact ⟨output, (hPairs input output).mpr <| Or.inl hPair⟩
      · rcases hRight.2.2 input hInputRight with
          ⟨output, _, hPair⟩
        exact ⟨output, (hPairs input output).mpr <| Or.inr hPair⟩
    · rintro ⟨output, hPair⟩
      rcases (hPairs input output).mp hPair with
        hPairLeft | hPairRight
      · exact (hSourceUnion input).mpr <| Or.inl <|
          hLeft.input_mem_of_pairMember hPairLeft
      · exact (hSourceUnion input).mpr <| Or.inr <|
          hRight.input_mem_of_pairMember hPairRight
  refine ⟨⟨hRelation, hSingleValued⟩, hDomain, ?_⟩
  intro input hInput
  rcases (hSourceUnion input).mp hInput with
    hInputLeft | hInputRight
  · rcases hLeft.2.2 input hInputLeft with
      ⟨output, hOutput, hPair⟩
    exact ⟨output, hOutput,
      (hPairs input output).mpr <| Or.inl hPair⟩
  · rcases hRight.2.2 input hInputRight with
      ⟨output, hOutput, hPair⟩
    exact ⟨output, hOutput,
      (hPairs input output).mpr <| Or.inr hPair⟩

end Structure.IsUnionOfTwo

end SetTheory
end YesMetaZFC
