import YesMetaZFC.SetTheory.Card.Arithmetic.Basic
import YesMetaZFC.SetTheory.Card.CantorBernstein
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.FunctionSpaceConstruction
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.TaggedUnionConstruction

/-!
# 基数算术使用的等势构造

本层收集运算代表元之间的通用双射。第一组接口处理两个不交并上的分片映射；证明生成
的仍是模型内部函数图，并显式使用源、目标两侧的不交性排除交叉分支。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Definitional
namespace Project

namespace BinarySchema

/-- 在两个不交分量上分别使用给定函数图的值关系。 -/
def disjointUnionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 4 where
  body := .disj
    (.conj
      (.mem (.bound 1) (.bound 4))
      (Formula.orderedPairMem 𝒞
        (.bound 1) (.bound 0) (.bound 2)))
    (.conj
      (.mem (.bound 1) (.bound 5))
      (Formula.orderedPairMem 𝒞
        (.bound 1) (.bound 0) (.bound 3)))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 分别映射两个坐标的笛卡尔积值关系。 -/
def cartesianProductValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .existsE <| .existsE <| .existsE <|
    .conj
      (𝒞.code (.bound 5) (.bound 3) (.bound 2)) <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 3) (.bound 1) (.bound 6)) <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 2) (.bound 0) (.bound 7))
      (𝒞.code (.bound 4) (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/--
把序数笛卡尔积中的 `(left, right)` 映到序数乘法的第 `right` 块中偏移 `left`
的位置。
-/
def ordinalMultiplicationValue
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := .existsE <| .existsE <| .existsE <|
    .conj (𝒞.code (.bound 4) (.bound 2) (.bound 1)) <|
    .conj
      (Formula.isOrdinalMultiplication 𝒞
        (.bound 0) (.bound 5) (.bound 1))
      (Formula.isOrdinalAddition 𝒞
        (.bound 3) (.bound 0) (.bound 2))
  freeClosed := by
    simp [Formula.isOrdinalMultiplication,
      Formula.isOrdinalAddition, Formula.related,
      Formula.FreeClosed]
    constructor
    · apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]
    · apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

/--
把后继中新加入的点送到零，把自然数整体后移一位，其余元素保持不变。
-/
def successorAbsorptionValue : BinarySchema 3 where
  body := .disj
    (.conj
      (Formula.extensionalEq (.bound 1) (.bound 2))
      (Formula.extensionalEq (.bound 0) (.bound 4))) <|
    .disj
      (.conj
        (.mem (.bound 1) (.bound 3))
        (Formula.isSuccessor (.bound 0) (.bound 1))) <|
      .conj (.neg <| Formula.extensionalEq (.bound 1) (.bound 2)) <|
        .conj (.neg <| .mem (.bound 1) (.bound 3))
          (Formula.extensionalEq (.bound 0) (.bound 1))
  freeClosed := by
    simp [Formula.isSuccessor, Formula.extensionalEq,
      Formula.FreeClosed]

/-- 交换坐标后分别应用给定双射的笛卡尔积值关系。 -/
def swappedCartesianProductValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .existsE <| .existsE <| .existsE <|
    .conj
      (𝒞.code (.bound 5) (.bound 3) (.bound 2)) <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 3) (.bound 0) (.bound 6)) <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 2) (.bound 1) (.bound 7))
      (𝒞.code (.bound 4) (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 把 `((a, b), c)` 重括号为 `(a, (b, c))`。 -/
def associateCartesianProductValue
    (𝒞 : OrderedPairConvention) : BinarySchema 0 where
  body := .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
    .conj (𝒞.code (.bound 1) (.bound 4) (.bound 3)) <|
    .conj (𝒞.code (.bound 6) (.bound 1) (.bound 2)) <|
    .conj (𝒞.code (.bound 0) (.bound 3) (.bound 2))
      (𝒞.code (.bound 5) (.bound 4) (.bound 0))
  freeClosed := by
    simp [Formula.FreeClosed]

/-- 把左结合的二元标签编码重括号为右结合编码。 -/
def associateTaggedUnionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .disj
    (.existsE <| .existsE <|
      .conj (𝒞.code (.bound 3) (.bound 4) (.bound 1)) <|
      .conj (𝒞.code (.bound 1) (.bound 4) (.bound 0))
        (𝒞.code (.bound 2) (.bound 4) (.bound 0))) <|
    .disj
      (.existsE <| .existsE <| .existsE <|
        .conj (𝒞.code (.bound 4) (.bound 5) (.bound 2)) <|
        .conj (𝒞.code (.bound 2) (.bound 6) (.bound 1)) <|
        .conj (𝒞.code (.bound 0) (.bound 5) (.bound 1))
          (𝒞.code (.bound 3) (.bound 6) (.bound 0)))
      (.existsE <| .existsE <|
        .conj (𝒞.code (.bound 3) (.bound 5) (.bound 1)) <|
        .conj (𝒞.code (.bound 0) (.bound 5) (.bound 1))
          (𝒞.code (.bound 2) (.bound 5) (.bound 0)))
  freeClosed := by
    simp [Formula.FreeClosed]

end BinarySchema

namespace Formula

/-- 不交并分片值关系的纸面解释。 -/
theorem denote_disjointUnionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 4) (input output : ℳ.Domain) :
    (BinarySchema.disjointUnionValue 𝒞).denote env input output ↔
      (ℳ.mem input (env.bound 2) ∧
        ℳ.PairMember 𝕀 input output (env.bound 0)) ∨
      (ℳ.mem input (env.bound 3) ∧
        ℳ.PairMember 𝕀 input output (env.bound 1)) := by
  simp only [BinarySchema.disjointUnionValue, BinarySchema.denote,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl

/-- 笛卡尔积逐坐标值关系的纸面解释。 -/
theorem denote_cartesianProductValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.cartesianProductValue 𝒞).denote env input output ↔
      ∃ sourceLeft sourceRight targetLeft targetRight,
        𝕀.Codes input sourceLeft sourceRight ∧
          ℳ.PairMember 𝕀 sourceLeft targetLeft (env.bound 0) ∧
          ℳ.PairMember 𝕀 sourceRight targetRight (env.bound 1) ∧
          𝕀.Codes output targetLeft targetRight := by
  simp only [BinarySchema.cartesianProductValue, BinarySchema.denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push, Term.eval_bound_seven_push]
  rfl

/-- 序数乘法坐标值关系的纸面解释。 -/
theorem denote_ordinalMultiplicationValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (input output : ℳ.Domain) :
    (BinarySchema.ordinalMultiplicationValue 𝒞).denote
        env input output ↔
      ∃ left right block,
        𝕀.Codes input left right ∧
          ℳ.IsOrdinalMultiplication 𝕀
            block (env.bound 0) right ∧
          ℳ.IsOrdinalAddition 𝕀 output block left := by
  simp only [BinarySchema.ordinalMultiplicationValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, 𝕀.satisfies_code_iff,
    Formula.satisfies_isOrdinalMultiplication_iff 𝕀 hExt,
    Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl

/-- 后继吸收值关系的纸面解释。 -/
theorem denote_successorAbsorptionValue_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    (env : Env ℳ 3) (input output : ℳ.Domain) :
    BinarySchema.successorAbsorptionValue.denote env input output ↔
      (input = env.bound 0 ∧ output = env.bound 2) ∨
      (ℳ.mem input (env.bound 1) ∧
        ℳ.SuccessorOf output input) ∨
      (input ≠ env.bound 0 ∧
        ¬ ℳ.mem input (env.bound 1) ∧ output = input) := by
  simp only [BinarySchema.successorAbsorptionValue,
    BinarySchema.denote, Formula.satisfies_disj_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_extensionalEq_iff_eq hExt]
  change
    ((input = env.bound 0 ∧ output = env.bound 2) ∨
      (ℳ.mem input (env.bound 1) ∧
        ℳ.SuccessorOf output input) ∨
      (input ≠ env.bound 0 ∧
        ¬ ℳ.mem input (env.bound 1) ∧ output = input)) ↔ _
  rfl

/-- 笛卡尔积交换坐标值关系的纸面解释。 -/
theorem denote_swappedCartesianProductValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.swappedCartesianProductValue 𝒞).denote env input output ↔
      ∃ sourceLeft sourceRight targetLeft targetRight,
        𝕀.Codes input sourceLeft sourceRight ∧
          ℳ.PairMember 𝕀 sourceLeft targetRight (env.bound 0) ∧
          ℳ.PairMember 𝕀 sourceRight targetLeft (env.bound 1) ∧
          𝕀.Codes output targetLeft targetRight := by
  simp only [BinarySchema.swappedCartesianProductValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push, Term.eval_bound_seven_push]
  rfl

/-- 笛卡尔积重括号值关系的纸面解释。 -/
theorem denote_associateCartesianProductValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 0) (input output : ℳ.Domain) :
    (BinarySchema.associateCartesianProductValue 𝒞).denote
        env input output ↔
      ∃ left middle right leftPair rightPair,
        𝕀.Codes leftPair left middle ∧
          𝕀.Codes input leftPair right ∧
          𝕀.Codes rightPair middle right ∧
          𝕀.Codes output left rightPair := by
  simp only [BinarySchema.associateCartesianProductValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push]

/-- 带标签不交并重括号值关系的纸面解释。 -/
theorem denote_associateTaggedUnionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.associateTaggedUnionValue 𝒞).denote
        env input output ↔
      (∃ inner value,
        𝕀.Codes input (env.bound 0) inner ∧
          𝕀.Codes inner (env.bound 0) value ∧
          𝕀.Codes output (env.bound 0) value) ∨
      (∃ inner value innerOutput,
        𝕀.Codes input (env.bound 0) inner ∧
          𝕀.Codes inner (env.bound 1) value ∧
          𝕀.Codes innerOutput (env.bound 0) value ∧
          𝕀.Codes output (env.bound 1) innerOutput) ∨
      (∃ value innerOutput,
        𝕀.Codes input (env.bound 1) value ∧
          𝕀.Codes innerOutput (env.bound 1) value ∧
          𝕀.Codes output (env.bound 1) innerOutput) := by
  simp only [BinarySchema.associateTaggedUnionValue,
    BinarySchema.denote, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push]
  rfl

end Formula

end Project
end Definitional

namespace ZF

/--
两个分量上的双射可逐段拼成两个不交并之间的双射。
-/
theorem equinumerous_unionOfTwo
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target sourceLeft sourceRight targetLeft targetRight
      leftFunction rightFunction : ℳ.Domain}
    (hSourceUnion :
      ℳ.IsUnionOfTwo source sourceLeft sourceRight)
    (hTargetUnion :
      ℳ.IsUnionOfTwo target targetLeft targetRight)
    (hSourceDisjoint :
      ℳ.IsDisjoint sourceLeft sourceRight)
    (hTargetDisjoint :
      ℳ.IsDisjoint targetLeft targetRight)
    (hLeft :
      ℳ.IsSetBijectionFromTo 𝕀
        leftFunction sourceLeft targetLeft)
    (hRight :
      ℳ.IsSetBijectionFromTo 𝕀
        rightFunction sourceRight targetRight) :
    ℳ.Equinumerous 𝕀 source target := by
  let env : Env ℳ 4 := {
    bound := Fin.cases leftFunction <|
      Fin.cases rightFunction <|
        Fin.cases sourceLeft <|
          Fin.cases sourceRight Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.disjointUnionValue 𝒞) env
  · intro input hInput
    rcases (hSourceUnion input).mp hInput with hInputLeft | hInputRight
    · rcases hLeft.1.1.2.2 input hInputLeft with
        ⟨output, _, hPair⟩
      exact ⟨output,
        (Definitional.Project.Formula.denote_disjointUnionValue_iff
          𝕀 env input output).mpr <|
          Or.inl ⟨hInputLeft, hPair⟩⟩
    · rcases hRight.1.1.2.2 input hInputRight with
        ⟨output, _, hPair⟩
      exact ⟨output,
        (Definitional.Project.Formula.denote_disjointUnionValue_iff
          𝕀 env input output).mpr <|
          Or.inr ⟨hInputRight, hPair⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_disjointUnionValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with hFirstLeft | hFirstRight
    · rcases hSecond with hSecondLeft | hSecondRight
      · exact hLeft.1.1.1.2 input first second
          hFirstLeft.2 hSecondLeft.2
      · exact False.elim <|
          hSourceDisjoint input ⟨hFirstLeft.1, hSecondRight.1⟩
    · rcases hSecond with hSecondLeft | hSecondRight
      · exact False.elim <|
          hSourceDisjoint input ⟨hSecondLeft.1, hFirstRight.1⟩
      · exact hRight.1.1.1.2 input first second
          hFirstRight.2 hSecondRight.2
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_disjointUnionValue_iff 𝕀] at hValue
    apply (hTargetUnion output).mpr
    rcases hValue with hLeftValue | hRightValue
    · exact Or.inl <|
        hLeft.1.1.output_mem_of_pairMember hLeftValue.2
    · exact Or.inr <|
        hRight.1.1.output_mem_of_pairMember hRightValue.2
  · intro first second output _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_disjointUnionValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with hFirstLeft | hFirstRight
    · rcases hSecond with hSecondLeft | hSecondRight
      · exact hLeft.1.2 first second output
          hFirstLeft.2 hSecondLeft.2
      · exact False.elim <| hTargetDisjoint output
          ⟨hLeft.1.1.output_mem_of_pairMember hFirstLeft.2,
            hRight.1.1.output_mem_of_pairMember hSecondRight.2⟩
    · rcases hSecond with hSecondLeft | hSecondRight
      · exact False.elim <| hTargetDisjoint output
          ⟨hLeft.1.1.output_mem_of_pairMember hSecondLeft.2,
            hRight.1.1.output_mem_of_pairMember hFirstRight.2⟩
      · exact hRight.1.2 first second output
          hFirstRight.2 hSecondRight.2
  · intro output hOutput
    rcases (hTargetUnion output).mp hOutput with
      hOutputLeft | hOutputRight
    · rcases hLeft.2 output hOutputLeft with
        ⟨input, hInput, hPair⟩
      exact ⟨input, (hSourceUnion input).mpr <| Or.inl hInput,
        (Definitional.Project.Formula.denote_disjointUnionValue_iff
          𝕀 env input output).mpr <|
          Or.inl ⟨hInput, hPair⟩⟩
    · rcases hRight.2 output hOutputRight with
        ⟨input, hInput, hPair⟩
      exact ⟨input, (hSourceUnion input).mpr <| Or.inr hInput,
        (Definitional.Project.Formula.denote_disjointUnionValue_iff
          𝕀 env input output).mpr <|
          Or.inr ⟨hInput, hPair⟩⟩

/-- 固定标签的有序对行与原集合等势。 -/
theorem equinumerous_cartesianRow
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {tag set row : ℳ.Domain}
    (hRow : ∀ pair, ℳ.mem pair row ↔
      ∃ value, ℳ.mem value set ∧
        𝕀.Codes pair tag value) :
    ℳ.Equinumerous 𝕀 set row := by
  let env : Env ℳ 1 := {
    bound := fun _ => tag
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.orderedPairWithLeft 𝒞) env
  · intro input _
    rcases 𝕀.total tag input with ⟨pair, hCode⟩
    exact ⟨pair,
      (Definitional.Project.Formula.denote_orderedPairWithLeft_iff
        𝕀 env input pair).mpr hCode⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_orderedPairWithLeft_iff 𝕀]
      at hFirst hSecond
    exact 𝕀.unique hFirst hSecond
  · intro input pair hInput hValue
    rw [Definitional.Project.Formula.denote_orderedPairWithLeft_iff 𝕀] at hValue
    exact (hRow pair).mpr ⟨input, hInput, hValue⟩
  · intro first second pair _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_orderedPairWithLeft_iff 𝕀]
      at hFirst hSecond
    exact (𝕀.injective hFirst hSecond).2
  · intro pair hPair
    rcases (hRow pair).mp hPair with ⟨value, hValue, hCode⟩
    exact ⟨value, hValue,
      (Definitional.Project.Formula.denote_orderedPairWithLeft_iff
        𝕀 env value pair).mpr hCode⟩

/--
任意不交并可沿分量等势正规化为带标签不交并。
-/
theorem equinumerous_unionToTaggedUnion
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source sourceLeft sourceRight target
      leftTag rightTag targetLeft targetRight : ℳ.Domain}
    (hSourceUnion :
      ℳ.IsUnionOfTwo source sourceLeft sourceRight)
    (hSourceDisjoint :
      ℳ.IsDisjoint sourceLeft sourceRight)
    (hTarget :
      ℳ.IsTaggedUnion 𝕀
        target leftTag rightTag targetLeft targetRight)
    (hLeft :
      ℳ.Equinumerous 𝕀 sourceLeft targetLeft)
    (hRight :
      ℳ.Equinumerous 𝕀 sourceRight targetRight) :
    ℳ.Equinumerous 𝕀 source target := by
  rcases hTarget with
    ⟨targetLeftCopy, targetRightCopy,
      hTargetLeftCopy, hTargetRightCopy,
      hTargetDisjoint, hTargetUnion⟩
  have hLeftCopy :=
    hLeft.trans hZF 𝕀 <|
      equinumerous_cartesianRow hZF 𝕀 hTargetLeftCopy
  have hRightCopy :=
    hRight.trans hZF 𝕀 <|
      equinumerous_cartesianRow hZF 𝕀 hTargetRightCopy
  rcases hLeftCopy with ⟨leftFunction, hLeftFunction⟩
  rcases hRightCopy with ⟨rightFunction, hRightFunction⟩
  exact equinumerous_unionOfTwo hZF 𝕀
    hSourceUnion hTargetUnion hSourceDisjoint hTargetDisjoint
    hLeftFunction hRightFunction

/-- 两个坐标上的单射逐点诱导笛卡尔积之间的单射。 -/
theorem exists_cartesianProductInjection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target sourceLeft sourceRight targetLeft targetRight
      leftFunction rightFunction : ℳ.Domain}
    (hSourceProduct :
      ℳ.IsCartesianProduct 𝕀 source sourceLeft sourceRight)
    (hTargetProduct :
      ℳ.IsCartesianProduct 𝕀 target targetLeft targetRight)
    (hLeft :
      ℳ.IsSetInjectionFromTo 𝕀
        leftFunction sourceLeft targetLeft)
    (hRight :
      ℳ.IsSetInjectionFromTo 𝕀
        rightFunction sourceRight targetRight) :
    ∃ function,
      ℳ.IsSetInjectionFromTo 𝕀 function source target := by
  let env : Env ℳ 2 := {
    bound := Fin.cases leftFunction <|
      Fin.cases rightFunction Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setInjectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.cartesianProductValue 𝒞) env
  · intro input hInput
    rcases (hSourceProduct input).mp hInput with
      ⟨sourceLeftValue, hSourceLeft,
        sourceRightValue, hSourceRight, hInputCode⟩
    rcases hLeft.1.2.2 sourceLeftValue hSourceLeft with
      ⟨targetLeftValue, _, hLeftPair⟩
    rcases hRight.1.2.2 sourceRightValue hSourceRight with
      ⟨targetRightValue, _, hRightPair⟩
    rcases 𝕀.total targetLeftValue targetRightValue with
      ⟨output, hOutputCode⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_cartesianProductValue_iff
        𝕀 env input output).mpr
          ⟨sourceLeftValue, sourceRightValue,
            targetLeftValue, targetRightValue,
            hInputCode, hLeftPair, hRightPair, hOutputCode⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_cartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstSourceLeft, firstSourceRight,
        firstTargetLeft, firstTargetRight,
        hFirstInput, hFirstLeft, hFirstRight, hFirstOutput⟩
    rcases hSecond with
      ⟨secondSourceLeft, secondSourceRight,
        secondTargetLeft, secondTargetRight,
        hSecondInput, hSecondLeft, hSecondRight, hSecondOutput⟩
    rcases 𝕀.injective hFirstInput hSecondInput with
      ⟨hSourceLeftEq, hSourceRightEq⟩
    subst secondSourceLeft
    subst secondSourceRight
    have hTargetLeftEq :=
      hLeft.1.1.2 firstSourceLeft
        firstTargetLeft secondTargetLeft hFirstLeft hSecondLeft
    have hTargetRightEq :=
      hRight.1.1.2 firstSourceRight
        firstTargetRight secondTargetRight hFirstRight hSecondRight
    subst secondTargetLeft
    subst secondTargetRight
    exact 𝕀.unique hFirstOutput hSecondOutput
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_cartesianProductValue_iff 𝕀]
      at hValue
    rcases hValue with
      ⟨sourceLeftValue, sourceRightValue,
        targetLeftValue, targetRightValue,
        _, hLeftPair, hRightPair, hOutputCode⟩
    exact (hTargetProduct output).mpr
      ⟨targetLeftValue,
        hLeft.1.output_mem_of_pairMember hLeftPair,
        targetRightValue,
        hRight.1.output_mem_of_pairMember hRightPair,
        hOutputCode⟩
  · intro first second output _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_cartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstSourceLeft, firstSourceRight,
        firstTargetLeft, firstTargetRight,
        hFirstInput, hFirstLeft, hFirstRight, hFirstOutput⟩
    rcases hSecond with
      ⟨secondSourceLeft, secondSourceRight,
        secondTargetLeft, secondTargetRight,
        hSecondInput, hSecondLeft, hSecondRight, hSecondOutput⟩
    rcases 𝕀.injective hFirstOutput hSecondOutput with
      ⟨hTargetLeftEq, hTargetRightEq⟩
    subst secondTargetLeft
    subst secondTargetRight
    have hSourceLeftEq :=
      hLeft.2 firstSourceLeft secondSourceLeft
        firstTargetLeft hFirstLeft hSecondLeft
    have hSourceRightEq :=
      hRight.2 firstSourceRight secondSourceRight
        firstTargetRight hFirstRight hSecondRight
    subst secondSourceLeft
    subst secondSourceRight
    exact 𝕀.unique hFirstInput hSecondInput

/--
两个坐标上的双射逐点诱导笛卡尔积之间的双射。
-/
theorem equinumerous_cartesianProduct
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target sourceLeft sourceRight targetLeft targetRight
      leftFunction rightFunction : ℳ.Domain}
    (hSourceProduct :
      ℳ.IsCartesianProduct 𝕀 source sourceLeft sourceRight)
    (hTargetProduct :
      ℳ.IsCartesianProduct 𝕀 target targetLeft targetRight)
    (hLeft :
      ℳ.IsSetBijectionFromTo 𝕀
        leftFunction sourceLeft targetLeft)
    (hRight :
      ℳ.IsSetBijectionFromTo 𝕀
        rightFunction sourceRight targetRight) :
    ℳ.Equinumerous 𝕀 source target := by
  let env : Env ℳ 2 := {
    bound := Fin.cases leftFunction <|
      Fin.cases rightFunction Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.cartesianProductValue 𝒞) env
  · intro input hInput
    rcases (hSourceProduct input).mp hInput with
      ⟨sourceLeftValue, hSourceLeft,
        sourceRightValue, hSourceRight, hInputCode⟩
    rcases hLeft.1.1.2.2 sourceLeftValue hSourceLeft with
      ⟨targetLeftValue, _, hLeftPair⟩
    rcases hRight.1.1.2.2 sourceRightValue hSourceRight with
      ⟨targetRightValue, _, hRightPair⟩
    rcases 𝕀.total targetLeftValue targetRightValue with
      ⟨output, hOutputCode⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_cartesianProductValue_iff
        𝕀 env input output).mpr
          ⟨sourceLeftValue, sourceRightValue,
            targetLeftValue, targetRightValue,
            hInputCode, hLeftPair, hRightPair, hOutputCode⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_cartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstSourceLeft, firstSourceRight,
        firstTargetLeft, firstTargetRight,
        hFirstInput, hFirstLeft, hFirstRight, hFirstOutput⟩
    rcases hSecond with
      ⟨secondSourceLeft, secondSourceRight,
        secondTargetLeft, secondTargetRight,
        hSecondInput, hSecondLeft, hSecondRight, hSecondOutput⟩
    rcases 𝕀.injective hFirstInput hSecondInput with
      ⟨hSourceLeftEq, hSourceRightEq⟩
    subst secondSourceLeft
    subst secondSourceRight
    have hTargetLeftEq :=
      hLeft.1.1.1.2 firstSourceLeft
        firstTargetLeft secondTargetLeft hFirstLeft hSecondLeft
    have hTargetRightEq :=
      hRight.1.1.1.2 firstSourceRight
        firstTargetRight secondTargetRight hFirstRight hSecondRight
    subst secondTargetLeft
    subst secondTargetRight
    exact 𝕀.unique hFirstOutput hSecondOutput
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_cartesianProductValue_iff 𝕀] at hValue
    rcases hValue with
      ⟨sourceLeftValue, sourceRightValue,
        targetLeftValue, targetRightValue,
        _, hLeftPair, hRightPair, hOutputCode⟩
    apply (hTargetProduct output).mpr
    exact ⟨targetLeftValue,
      hLeft.1.1.output_mem_of_pairMember hLeftPair,
      targetRightValue,
      hRight.1.1.output_mem_of_pairMember hRightPair,
      hOutputCode⟩
  · intro first second output _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_cartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstSourceLeft, firstSourceRight,
        firstTargetLeft, firstTargetRight,
        hFirstInput, hFirstLeft, hFirstRight, hFirstOutput⟩
    rcases hSecond with
      ⟨secondSourceLeft, secondSourceRight,
        secondTargetLeft, secondTargetRight,
        hSecondInput, hSecondLeft, hSecondRight, hSecondOutput⟩
    rcases 𝕀.injective hFirstOutput hSecondOutput with
      ⟨hTargetLeftEq, hTargetRightEq⟩
    subst secondTargetLeft
    subst secondTargetRight
    have hSourceLeftEq :=
      hLeft.1.2 firstSourceLeft secondSourceLeft
        firstTargetLeft hFirstLeft hSecondLeft
    have hSourceRightEq :=
      hRight.1.2 firstSourceRight secondSourceRight
        firstTargetRight hFirstRight hSecondRight
    subst secondSourceLeft
    subst secondSourceRight
    exact 𝕀.unique hFirstInput hSecondInput
  · intro output hOutput
    rcases (hTargetProduct output).mp hOutput with
      ⟨targetLeftValue, hTargetLeft,
        targetRightValue, hTargetRight, hOutputCode⟩
    rcases hLeft.2 targetLeftValue hTargetLeft with
      ⟨sourceLeftValue, hSourceLeft, hLeftPair⟩
    rcases hRight.2 targetRightValue hTargetRight with
      ⟨sourceRightValue, hSourceRight, hRightPair⟩
    rcases 𝕀.total sourceLeftValue sourceRightValue with
      ⟨input, hInputCode⟩
    exact ⟨input,
      (hSourceProduct input).mpr
        ⟨sourceLeftValue, hSourceLeft,
          sourceRightValue, hSourceRight, hInputCode⟩,
      (Definitional.Project.Formula.denote_cartesianProductValue_iff
        𝕀 env input output).mpr
          ⟨sourceLeftValue, sourceRightValue,
            targetLeftValue, targetRightValue,
            hInputCode, hLeftPair, hRightPair, hOutputCode⟩⟩

/--
序数乘法的递归值与对应笛卡尔积等势。

函数图由序数乘法块及块内加法余项的对象语言关系收集，因而得到真正的模型内部双射。
-/
theorem equinumerous_cartesianProduct_ordinalMultiplication
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left right cartesian product : ℳ.Domain}
    (hLeft : ℳ.IsOrdinal left)
    (hRight : ℳ.IsOrdinal right)
    (hCartesian :
      ℳ.IsCartesianProduct 𝕀 cartesian left right)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left right) :
    ℳ.Equinumerous 𝕀 cartesian product := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have coordinates_mem
      {input leftValue rightValue : ℳ.Domain}
      (hInput : ℳ.mem input cartesian)
      (hCode : 𝕀.Codes input leftValue rightValue) :
      ℳ.mem leftValue left ∧ ℳ.mem rightValue right := by
    rcases (hCartesian input).mp hInput with
      ⟨selectedLeft, hSelectedLeft,
        selectedRight, hSelectedRight, hSelectedCode⟩
    rcases 𝕀.injective hCode hSelectedCode with
      ⟨hLeftEq, hRightEq⟩
    simpa [hLeftEq, hRightEq] using
      And.intro hSelectedLeft hSelectedRight
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀
        (Definitional.Project.BinarySchema.ordinalMultiplicationValue 𝒞)
        env
  · intro input hInput
    rcases (hCartesian input).mp hInput with
      ⟨leftValue, hLeftValue, rightValue, hRightValue, hInputCode⟩
    rcases ordinalMultiplication_existsUnique
        hZF 𝕀 left (hRight.mem hRightValue) with
      ⟨block, hBlock, _⟩
    rcases ordinalAddition_existsUnique
        hZF 𝕀 block (hLeft.mem hLeftValue) with
      ⟨output, hOutput, _⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_ordinalMultiplicationValue_iff
        𝕀 hZF.1 env input output).mpr
          ⟨leftValue, rightValue, block,
            hInputCode, hBlock, hOutput⟩⟩
  · intro input hInput first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_ordinalMultiplicationValue_iff
      𝕀 hZF.1] at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstRight, firstBlock,
        hFirstCode, hFirstBlock, hFirstValue⟩
    rcases hSecond with
      ⟨secondLeft, secondRight, secondBlock,
        hSecondCode, hSecondBlock, hSecondValue⟩
    rcases 𝕀.injective hFirstCode hSecondCode with
      ⟨hLeftEq, hRightEq⟩
    subst secondLeft
    subst secondRight
    have hCoordinates :=
      coordinates_mem hInput hFirstCode
    rcases ordinalMultiplication_existsUnique
        hZF 𝕀 left (hRight.mem hCoordinates.2) with
      ⟨selectedBlock, _, hBlockUnique⟩
    have hFirstBlockEq :=
      hBlockUnique firstBlock hFirstBlock
    have hSecondBlockEq :=
      hBlockUnique secondBlock hSecondBlock
    subst firstBlock
    subst secondBlock
    rcases ordinalAddition_existsUnique
        hZF 𝕀 selectedBlock (hLeft.mem hCoordinates.1) with
      ⟨selected, _, hUnique⟩
    exact (hUnique first hFirstValue).trans
      (hUnique second hSecondValue).symm
  · intro input output hInput hValue
    rw [Definitional.Project.Formula.denote_ordinalMultiplicationValue_iff
      𝕀 hZF.1] at hValue
    rcases hValue with
      ⟨leftValue, rightValue, block,
        hInputCode, hBlock, hOutput⟩
    have hCoordinates :=
      coordinates_mem hInput hInputCode
    exact (ordinalMultiplication_mem_iff
      hZF 𝕀 hLeft hRight hProduct).mpr
        ⟨rightValue, hCoordinates.2,
          block, hBlock, leftValue, hCoordinates.1, hOutput⟩
  · intro first second output hFirstInput hSecondInput
      hFirst hSecond
    rw [Definitional.Project.Formula.denote_ordinalMultiplicationValue_iff
      𝕀 hZF.1] at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstRight, firstBlock,
        hFirstCode, hFirstBlock, hFirstValue⟩
    rcases hSecond with
      ⟨secondLeft, secondRight, secondBlock,
        hSecondCode, hSecondBlock, hSecondValue⟩
    have hFirstCoordinates :=
      coordinates_mem hFirstInput hFirstCode
    have hSecondCoordinates :=
      coordinates_mem hSecondInput hSecondCode
    have hLeftNonempty : ∃ member, ℳ.mem member left :=
      ⟨firstLeft, hFirstCoordinates.1⟩
    have hCoordinateEq :=
      ordinalMultiplication_block_coordinates_unique
        hZF 𝕀 hLeft hLeftNonempty
        (hRight.mem hFirstCoordinates.2)
        (hRight.mem hSecondCoordinates.2)
        hFirstBlock hSecondBlock
        hFirstCoordinates.1 hSecondCoordinates.1
        hFirstValue hSecondValue
    rcases hCoordinateEq with
      ⟨hRightEq, hLeftEq⟩
    subst secondRight
    subst secondLeft
    exact 𝕀.unique hFirstCode hSecondCode
  · intro output hOutput
    rcases (ordinalMultiplication_mem_iff
        hZF 𝕀 hLeft hRight hProduct).mp hOutput with
      ⟨rightValue, hRightValue, block, hBlock,
        leftValue, hLeftValue, hValue⟩
    rcases 𝕀.total leftValue rightValue with
      ⟨input, hInputCode⟩
    exact ⟨input,
      (hCartesian input).mpr
        ⟨leftValue, hLeftValue,
          rightValue, hRightValue, hInputCode⟩,
      (Definitional.Project.Formula.denote_ordinalMultiplicationValue_iff
        𝕀 hZF.1 env input output).mpr
          ⟨leftValue, rightValue, block,
            hInputCode, hBlock, hValue⟩⟩

/--
若 `ω` 包含于 `set`，则 `set` 的集合后继仍与 `set` 等势。

正向单射把新点送到零、把自然数后移一位，并在 `set \ ω` 上保持恒等；反向单射取
后继中的自然包含。
-/
theorem equinumerous_successor_of_omegaSubset
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω set successor : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hOmegaSubset : ℳ.MemberSubset ω set)
    (hSuccessor : ℳ.SuccessorOf successor set) :
    ℳ.Equinumerous 𝕀 successor set := by
  rcases hω.1.1 with
    ⟨zero, hZero, hZeroOmega⟩
  have hZeroSet : ℳ.mem zero set :=
    hOmegaSubset zero hZeroOmega
  have hSetNotOmega : ¬ ℳ.mem set ω := by
    intro hSetOmega
    exact KP.mem_irrefl (ZF.modelsKP hZF) set <|
      hOmegaSubset set hSetOmega
  let env : Env ℳ 3 := {
    bound := Fin.cases set <|
      Fin.cases ω <| Fin.cases zero Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hValueSemantic (input output : ℳ.Domain) :
      Definitional.Project.BinarySchema.successorAbsorptionValue.denote
          env input output ↔
        (input = set ∧ output = zero) ∨
        (ℳ.mem input ω ∧ ℳ.SuccessorOf output input) ∨
        (input ≠ set ∧ ¬ ℳ.mem input ω ∧ output = input) := by
    rw [Definitional.Project.Formula.denote_successorAbsorptionValue_iff
      hZF.1 env input output]
    change
      ((input = set ∧ output = zero) ∨
        (ℳ.mem input ω ∧ ℳ.SuccessorOf output input) ∨
        (input ≠ set ∧ ¬ ℳ.mem input ω ∧ output = input)) ↔ _
    rfl
  have hSuccessorToSet :
      ℳ.CardinalLessOrEqual 𝕀 successor set := by
    apply exists_setInjectionFromTo_of_denote
        hZF 𝕀
          Definitional.Project.BinarySchema.successorAbsorptionValue env
    · intro input _
      by_cases hInputSet : input = set
      · exact ⟨zero, (hValueSemantic input zero).mpr <|
          Or.inl ⟨hInputSet, rfl⟩⟩
      · by_cases hInputOmega : ℳ.mem input ω
        · rcases hω.1.2 input hInputOmega with
            ⟨shifted, hShifted, _⟩
          exact ⟨shifted, (hValueSemantic input shifted).mpr <|
            Or.inr <| Or.inl ⟨hInputOmega, hShifted⟩⟩
        · exact ⟨input, (hValueSemantic input input).mpr <|
            Or.inr <| Or.inr ⟨hInputSet, hInputOmega, rfl⟩⟩
    · intro input _ first second hFirst hSecond
      rw [hValueSemantic] at hFirst hSecond
      rcases hFirst with hFirstExtra | hFirstNatural | hFirstFixed
      · rcases hSecond with hSecondExtra | hSecondNatural | hSecondFixed
        · exact hFirstExtra.2.trans hSecondExtra.2.symm
        · exact False.elim <| hSetNotOmega <| by
            simpa [hFirstExtra.1] using hSecondNatural.1
        · exact False.elim <| hSecondFixed.1 hFirstExtra.1
      · rcases hSecond with hSecondExtra | hSecondNatural | hSecondFixed
        · exact False.elim <| hSetNotOmega <| by
            simpa [hSecondExtra.1] using hFirstNatural.1
        · exact Structure.SuccessorOf.eq hZF.1
            hFirstNatural.2 hSecondNatural.2
        · exact False.elim <| hSecondFixed.2.1 hFirstNatural.1
      · rcases hSecond with hSecondExtra | hSecondNatural | hSecondFixed
        · exact False.elim <| hFirstFixed.1 hSecondExtra.1
        · exact False.elim <| hFirstFixed.2.1 hSecondNatural.1
        · exact hFirstFixed.2.2.trans hSecondFixed.2.2.symm
    · intro input output hInput hValue
      rw [hValueSemantic] at hValue
      rcases hValue with hExtra | hNatural | hFixed
      · simpa [hExtra.2] using hZeroSet
      · rcases hω.1.2 input hNatural.1 with
          ⟨selected, hSelected, hSelectedOmega⟩
        have hOutputEq :=
          Structure.SuccessorOf.eq hZF.1
            hNatural.2 hSelected
        exact hOmegaSubset output <| by
          simpa [hOutputEq] using hSelectedOmega
      · rcases (hSuccessor input).mp hInput with
          hInputSet | hInputSame
        · simpa [hFixed.2.2] using hInputSet
        · have hInputEq :=
            hZF.1.eq_of_same_members input set hInputSame
          exact False.elim <| hFixed.1 hInputEq
    · intro first second output hFirstInput hSecondInput
        hFirst hSecond
      rw [hValueSemantic] at hFirst hSecond
      rcases hFirst with hFirstExtra | hFirstNatural | hFirstFixed
      · rcases hSecond with hSecondExtra | hSecondNatural | hSecondFixed
        · exact hFirstExtra.1.trans hSecondExtra.1.symm
        · have hOutputEmpty : ∀ member, ¬ ℳ.mem member output := by
            simpa [hFirstExtra.2] using hZero
          exact False.elim <| hOutputEmpty second <|
            hSecondNatural.2.predecessor_mem
        · have hSecondEqZero :=
            hSecondFixed.2.2.symm.trans hFirstExtra.2
          exact False.elim <| hSecondFixed.2.1 <| by
            simpa [hSecondEqZero] using hZeroOmega
      · rcases hSecond with hSecondExtra | hSecondNatural | hSecondFixed
        · have hOutputEmpty : ∀ member, ¬ ℳ.mem member output := by
            simpa [hSecondExtra.2] using hZero
          exact False.elim <| hOutputEmpty first <|
            hFirstNatural.2.predecessor_mem
        · exact Structure.SuccessorOf.predecessor_eq hZF.1
            (hω.members_areOrdinals hZF first hFirstNatural.1)
            hFirstNatural.2 hSecondNatural.2
        · rcases hω.1.2 first hFirstNatural.1 with
            ⟨selected, hSelected, hSelectedOmega⟩
          have hSelectedEq :=
            Structure.SuccessorOf.eq hZF.1
              hSelected hFirstNatural.2
          exact False.elim <| hSecondFixed.2.1 <| by
            simpa [hSecondFixed.2.2, hSelectedEq] using hSelectedOmega
      · rcases hSecond with hSecondExtra | hSecondNatural | hSecondFixed
        · have hFirstEqZero :=
            hFirstFixed.2.2.symm.trans hSecondExtra.2
          exact False.elim <| hFirstFixed.2.1 <| by
            simpa [hFirstEqZero] using hZeroOmega
        · rcases hω.1.2 second hSecondNatural.1 with
            ⟨selected, hSelected, hSelectedOmega⟩
          have hSelectedEq :=
            Structure.SuccessorOf.eq hZF.1
              hSelected hSecondNatural.2
          exact False.elim <| hFirstFixed.2.1 <| by
            simpa [hFirstFixed.2.2, hSelectedEq] using hSelectedOmega
        · exact hFirstFixed.2.2.symm.trans hSecondFixed.2.2
  have hSetToSuccessor :
      ℳ.CardinalLessOrEqual 𝕀 set successor :=
    exists_inclusionInjection hZF 𝕀 fun value hValue =>
      (hSuccessor value).mpr <| Or.inl hValue
  exact equinumerous_of_cardinalLessOrEqual
    hZF 𝕀 hSuccessorToSet hSetToSuccessor

/--
笛卡尔积在右坐标的带标签不交并上分配到两个分量。
-/
theorem equinumerous_productOverTaggedUnion
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left rightLeft rightRight rightUnion source
      leftProduct rightProduct target leftTag rightTag : ℳ.Domain}
    (hRightUnion :
      ℳ.IsTaggedUnion 𝕀
        rightUnion leftTag rightTag rightLeft rightRight)
    (hSource :
      ℳ.IsCartesianProduct 𝕀 source left rightUnion)
    (hLeftProduct :
      ℳ.IsCartesianProduct 𝕀 leftProduct left rightLeft)
    (hRightProduct :
      ℳ.IsCartesianProduct 𝕀 rightProduct left rightRight)
    (hTarget :
      ℳ.IsTaggedUnion 𝕀
        target leftTag rightTag leftProduct rightProduct) :
    ℳ.Equinumerous 𝕀 source target := by
  rcases hRightUnion with
    ⟨rightLeftCopy, rightRightCopy,
      hRightLeftCopy, hRightRightCopy,
      hRightDisjoint, hRightUnion⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀 left rightLeftCopy with
    ⟨sourceLeft, hSourceLeft⟩
  rcases ZF.exists_cartesianProduct hZF 𝕀 left rightRightCopy with
    ⟨sourceRight, hSourceRight⟩
  have hSourceUnion :=
    hSource.union_right hSourceLeft hSourceRight hRightUnion
  have hSourceDisjoint :=
    hSourceLeft.disjoint_right hSourceRight hRightDisjoint
  rcases Structure.Equinumerous.refl hZF 𝕀 left with
    ⟨leftIdentity, hLeftIdentity⟩
  have hRightLeftEquinumerous :=
    (equinumerous_cartesianRow hZF 𝕀
      hRightLeftCopy).symm hZF 𝕀
  have hRightRightEquinumerous :=
    (equinumerous_cartesianRow hZF 𝕀
      hRightRightCopy).symm hZF 𝕀
  rcases hRightLeftEquinumerous with
    ⟨rightLeftFunction, hRightLeftFunction⟩
  rcases hRightRightEquinumerous with
    ⟨rightRightFunction, hRightRightFunction⟩
  have hSourceLeftEquinumerous :=
    equinumerous_cartesianProduct hZF 𝕀
      hSourceLeft hLeftProduct
      hLeftIdentity hRightLeftFunction
  have hSourceRightEquinumerous :=
    equinumerous_cartesianProduct hZF 𝕀
      hSourceRight hRightProduct
      hLeftIdentity hRightRightFunction
  exact equinumerous_unionToTaggedUnion hZF 𝕀
    hSourceUnion hSourceDisjoint hTarget
    hSourceLeftEquinumerous hSourceRightEquinumerous

/--
交换两个坐标，并在交换后的对应坐标上应用双射。
-/
theorem equinumerous_swappedCartesianProduct
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target sourceLeft sourceRight targetLeft targetRight
      leftFunction rightFunction : ℳ.Domain}
    (hSourceProduct :
      ℳ.IsCartesianProduct 𝕀 source sourceLeft sourceRight)
    (hTargetProduct :
      ℳ.IsCartesianProduct 𝕀 target targetLeft targetRight)
    (hLeft :
      ℳ.IsSetBijectionFromTo 𝕀
        leftFunction sourceLeft targetRight)
    (hRight :
      ℳ.IsSetBijectionFromTo 𝕀
        rightFunction sourceRight targetLeft) :
    ℳ.Equinumerous 𝕀 source target := by
  let env : Env ℳ 2 := {
    bound := Fin.cases leftFunction <|
      Fin.cases rightFunction Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀
        (Definitional.Project.BinarySchema.swappedCartesianProductValue 𝒞) env
  · intro input hInput
    rcases (hSourceProduct input).mp hInput with
      ⟨sourceLeftValue, hSourceLeft,
        sourceRightValue, hSourceRight, hInputCode⟩
    rcases hLeft.1.1.2.2 sourceLeftValue hSourceLeft with
      ⟨targetRightValue, _, hLeftPair⟩
    rcases hRight.1.1.2.2 sourceRightValue hSourceRight with
      ⟨targetLeftValue, _, hRightPair⟩
    rcases 𝕀.total targetLeftValue targetRightValue with
      ⟨output, hOutputCode⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_swappedCartesianProductValue_iff
        𝕀 env input output).mpr
          ⟨sourceLeftValue, sourceRightValue,
            targetLeftValue, targetRightValue,
            hInputCode, hLeftPair, hRightPair, hOutputCode⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_swappedCartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstSourceLeft, firstSourceRight,
        firstTargetLeft, firstTargetRight,
        hFirstInput, hFirstLeft, hFirstRight, hFirstOutput⟩
    rcases hSecond with
      ⟨secondSourceLeft, secondSourceRight,
        secondTargetLeft, secondTargetRight,
        hSecondInput, hSecondLeft, hSecondRight, hSecondOutput⟩
    rcases 𝕀.injective hFirstInput hSecondInput with
      ⟨hSourceLeftEq, hSourceRightEq⟩
    subst secondSourceLeft
    subst secondSourceRight
    have hTargetRightEq :=
      hLeft.1.1.1.2 firstSourceLeft
        firstTargetRight secondTargetRight hFirstLeft hSecondLeft
    have hTargetLeftEq :=
      hRight.1.1.1.2 firstSourceRight
        firstTargetLeft secondTargetLeft hFirstRight hSecondRight
    subst secondTargetLeft
    subst secondTargetRight
    exact 𝕀.unique hFirstOutput hSecondOutput
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_swappedCartesianProductValue_iff 𝕀]
      at hValue
    rcases hValue with
      ⟨sourceLeftValue, sourceRightValue,
        targetLeftValue, targetRightValue,
        _, hLeftPair, hRightPair, hOutputCode⟩
    apply (hTargetProduct output).mpr
    exact ⟨targetLeftValue,
      hRight.1.1.output_mem_of_pairMember hRightPair,
      targetRightValue,
      hLeft.1.1.output_mem_of_pairMember hLeftPair,
      hOutputCode⟩
  · intro first second output _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_swappedCartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstSourceLeft, firstSourceRight,
        firstTargetLeft, firstTargetRight,
        hFirstInput, hFirstLeft, hFirstRight, hFirstOutput⟩
    rcases hSecond with
      ⟨secondSourceLeft, secondSourceRight,
        secondTargetLeft, secondTargetRight,
        hSecondInput, hSecondLeft, hSecondRight, hSecondOutput⟩
    rcases 𝕀.injective hFirstOutput hSecondOutput with
      ⟨hTargetLeftEq, hTargetRightEq⟩
    subst secondTargetLeft
    subst secondTargetRight
    have hSourceLeftEq :=
      hLeft.1.2 firstSourceLeft secondSourceLeft
        firstTargetRight hFirstLeft hSecondLeft
    have hSourceRightEq :=
      hRight.1.2 firstSourceRight secondSourceRight
        firstTargetLeft hFirstRight hSecondRight
    subst secondSourceLeft
    subst secondSourceRight
    exact 𝕀.unique hFirstInput hSecondInput
  · intro output hOutput
    rcases (hTargetProduct output).mp hOutput with
      ⟨targetLeftValue, hTargetLeft,
        targetRightValue, hTargetRight, hOutputCode⟩
    rcases hLeft.2 targetRightValue hTargetRight with
      ⟨sourceLeftValue, hSourceLeft, hLeftPair⟩
    rcases hRight.2 targetLeftValue hTargetLeft with
      ⟨sourceRightValue, hSourceRight, hRightPair⟩
    rcases 𝕀.total sourceLeftValue sourceRightValue with
      ⟨input, hInputCode⟩
    exact ⟨input,
      (hSourceProduct input).mpr
        ⟨sourceLeftValue, hSourceLeft,
          sourceRightValue, hSourceRight, hInputCode⟩,
      (Definitional.Project.Formula.denote_swappedCartesianProductValue_iff
        𝕀 env input output).mpr
          ⟨sourceLeftValue, sourceRightValue,
            targetLeftValue, targetRightValue,
            hInputCode, hLeftPair, hRightPair, hOutputCode⟩⟩

/--
定义域与值域分别等势时，相应的函数集等势。
-/
theorem equinumerous_functionSpace
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sourceSpace targetSpace sourceDomain sourceBase
      targetDomain targetBase : ℳ.Domain}
    (hSourceSpace :
      ℳ.IsFunctionSpace 𝕀 sourceSpace sourceDomain sourceBase)
    (hTargetSpace :
      ℳ.IsFunctionSpace 𝕀 targetSpace targetDomain targetBase)
    (hDomain :
      ℳ.Equinumerous 𝕀 sourceDomain targetDomain)
    (hBase :
      ℳ.Equinumerous 𝕀 sourceBase targetBase) :
    ℳ.Equinumerous 𝕀 sourceSpace targetSpace := by
  rcases hDomain with ⟨domainMap, hDomainMap⟩
  rcases hBase with ⟨baseMap, hBaseMap⟩
  rcases exists_functionSpaceTransportInjection hZF 𝕀
      hSourceSpace hTargetSpace hDomainMap hBaseMap.1 with
    ⟨forward, hForward⟩
  rcases exists_inverseBijection hZF 𝕀 hDomainMap with
    ⟨inverseDomainMap, hInverseDomainMap⟩
  rcases exists_inverseBijection hZF 𝕀 hBaseMap with
    ⟨inverseBaseMap, hInverseBaseMap⟩
  rcases exists_functionSpaceTransportInjection hZF 𝕀
      hTargetSpace hSourceSpace hInverseDomainMap hInverseBaseMap.1 with
    ⟨reverse, hReverse⟩
  exact equinumerous_of_injections hZF 𝕀 hForward hReverse

/-- 笛卡尔积满足标准重括号等势。 -/
theorem equinumerous_associatedCartesianProduct
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left middle right leftProduct source rightProduct target : ℳ.Domain}
    (hLeftProduct :
      ℳ.IsCartesianProduct 𝕀 leftProduct left middle)
    (hSource :
      ℳ.IsCartesianProduct 𝕀 source leftProduct right)
    (hRightProduct :
      ℳ.IsCartesianProduct 𝕀 rightProduct middle right)
    (hTarget :
      ℳ.IsCartesianProduct 𝕀 target left rightProduct) :
    ℳ.Equinumerous 𝕀 source target := by
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀
        (Definitional.Project.BinarySchema.associateCartesianProductValue 𝒞) env
  · intro input hInput
    rcases (hSource input).mp hInput with
      ⟨leftPair, hLeftPair, rightValue, hRight, hInputCode⟩
    rcases (hLeftProduct leftPair).mp hLeftPair with
      ⟨leftValue, hLeft, middleValue, hMiddle, hLeftCode⟩
    rcases 𝕀.total middleValue rightValue with
      ⟨rightPair, hRightCode⟩
    rcases 𝕀.total leftValue rightPair with
      ⟨output, hOutputCode⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_associateCartesianProductValue_iff
        𝕀 env input output).mpr
          ⟨leftValue, middleValue, rightValue,
            leftPair, rightPair,
            hLeftCode, hInputCode, hRightCode, hOutputCode⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_associateCartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstMiddle, firstRight,
        firstLeftPair, firstRightPair,
        hFirstLeftCode, hFirstInput, hFirstRightCode, hFirstOutput⟩
    rcases hSecond with
      ⟨secondLeft, secondMiddle, secondRight,
        secondLeftPair, secondRightPair,
        hSecondLeftCode, hSecondInput, hSecondRightCode, hSecondOutput⟩
    rcases 𝕀.injective hFirstInput hSecondInput with
      ⟨hLeftPairEq, hRightEq⟩
    subst secondLeftPair
    subst secondRight
    rcases 𝕀.injective hFirstLeftCode hSecondLeftCode with
      ⟨hLeftEq, hMiddleEq⟩
    subst secondLeft
    subst secondMiddle
    have hRightPairEq := 𝕀.unique hFirstRightCode hSecondRightCode
    subst secondRightPair
    exact 𝕀.unique hFirstOutput hSecondOutput
  · intro input output hInput hValue
    rw [Definitional.Project.Formula.denote_associateCartesianProductValue_iff 𝕀]
      at hValue
    rcases hValue with
      ⟨leftValue, middleValue, rightValue,
        leftPair, rightPair,
        hLeftCode, hInputCode, hRightCode, hOutputCode⟩
    rcases (hSource input).mp hInput with
      ⟨sourceLeftPair, hSourceLeftPair,
        sourceRightValue, hSourceRight, hSourceInputCode⟩
    rcases 𝕀.injective hInputCode hSourceInputCode with
      ⟨hLeftPairEq, hRightEq⟩
    subst sourceLeftPair
    subst sourceRightValue
    rcases (hLeftProduct leftPair).mp hSourceLeftPair with
      ⟨sourceLeftValue, hSourceLeft,
        sourceMiddleValue, hSourceMiddle, hSourceLeftCode⟩
    rcases 𝕀.injective hLeftCode hSourceLeftCode with
      ⟨hLeftEq, hMiddleEq⟩
    subst sourceLeftValue
    subst sourceMiddleValue
    apply (hTarget output).mpr
    exact ⟨leftValue,
      hSourceLeft,
      rightPair,
      (hRightProduct rightPair).mpr
        ⟨middleValue, hSourceMiddle,
          rightValue, hSourceRight, hRightCode⟩,
      hOutputCode⟩
  · intro first second output _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_associateCartesianProductValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstMiddle, firstRight,
        firstLeftPair, firstRightPair,
        hFirstLeftCode, hFirstInput, hFirstRightCode, hFirstOutput⟩
    rcases hSecond with
      ⟨secondLeft, secondMiddle, secondRight,
        secondLeftPair, secondRightPair,
        hSecondLeftCode, hSecondInput, hSecondRightCode, hSecondOutput⟩
    rcases 𝕀.injective hFirstOutput hSecondOutput with
      ⟨hLeftEq, hRightPairEq⟩
    subst secondLeft
    subst secondRightPair
    rcases 𝕀.injective hFirstRightCode hSecondRightCode with
      ⟨hMiddleEq, hRightEq⟩
    subst secondMiddle
    subst secondRight
    have hLeftPairEq := 𝕀.unique hFirstLeftCode hSecondLeftCode
    subst secondLeftPair
    exact 𝕀.unique hFirstInput hSecondInput
  · intro output hOutput
    rcases (hTarget output).mp hOutput with
      ⟨leftValue, hLeft, rightPair, hRightPair, hOutputCode⟩
    rcases (hRightProduct rightPair).mp hRightPair with
      ⟨middleValue, hMiddle, rightValue, hRight, hRightCode⟩
    rcases 𝕀.total leftValue middleValue with
      ⟨leftPair, hLeftCode⟩
    rcases 𝕀.total leftPair rightValue with
      ⟨input, hInputCode⟩
    exact ⟨input,
      (hSource input).mpr
        ⟨leftPair,
          (hLeftProduct leftPair).mpr
            ⟨leftValue, hLeft,
              middleValue, hMiddle, hLeftCode⟩,
          rightValue, hRight, hInputCode⟩,
      (Definitional.Project.Formula.denote_associateCartesianProductValue_iff
        𝕀 env input output).mpr
          ⟨leftValue, middleValue, rightValue,
            leftPair, rightPair,
            hLeftCode, hInputCode, hRightCode, hOutputCode⟩⟩

/-- 带标签不交并满足标准重括号等势。 -/
theorem equinumerous_associatedTaggedUnion
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {leftTag rightTag left middle right
      leftMiddle source middleRight target : ℳ.Domain}
    (hTags : leftTag ≠ rightTag)
    (hLeftMiddle :
      ℳ.IsTaggedUnion 𝕀
        leftMiddle leftTag rightTag left middle)
    (hSource :
      ℳ.IsTaggedUnion 𝕀
        source leftTag rightTag leftMiddle right)
    (hMiddleRight :
      ℳ.IsTaggedUnion 𝕀
        middleRight leftTag rightTag middle right)
    (hTarget :
      ℳ.IsTaggedUnion 𝕀
        target leftTag rightTag left middleRight) :
    ℳ.Equinumerous 𝕀 source target := by
  rcases hLeftMiddle with
    ⟨leftCopy, middleCopy,
      hLeftCopy, hMiddleCopy, _, hLeftMiddleUnion⟩
  rcases hSource with
    ⟨sourceLeft, sourceRight,
      hSourceLeft, hSourceRight, _, hSourceUnion⟩
  rcases hMiddleRight with
    ⟨middleCopy', rightCopy,
      hMiddleCopy', hRightCopy, _, hMiddleRightUnion⟩
  rcases hTarget with
    ⟨targetLeft, targetRight,
      hTargetLeft, hTargetRight, _, hTargetUnion⟩
  let env : Env ℳ 2 := {
    bound := Fin.cases leftTag <| Fin.cases rightTag Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀
        (Definitional.Project.BinarySchema.associateTaggedUnionValue 𝒞) env
  · intro input hInput
    rcases (hSourceUnion input).mp hInput with
      hInputLeft | hInputRight
    · rcases (hSourceLeft input).mp hInputLeft with
        ⟨inner, hInner, hInputCode⟩
      rcases (hLeftMiddleUnion inner).mp hInner with
        hInnerLeft | hInnerMiddle
      · rcases (hLeftCopy inner).mp hInnerLeft with
          ⟨value, _, hInnerCode⟩
        rcases 𝕀.total leftTag value with ⟨output, hOutputCode⟩
        exact ⟨output,
          (Definitional.Project.Formula.denote_associateTaggedUnionValue_iff
            𝕀 env input output).mpr <|
              Or.inl ⟨inner, value,
                hInputCode, hInnerCode, hOutputCode⟩⟩
      · rcases (hMiddleCopy inner).mp hInnerMiddle with
          ⟨value, _, hInnerCode⟩
        rcases 𝕀.total leftTag value with
          ⟨innerOutput, hInnerOutputCode⟩
        rcases 𝕀.total rightTag innerOutput with
          ⟨output, hOutputCode⟩
        exact ⟨output,
          (Definitional.Project.Formula.denote_associateTaggedUnionValue_iff
            𝕀 env input output).mpr <|
              Or.inr <| Or.inl
                ⟨inner, value, innerOutput,
                  hInputCode, hInnerCode,
                  hInnerOutputCode, hOutputCode⟩⟩
    · rcases (hSourceRight input).mp hInputRight with
        ⟨value, _, hInputCode⟩
      rcases 𝕀.total rightTag value with
        ⟨innerOutput, hInnerOutputCode⟩
      rcases 𝕀.total rightTag innerOutput with
        ⟨output, hOutputCode⟩
      exact ⟨output,
        (Definitional.Project.Formula.denote_associateTaggedUnionValue_iff
          𝕀 env input output).mpr <|
            Or.inr <| Or.inr
              ⟨value, innerOutput,
                hInputCode, hInnerOutputCode, hOutputCode⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_associateTaggedUnionValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with hFirstLeft | hFirstMiddle | hFirstRight
    · rcases hSecond with hSecondLeft | hSecondMiddle | hSecondRight
      · rcases hFirstLeft with
          ⟨firstInner, firstValue,
            hFirstInput, hFirstInner, hFirstOutput⟩
        rcases hSecondLeft with
          ⟨secondInner, secondValue,
            hSecondInput, hSecondInner, hSecondOutput⟩
        rcases 𝕀.injective hFirstInput hSecondInput with
          ⟨_, hInnerEq⟩
        subst secondInner
        rcases 𝕀.injective hFirstInner hSecondInner with
          ⟨_, hValueEq⟩
        subst secondValue
        exact 𝕀.unique hFirstOutput hSecondOutput
      · rcases hFirstLeft with
          ⟨firstInner, _, hFirstInput, hFirstInner, _⟩
        rcases hSecondMiddle with
          ⟨secondInner, _, _, hSecondInput, hSecondInner, _, _⟩
        have hInnerEq := (𝕀.injective hFirstInput hSecondInput).2
        subst secondInner
        exact False.elim <| hTags <|
          (𝕀.injective hFirstInner hSecondInner).1
      · rcases hFirstLeft with
          ⟨_, _, hFirstInput, _, _⟩
        rcases hSecondRight with
          ⟨_, _, hSecondInput, _, _⟩
        exact False.elim <| hTags <|
          (𝕀.injective hFirstInput hSecondInput).1
    · rcases hSecond with hSecondLeft | hSecondMiddle | hSecondRight
      · rcases hFirstMiddle with
          ⟨firstInner, _, _, hFirstInput, hFirstInner, _, _⟩
        rcases hSecondLeft with
          ⟨secondInner, _, hSecondInput, hSecondInner, _⟩
        have hInnerEq := (𝕀.injective hFirstInput hSecondInput).2
        subst secondInner
        exact False.elim <| hTags <|
          (𝕀.injective hSecondInner hFirstInner).1
      · rcases hFirstMiddle with
          ⟨firstInner, firstValue, firstInnerOutput,
            hFirstInput, hFirstInner,
            hFirstInnerOutput, hFirstOutput⟩
        rcases hSecondMiddle with
          ⟨secondInner, secondValue, secondInnerOutput,
            hSecondInput, hSecondInner,
            hSecondInnerOutput, hSecondOutput⟩
        have hInnerEq := (𝕀.injective hFirstInput hSecondInput).2
        subst secondInner
        have hValueEq := (𝕀.injective hFirstInner hSecondInner).2
        subst secondValue
        have hInnerOutputEq :=
          𝕀.unique hFirstInnerOutput hSecondInnerOutput
        subst secondInnerOutput
        exact 𝕀.unique hFirstOutput hSecondOutput
      · rcases hFirstMiddle with
          ⟨_, _, _, hFirstInput, _, _, _⟩
        rcases hSecondRight with
          ⟨_, _, hSecondInput, _, _⟩
        exact False.elim <| hTags <|
          (𝕀.injective hFirstInput hSecondInput).1
    · rcases hSecond with hSecondLeft | hSecondMiddle | hSecondRight
      · rcases hFirstRight with
          ⟨_, _, hFirstInput, _, _⟩
        rcases hSecondLeft with
          ⟨_, _, hSecondInput, _, _⟩
        exact False.elim <| hTags <|
          (𝕀.injective hSecondInput hFirstInput).1
      · rcases hFirstRight with
          ⟨_, _, hFirstInput, _, _⟩
        rcases hSecondMiddle with
          ⟨_, _, _, hSecondInput, _, _, _⟩
        exact False.elim <| hTags <|
          (𝕀.injective hSecondInput hFirstInput).1
      · rcases hFirstRight with
          ⟨firstValue, firstInnerOutput,
            hFirstInput, hFirstInnerOutput, hFirstOutput⟩
        rcases hSecondRight with
          ⟨secondValue, secondInnerOutput,
            hSecondInput, hSecondInnerOutput, hSecondOutput⟩
        have hValueEq := (𝕀.injective hFirstInput hSecondInput).2
        subst secondValue
        have hInnerOutputEq :=
          𝕀.unique hFirstInnerOutput hSecondInnerOutput
        subst secondInnerOutput
        exact 𝕀.unique hFirstOutput hSecondOutput
  · intro input output hInput hValue
    rw [Definitional.Project.Formula.denote_associateTaggedUnionValue_iff 𝕀]
      at hValue
    rcases (hSourceUnion input).mp hInput with
      hInputLeft | hInputRight
    · rcases (hSourceLeft input).mp hInputLeft with
        ⟨sourceInner, hSourceInner, hSourceInputCode⟩
      rcases (hLeftMiddleUnion sourceInner).mp hSourceInner with
        hSourceInnerLeft | hSourceInnerMiddle
      · rcases (hLeftCopy sourceInner).mp hSourceInnerLeft with
          ⟨sourceValue, hSourceValue, hSourceInnerCode⟩
        rcases hValue with hLeft | hMiddle | hRight
        · rcases hLeft with
            ⟨inner, value, hInputCode, hInnerCode, hOutputCode⟩
          have hInnerEq := (𝕀.injective hInputCode hSourceInputCode).2
          subst sourceInner
          have hValueEq := (𝕀.injective hInnerCode hSourceInnerCode).2
          subst sourceValue
          exact (hTargetUnion output).mpr <| Or.inl <|
            (hTargetLeft output).mpr
              ⟨value, hSourceValue, hOutputCode⟩
        · rcases hMiddle with
            ⟨inner, _, _, hInputCode, hInnerCode, _, _⟩
          have hInnerEq := (𝕀.injective hInputCode hSourceInputCode).2
          subst sourceInner
          exact False.elim <| hTags <|
            (𝕀.injective hSourceInnerCode hInnerCode).1
        · rcases hRight with
            ⟨_, _, hInputCode, _, _⟩
          exact False.elim <| hTags <|
            (𝕀.injective hSourceInputCode hInputCode).1
      · rcases (hMiddleCopy sourceInner).mp hSourceInnerMiddle with
          ⟨sourceValue, hSourceValue, hSourceInnerCode⟩
        rcases hValue with hLeft | hMiddle | hRight
        · rcases hLeft with
            ⟨inner, _, hInputCode, hInnerCode, _⟩
          have hInnerEq := (𝕀.injective hInputCode hSourceInputCode).2
          subst sourceInner
          exact False.elim <| hTags <|
            (𝕀.injective hInnerCode hSourceInnerCode).1
        · rcases hMiddle with
            ⟨inner, value, innerOutput,
              hInputCode, hInnerCode,
              hInnerOutputCode, hOutputCode⟩
          have hInnerEq := (𝕀.injective hInputCode hSourceInputCode).2
          subst sourceInner
          have hValueEq := (𝕀.injective hInnerCode hSourceInnerCode).2
          subst sourceValue
          exact (hTargetUnion output).mpr <| Or.inr <|
            (hTargetRight output).mpr
              ⟨innerOutput,
                (hMiddleRightUnion innerOutput).mpr <| Or.inl <|
                  (hMiddleCopy' innerOutput).mpr
                    ⟨value, hSourceValue, hInnerOutputCode⟩,
                hOutputCode⟩
        · rcases hRight with
            ⟨_, _, hInputCode, _, _⟩
          exact False.elim <| hTags <|
            (𝕀.injective hSourceInputCode hInputCode).1
    · rcases (hSourceRight input).mp hInputRight with
        ⟨sourceValue, hSourceValue, hSourceInputCode⟩
      rcases hValue with hLeft | hMiddle | hRight
      · rcases hLeft with
          ⟨_, _, hInputCode, _, _⟩
        exact False.elim <| hTags <|
          (𝕀.injective hInputCode hSourceInputCode).1
      · rcases hMiddle with
          ⟨_, _, _, hInputCode, _, _, _⟩
        exact False.elim <| hTags <|
          (𝕀.injective hInputCode hSourceInputCode).1
      · rcases hRight with
          ⟨value, innerOutput,
            hInputCode, hInnerOutputCode, hOutputCode⟩
        have hValueEq := (𝕀.injective hInputCode hSourceInputCode).2
        subst sourceValue
        exact (hTargetUnion output).mpr <| Or.inr <|
          (hTargetRight output).mpr
            ⟨innerOutput,
              (hMiddleRightUnion innerOutput).mpr <| Or.inr <|
                (hRightCopy innerOutput).mpr
                  ⟨value, hSourceValue, hInnerOutputCode⟩,
              hOutputCode⟩
  · intro first second output _ _ hFirst hSecond
    rw [Definitional.Project.Formula.denote_associateTaggedUnionValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with hFirstLeft | hFirstMiddle | hFirstRight
    · rcases hSecond with hSecondLeft | hSecondMiddle | hSecondRight
      · rcases hFirstLeft with
          ⟨firstInner, firstValue,
            hFirstInput, hFirstInner, hFirstOutput⟩
        rcases hSecondLeft with
          ⟨secondInner, secondValue,
            hSecondInput, hSecondInner, hSecondOutput⟩
        have hValueEq := (𝕀.injective hFirstOutput hSecondOutput).2
        subst secondValue
        have hInnerEq := 𝕀.unique hFirstInner hSecondInner
        subst secondInner
        exact 𝕀.unique hFirstInput hSecondInput
      · rcases hFirstLeft with
          ⟨_, _, _, _, hFirstOutput⟩
        rcases hSecondMiddle with
          ⟨_, _, _, _, _, _, hSecondOutput⟩
        exact False.elim <| hTags <|
          (𝕀.injective hFirstOutput hSecondOutput).1
      · rcases hFirstLeft with
          ⟨_, _, _, _, hFirstOutput⟩
        rcases hSecondRight with
          ⟨_, _, _, _, hSecondOutput⟩
        exact False.elim <| hTags <|
          (𝕀.injective hFirstOutput hSecondOutput).1
    · rcases hSecond with hSecondLeft | hSecondMiddle | hSecondRight
      · rcases hFirstMiddle with
          ⟨_, _, _, _, _, _, hFirstOutput⟩
        rcases hSecondLeft with
          ⟨_, _, _, _, hSecondOutput⟩
        exact False.elim <| hTags <|
          (𝕀.injective hSecondOutput hFirstOutput).1
      · rcases hFirstMiddle with
          ⟨firstInner, firstValue, firstInnerOutput,
            hFirstInput, hFirstInner,
            hFirstInnerOutput, hFirstOutput⟩
        rcases hSecondMiddle with
          ⟨secondInner, secondValue, secondInnerOutput,
            hSecondInput, hSecondInner,
            hSecondInnerOutput, hSecondOutput⟩
        have hInnerOutputEq :=
          (𝕀.injective hFirstOutput hSecondOutput).2
        subst secondInnerOutput
        have hValueEq :=
          (𝕀.injective hFirstInnerOutput hSecondInnerOutput).2
        subst secondValue
        have hInnerEq := 𝕀.unique hFirstInner hSecondInner
        subst secondInner
        exact 𝕀.unique hFirstInput hSecondInput
      · rcases hFirstMiddle with
          ⟨_, _, firstInnerOutput, _, _,
            hFirstInnerOutput, hFirstOutput⟩
        rcases hSecondRight with
          ⟨_, secondInnerOutput, _,
            hSecondInnerOutput, hSecondOutput⟩
        have hInnerOutputEq :=
          (𝕀.injective hFirstOutput hSecondOutput).2
        subst secondInnerOutput
        exact False.elim <| hTags <|
          (𝕀.injective hFirstInnerOutput hSecondInnerOutput).1
    · rcases hSecond with hSecondLeft | hSecondMiddle | hSecondRight
      · rcases hFirstRight with
          ⟨_, _, _, _, hFirstOutput⟩
        rcases hSecondLeft with
          ⟨_, _, _, _, hSecondOutput⟩
        exact False.elim <| hTags <|
          (𝕀.injective hSecondOutput hFirstOutput).1
      · rcases hFirstRight with
          ⟨_, firstInnerOutput, _,
            hFirstInnerOutput, hFirstOutput⟩
        rcases hSecondMiddle with
          ⟨_, _, secondInnerOutput, _, _,
            hSecondInnerOutput, hSecondOutput⟩
        have hInnerOutputEq :=
          (𝕀.injective hFirstOutput hSecondOutput).2
        subst secondInnerOutput
        exact False.elim <| hTags <|
          (𝕀.injective hSecondInnerOutput hFirstInnerOutput).1
      · rcases hFirstRight with
          ⟨firstValue, firstInnerOutput,
            hFirstInput, hFirstInnerOutput, hFirstOutput⟩
        rcases hSecondRight with
          ⟨secondValue, secondInnerOutput,
            hSecondInput, hSecondInnerOutput, hSecondOutput⟩
        have hInnerOutputEq :=
          (𝕀.injective hFirstOutput hSecondOutput).2
        subst secondInnerOutput
        have hValueEq :=
          (𝕀.injective hFirstInnerOutput hSecondInnerOutput).2
        subst secondValue
        exact 𝕀.unique hFirstInput hSecondInput
  · intro output hOutput
    rcases (hTargetUnion output).mp hOutput with
      hOutputLeft | hOutputRight
    · rcases (hTargetLeft output).mp hOutputLeft with
        ⟨value, hValue, hOutputCode⟩
      rcases 𝕀.total leftTag value with ⟨inner, hInnerCode⟩
      rcases 𝕀.total leftTag inner with ⟨input, hInputCode⟩
      exact ⟨input,
        (hSourceUnion input).mpr <| Or.inl <|
          (hSourceLeft input).mpr
            ⟨inner,
              (hLeftMiddleUnion inner).mpr <| Or.inl <|
                (hLeftCopy inner).mpr
                  ⟨value, hValue, hInnerCode⟩,
              hInputCode⟩,
        (Definitional.Project.Formula.denote_associateTaggedUnionValue_iff
          𝕀 env input output).mpr <| Or.inl
            ⟨inner, value, hInputCode, hInnerCode, hOutputCode⟩⟩
    · rcases (hTargetRight output).mp hOutputRight with
        ⟨innerOutput, hInnerOutput, hOutputCode⟩
      rcases (hMiddleRightUnion innerOutput).mp hInnerOutput with
        hInnerOutputMiddle | hInnerOutputRight
      · rcases (hMiddleCopy' innerOutput).mp hInnerOutputMiddle with
          ⟨value, hValue, hInnerOutputCode⟩
        rcases 𝕀.total rightTag value with ⟨inner, hInnerCode⟩
        rcases 𝕀.total leftTag inner with ⟨input, hInputCode⟩
        exact ⟨input,
          (hSourceUnion input).mpr <| Or.inl <|
            (hSourceLeft input).mpr
              ⟨inner,
                (hLeftMiddleUnion inner).mpr <| Or.inr <|
                  (hMiddleCopy inner).mpr
                    ⟨value, hValue, hInnerCode⟩,
                hInputCode⟩,
          (Definitional.Project.Formula.denote_associateTaggedUnionValue_iff
            𝕀 env input output).mpr <| Or.inr <| Or.inl
              ⟨inner, value, innerOutput,
                hInputCode, hInnerCode,
                hInnerOutputCode, hOutputCode⟩⟩
      · rcases (hRightCopy innerOutput).mp hInnerOutputRight with
          ⟨value, hValue, hInnerOutputCode⟩
        rcases 𝕀.total rightTag value with ⟨input, hInputCode⟩
        exact ⟨input,
          (hSourceUnion input).mpr <| Or.inr <|
            (hSourceRight input).mpr
              ⟨value, hValue, hInputCode⟩,
          (Definitional.Project.Formula.denote_associateTaggedUnionValue_iff
            𝕀 env input output).mpr <| Or.inr <| Or.inr
              ⟨value, innerOutput,
                hInputCode, hInnerOutputCode, hOutputCode⟩⟩

end ZF

end SetTheory
end YesMetaZFC
