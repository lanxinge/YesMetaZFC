import YesMetaZFC.SetTheory.Replacement
import YesMetaZFC.SetTheory.SetConstruction

/-!
# 笛卡尔积的模型内部构造

对每个左坐标先用 Replacement 收集整行有序对，再对左集合收集这些行并取并集。整个
构造只依赖给定有序对解释合同，不假定某个具体编码的集合论形状。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Definitional
namespace Project
namespace BinarySchema

/-- 固定左坐标后，把右坐标映到相应有序对编码。 -/
def orderedPairWithLeft
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := 𝒞.code (.bound 0) (.bound 2) (.bound 1)
  freeClosed :=
    𝒞.code_freeClosed _ _ _ rfl rfl rfl

end BinarySchema

namespace Formula

/-- `row` 恰好由固定左坐标与右集合各元素组成的有序对编码构成。 -/
def isCartesianRow (𝒞 : OrderedPairConvention)
    {depth : Nat} (row left right : Term depth) : Formula 1 depth :=
  .forallE <| .iff
    (.mem Term.newest row.weaken) <|
    Formula.existsMem right.weaken <|
      𝒞.code (.bound 1) left.weaken.weaken Term.newest

/-- 固定左坐标的有序对模式按合同解释。 -/
theorem denote_orderedPairWithLeft_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (right pair : ℳ.Domain) :
    (Definitional.Project.BinarySchema.orderedPairWithLeft 𝒞).denote
        env right pair ↔
      𝕀.Codes pair (env.bound 0) right := by
  simp [Definitional.Project.BinarySchema.orderedPairWithLeft,
    Definitional.Project.BinarySchema.denote,
    𝕀.satisfies_code_iff]
  rfl

/-- 笛卡尔积行公式与纸面逐坐标语义一致。 -/
theorem satisfies_isCartesianRow_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (row left right : Term depth) :
    satisfies env (isCartesianRow 𝒞 row left right) ↔
      ∀ pair, ℳ.mem pair (row.eval env) ↔
        ∃ rightValue, ℳ.mem rightValue (right.eval env) ∧
          𝕀.Codes pair (left.eval env) rightValue := by
  simp only [isCartesianRow, satisfies_forall_iff,
    satisfies_iff_iff, satisfies_mem_iff,
    satisfies_existsMem_iff, 𝕀.satisfies_code_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

end Formula

namespace BinarySchema

/-- 固定右集合后，把每个左坐标映到其笛卡尔积行。 -/
def cartesianRow
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := Definitional.Project.Formula.isCartesianRow 𝒞
    (.bound 0) (.bound 1) (.bound 2)
  freeClosed := by
    simp [Definitional.Project.Formula.isCartesianRow,
      Definitional.Project.Formula.existsMem,
      Definitional.Formula.FreeClosed, Definitional.Term.newest]

end BinarySchema

namespace Formula

/-- 笛卡尔积行模式的 schema 解释。 -/
theorem denote_cartesianRow_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (left row : ℳ.Domain) :
    (Definitional.Project.BinarySchema.cartesianRow 𝒞).denote env left row ↔
      ∀ pair, ℳ.mem pair row ↔
        ∃ rightValue, ℳ.mem rightValue (env.bound 0) ∧
          𝕀.Codes pair left rightValue := by
  simpa [Definitional.Project.BinarySchema.cartesianRow,
    Definitional.Project.BinarySchema.denote,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push] using
      satisfies_isCartesianRow_iff 𝕀
        ((env.push left).push row)
        (.bound 0) (.bound 1) (.bound 2)

end Formula
end Project
end Definitional

namespace ZF

/-- 固定左坐标与右集合时，模型内部存在对应的笛卡尔积行。 -/
theorem exists_cartesianRow
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left right : ℳ.Domain) :
    ∃ row, ∀ pair, ℳ.mem pair row ↔
      ∃ rightValue, ℳ.mem rightValue right ∧
        𝕀.Codes pair left rightValue := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_functionalImageOn hZF
      (Definitional.Project.BinarySchema.orderedPairWithLeft 𝒞) env right
      (by
        intro rightValue _
        rcases 𝕀.total left rightValue with ⟨pair, hCode⟩
        exact ⟨pair,
          (Definitional.Project.Formula.denote_orderedPairWithLeft_iff
            𝕀 env rightValue pair).mpr hCode⟩)
      (by
        intro rightValue _ first second hFirst hSecond
        rw [Definitional.Project.Formula.denote_orderedPairWithLeft_iff 𝕀]
          at hFirst hSecond
        exact 𝕀.unique hFirst hSecond) with
    ⟨row, hRow⟩
  refine ⟨row, fun pair => ?_⟩
  rw [hRow pair]
  constructor
  · rintro ⟨rightValue, hRightValue, hPair⟩
    exact ⟨rightValue, hRightValue,
      (Definitional.Project.Formula.denote_orderedPairWithLeft_iff
        𝕀 env rightValue pair).mp hPair⟩
  · rintro ⟨rightValue, hRightValue, hCode⟩
    exact ⟨rightValue, hRightValue,
      (Definitional.Project.Formula.denote_orderedPairWithLeft_iff
        𝕀 env rightValue pair).mpr hCode⟩

/-- ZF 模型中任意两个集合都有按给定合同编码的笛卡尔积。 -/
theorem exists_cartesianProduct
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left right : ℳ.Domain) :
    ∃ product, ℳ.IsCartesianProduct 𝕀 product left right := by
  let env : Env ℳ 1 := {
    bound := fun _ => right
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hTotal :
      ∀ leftValue, ℳ.mem leftValue left →
        ∃ row, (Definitional.Project.BinarySchema.cartesianRow 𝒞).denote
          env leftValue row := by
    intro leftValue _
    rcases exists_cartesianRow hZF 𝕀 leftValue right with
      ⟨row, hRow⟩
    exact ⟨row,
      (Definitional.Project.Formula.denote_cartesianRow_iff
        𝕀 env leftValue row).mpr hRow⟩
  have hUnique :
      ∀ leftValue, ℳ.mem leftValue left → ∀ first second,
        (Definitional.Project.BinarySchema.cartesianRow 𝒞).denote
          env leftValue first →
        (Definitional.Project.BinarySchema.cartesianRow 𝒞).denote
          env leftValue second →
        first = second := by
    intro leftValue _ first second hFirst hSecond
    apply hZF.1.eq_of_same_members
    intro pair
    rw [(Definitional.Project.Formula.denote_cartesianRow_iff
      𝕀 env leftValue first).mp hFirst pair]
    rw [(Definitional.Project.Formula.denote_cartesianRow_iff
      𝕀 env leftValue second).mp hSecond pair]
  rcases exists_functionalImageOn hZF
      (Definitional.Project.BinarySchema.cartesianRow 𝒞)
      env left hTotal hUnique with
    ⟨rows, hRows⟩
  rcases KP.exists_union (modelsKP hZF) rows with
    ⟨product, hProduct⟩
  refine ⟨product, fun pair => ?_⟩
  rw [hProduct pair]
  constructor
  · rintro ⟨row, hRowMem, hPairRow⟩
    rcases (hRows row).mp hRowMem with
      ⟨leftValue, hLeftValue, hRow⟩
    rcases
        ((Definitional.Project.Formula.denote_cartesianRow_iff
          𝕀 env leftValue row).mp hRow pair).mp hPairRow with
      ⟨rightValue, hRightValue, hCode⟩
    exact ⟨leftValue, hLeftValue,
      rightValue, hRightValue, hCode⟩
  · rintro ⟨leftValue, hLeftValue,
      rightValue, hRightValue, hCode⟩
    rcases hTotal leftValue hLeftValue with ⟨row, hRow⟩
    refine ⟨row, (hRows row).mpr
      ⟨leftValue, hLeftValue, hRow⟩, ?_⟩
    exact ((Definitional.Project.Formula.denote_cartesianRow_iff
      𝕀 env leftValue row).mp hRow pair).mpr
        ⟨rightValue, hRightValue, hCode⟩

end ZF

namespace Structure.IsCartesianProduct

/-- 右坐标是二元并时，笛卡尔积相应分解为两个笛卡尔积之并。 -/
theorem union_right
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {product leftProduct rightProduct
      left rightUnion rightLeft rightRight : ℳ.Domain}
    (hProduct :
      ℳ.IsCartesianProduct 𝕀 product left rightUnion)
    (hLeftProduct :
      ℳ.IsCartesianProduct 𝕀 leftProduct left rightLeft)
    (hRightProduct :
      ℳ.IsCartesianProduct 𝕀 rightProduct left rightRight)
    (hRightUnion :
      ℳ.IsUnionOfTwo rightUnion rightLeft rightRight) :
    ℳ.IsUnionOfTwo product leftProduct rightProduct := by
  intro pair
  constructor
  · intro hPair
    rcases (hProduct pair).mp hPair with
      ⟨leftValue, hLeftValue,
        rightValue, hRightValue, hCode⟩
    rcases (hRightUnion rightValue).mp hRightValue with
      hRightLeft | hRightRight
    · exact Or.inl <| (hLeftProduct pair).mpr
        ⟨leftValue, hLeftValue,
          rightValue, hRightLeft, hCode⟩
    · exact Or.inr <| (hRightProduct pair).mpr
        ⟨leftValue, hLeftValue,
          rightValue, hRightRight, hCode⟩
  · intro hPair
    rcases hPair with hLeftPair | hRightPair
    · rcases (hLeftProduct pair).mp hLeftPair with
        ⟨leftValue, hLeftValue,
          rightValue, hRightValue, hCode⟩
      exact (hProduct pair).mpr
        ⟨leftValue, hLeftValue,
          rightValue,
          (hRightUnion rightValue).mpr <| Or.inl hRightValue,
          hCode⟩
    · rcases (hRightProduct pair).mp hRightPair with
        ⟨leftValue, hLeftValue,
          rightValue, hRightValue, hCode⟩
      exact (hProduct pair).mpr
        ⟨leftValue, hLeftValue,
          rightValue,
          (hRightUnion rightValue).mpr <| Or.inr hRightValue,
          hCode⟩

/-- 右坐标集合不交时，相应的两个笛卡尔积也不交。 -/
theorem disjoint_right
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {leftProduct rightProduct left rightLeft rightRight : ℳ.Domain}
    (hLeftProduct :
      ℳ.IsCartesianProduct 𝕀 leftProduct left rightLeft)
    (hRightProduct :
      ℳ.IsCartesianProduct 𝕀 rightProduct left rightRight)
    (hRightDisjoint :
      ℳ.IsDisjoint rightLeft rightRight) :
    ℳ.IsDisjoint leftProduct rightProduct := by
  intro pair hPair
  rcases (hLeftProduct pair).mp hPair.1 with
    ⟨_, _, leftRightValue, hLeftRightValue, hLeftCode⟩
  rcases (hRightProduct pair).mp hPair.2 with
    ⟨_, _, rightRightValue, hRightRightValue, hRightCode⟩
  have hRightEq := (𝕀.injective hLeftCode hRightCode).2
  subst rightRightValue
  exact hRightDisjoint leftRightValue
    ⟨hLeftRightValue, hRightRightValue⟩

end Structure.IsCartesianProduct

end SetTheory
end YesMetaZFC
