import YesMetaZFC.SetTheory.FunctionSpaceConstruction
import YesMetaZFC.SetTheory.TaggedUnionConstruction
import YesMetaZFC.SetTheory.Card.Basic

/-!
# 函数集的代数等势

本层收集基数指数律所需的模型内部函数集双射。所有变换都先由对象语言可定义关系生成
真正的集合编码函数图，再证明这些图在相应函数集之间构成双射。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- 把并定义域上的函数拆成两个限制函数，并编码为有序对。 -/
def IsFunctionDomainSplit {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left right input output : ℳ.Domain) : Prop :=
  ∃ leftFunction rightFunction,
    ℳ.IsRestrictionOf 𝕀 leftFunction input left ∧
      ℳ.IsRestrictionOf 𝕀 rightFunction input right ∧
        𝕀.Codes output leftFunction rightFunction

/-- `function` 是 `input` 的左坐标投影函数。 -/
def IsLeftFunctionProjection {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function input source left : ℳ.Domain) : Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 function source left ∧
    ∀ argument leftValue,
      ℳ.PairMember 𝕀 argument leftValue function ↔
        ∃ productValue rightValue,
          ℳ.PairMember 𝕀 argument productValue input ∧
            𝕀.Codes productValue leftValue rightValue

/-- `function` 是 `input` 的右坐标投影函数。 -/
def IsRightFunctionProjection {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function input source right : ℳ.Domain) : Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 function source right ∧
    ∀ argument rightValue,
      ℳ.PairMember 𝕀 argument rightValue function ↔
        ∃ productValue leftValue,
          ℳ.PairMember 𝕀 argument productValue input ∧
            𝕀.Codes productValue leftValue rightValue

/-- 把函数的左右坐标投影编码为一个有序对。 -/
def IsFunctionCodomainSplit {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (source left right input output : ℳ.Domain) : Prop :=
  ∃ leftFunction rightFunction,
    ℳ.IsLeftFunctionProjection 𝕀
      leftFunction input source left ∧
    ℳ.IsRightFunctionProjection 𝕀
      rightFunction input source right ∧
    𝕀.Codes output leftFunction rightFunction

/-- `sectionFunction` 是平坦函数在固定右坐标处的截面函数。 -/
def IsFunctionSection {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sectionFunction flat left base rightValue : ℳ.Domain) : Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 sectionFunction left base ∧
    ∀ leftValue output,
      ℳ.PairMember 𝕀 leftValue output sectionFunction ↔
        ∃ productValue,
          𝕀.Codes productValue leftValue rightValue ∧
            ℳ.PairMember 𝕀 productValue output flat

/-- `output` 是嵌套函数 `input` 的展平函数。 -/
def IsFunctionUncurrying {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (input output product base : ℳ.Domain) : Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 output product base ∧
    ∀ productValue value,
      ℳ.PairMember 𝕀 productValue value output ↔
        ∃ leftValue rightValue innerFunction,
          𝕀.Codes productValue leftValue rightValue ∧
            ℳ.PairMember 𝕀 rightValue innerFunction input ∧
              ℳ.PairMember 𝕀 leftValue value innerFunction

end Structure

namespace Definitional
namespace Project

namespace BinarySchema

/-- 并定义域函数拆分的值关系。 -/
def splitFunctionDomainValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .existsE <|
    .conj
      (Formula.isRestriction 𝒞
        (.bound 1) (.bound 3) (.bound 4)) <|
    .conj
      (Formula.isRestriction 𝒞
        (.bound 0) (.bound 3) (.bound 5))
      (𝒞.code (.bound 2) (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isRestriction, Formula.isRelation,
      Formula.forallMem, Formula.orderedPairMem,
      Formula.FreeClosed, Term.newest]

/-- 从取值于笛卡尔积的函数中读取左坐标。 -/
def leftFunctionProjectionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := .existsE <| .existsE <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 3) (.bound 1) (.bound 4))
      (𝒞.code (.bound 1) (.bound 2) (.bound 0))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 从取值于笛卡尔积的函数中读取右坐标。 -/
def rightFunctionProjectionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := .existsE <| .existsE <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 3) (.bound 1) (.bound 4))
      (𝒞.code (.bound 1) (.bound 0) (.bound 2))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 逐点合并两个函数的值为笛卡尔积编码。 -/
def combineFunctionCoordinatesValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .existsE <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 3) (.bound 1) (.bound 4)) <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 3) (.bound 0) (.bound 5))
      (𝒞.code (.bound 2) (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 从嵌套函数读取展平后的单点值。 -/
def uncurriedFunctionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := .existsE <| .existsE <| .existsE <|
    .conj
      (𝒞.code (.bound 4) (.bound 2) (.bound 1)) <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 1) (.bound 0) (.bound 5))
      (Formula.orderedPairMem 𝒞
        (.bound 2) (.bound 3) (.bound 0))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 从平坦函数读取固定右坐标截面上的单点值。 -/
def functionSectionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj
    (𝒞.code (.bound 0) (.bound 2) (.bound 4))
    (Formula.orderedPairMem 𝒞
      (.bound 0) (.bound 1) (.bound 3))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

end BinarySchema

namespace Formula

/-- 左坐标投影函数的对象语言刻画。 -/
def isLeftFunctionProjection
    (𝒞 : OrderedPairConvention) {depth : Nat}
    (function input source left : Term depth) : Formula 1 depth :=
  .conj (isFunctionFromTo 𝒞 function source left) <|
    .forallE <| .forallE <| .iff
      (orderedPairMem 𝒞
        (.bound 1) (.bound 0) function.weaken.weaken) <|
      .existsE <| .existsE <| .conj
        (orderedPairMem 𝒞
          (.bound 3) (.bound 1) input.weaken.weaken.weaken.weaken)
        (𝒞.code (.bound 1) (.bound 2) (.bound 0))

/-- 右坐标投影函数的对象语言刻画。 -/
def isRightFunctionProjection
    (𝒞 : OrderedPairConvention) {depth : Nat}
    (function input source right : Term depth) : Formula 1 depth :=
  .conj (isFunctionFromTo 𝒞 function source right) <|
    .forallE <| .forallE <| .iff
      (orderedPairMem 𝒞
        (.bound 1) (.bound 0) function.weaken.weaken) <|
      .existsE <| .existsE <| .conj
        (orderedPairMem 𝒞
          (.bound 3) (.bound 1) input.weaken.weaken.weaken.weaken)
        (𝒞.code (.bound 1) (.bound 0) (.bound 2))

/-- 平坦函数在固定右坐标处的截面函数公式。 -/
def isFunctionSection
    (𝒞 : OrderedPairConvention) {depth : Nat}
    (sectionFunction flat left base rightValue : Term depth) : Formula 1 depth :=
  .conj (isFunctionFromTo 𝒞 sectionFunction left base) <|
    .forallE <| .forallE <| .iff
      (orderedPairMem 𝒞
        (.bound 1) (.bound 0) sectionFunction.weaken.weaken) <|
      .existsE <| .conj
        (𝒞.code (.bound 0) (.bound 2) rightValue.weaken.weaken.weaken)
        (orderedPairMem 𝒞
          (.bound 0) (.bound 1) flat.weaken.weaken.weaken)

/-- 嵌套函数展平公式。 -/
def isFunctionUncurrying
    (𝒞 : OrderedPairConvention) {depth : Nat}
    (input output product base : Term depth) : Formula 1 depth :=
  .conj (isFunctionFromTo 𝒞 output product base) <|
    .forallE <| .forallE <| .iff
      (orderedPairMem 𝒞
        (.bound 1) (.bound 0) output.weaken.weaken) <|
      .existsE <| .existsE <| .existsE <|
        .conj
          (𝒞.code (.bound 4) (.bound 2) (.bound 1)) <|
        .conj
          (orderedPairMem 𝒞
            (.bound 1) (.bound 0) input.weaken.weaken.weaken.weaken.weaken)
          (orderedPairMem 𝒞
            (.bound 2) (.bound 3) (.bound 0))

end Formula

namespace BinarySchema

/-- 把左右投影函数编码为输出有序对。 -/
def splitFunctionCodomainValue
    (𝒞 : OrderedPairConvention) : BinarySchema 3 where
  body := .existsE <| .existsE <|
    .conj
      (Formula.isLeftFunctionProjection 𝒞
        (.bound 1) (.bound 3) (.bound 4) (.bound 5)) <|
    .conj
      (Formula.isRightFunctionProjection 𝒞
        (.bound 0) (.bound 3) (.bound 4) (.bound 6))
      (𝒞.code (.bound 2) (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isLeftFunctionProjection,
      Formula.isRightFunctionProjection,
      Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.forallMem, Formula.existsMem,
      Formula.orderedPairMem, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]

/-- 固定平坦函数后，把右坐标映到相应截面函数。 -/
def functionSection
    (𝒞 : OrderedPairConvention) : BinarySchema 3 where
  body := Formula.isFunctionSection 𝒞
    (.bound 0) (.bound 2) (.bound 3) (.bound 4) (.bound 1)
  freeClosed := by
    simp [Formula.isFunctionSection,
      Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.forallMem, Formula.existsMem,
      Formula.orderedPairMem, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]

/-- 把嵌套函数整体展平。 -/
def uncurryFunctionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := Formula.isFunctionUncurrying 𝒞
    (.bound 1) (.bound 0) (.bound 2) (.bound 3)
  freeClosed := by
    simp [Formula.isFunctionUncurrying,
      Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.forallMem, Formula.existsMem,
      Formula.orderedPairMem, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]

end BinarySchema

namespace Formula

/-- 左坐标投影值关系的纸面解释。 -/
theorem denote_leftFunctionProjectionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (argument output : ℳ.Domain) :
    (BinarySchema.leftFunctionProjectionValue 𝒞).denote
        env argument output ↔
      ∃ productValue rightValue,
        ℳ.PairMember 𝕀 argument productValue (env.bound 0) ∧
          𝕀.Codes productValue output rightValue := by
  simp only [BinarySchema.leftFunctionProjectionValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push]
  rfl

/-- 右坐标投影值关系的纸面解释。 -/
theorem denote_rightFunctionProjectionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (argument output : ℳ.Domain) :
    (BinarySchema.rightFunctionProjectionValue 𝒞).denote
        env argument output ↔
      ∃ productValue leftValue,
        ℳ.PairMember 𝕀 argument productValue (env.bound 0) ∧
          𝕀.Codes productValue leftValue output := by
  simp only [BinarySchema.rightFunctionProjectionValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push]
  rfl

/-- 逐点合并值关系的纸面解释。 -/
theorem denote_combineFunctionCoordinatesValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (argument output : ℳ.Domain) :
    (BinarySchema.combineFunctionCoordinatesValue 𝒞).denote
        env argument output ↔
      ∃ leftValue rightValue,
        ℳ.PairMember 𝕀 argument leftValue (env.bound 0) ∧
        ℳ.PairMember 𝕀 argument rightValue (env.bound 1) ∧
        𝕀.Codes output leftValue rightValue := by
  simp only [BinarySchema.combineFunctionCoordinatesValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl

/-- 展平单点值关系的纸面解释。 -/
theorem denote_uncurriedFunctionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (productValue output : ℳ.Domain) :
    (BinarySchema.uncurriedFunctionValue 𝒞).denote
        env productValue output ↔
      ∃ leftValue rightValue innerFunction,
        𝕀.Codes productValue leftValue rightValue ∧
          ℳ.PairMember 𝕀 rightValue innerFunction (env.bound 0) ∧
            ℳ.PairMember 𝕀 leftValue output innerFunction := by
  simp only [BinarySchema.uncurriedFunctionValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl

/-- 截面单点值关系的纸面解释。 -/
theorem denote_functionSectionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (leftValue output : ℳ.Domain) :
    (BinarySchema.functionSectionValue 𝒞).denote
        env leftValue output ↔
      ∃ productValue,
        𝕀.Codes productValue leftValue (env.bound 1) ∧
          ℳ.PairMember 𝕀 productValue output (env.bound 0) := by
  simp only [BinarySchema.functionSectionValue,
    BinarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push]
  rfl

/-- 截面函数公式与纸面语义一致。 -/
theorem satisfies_isFunctionSection_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sectionFunction flat left base rightValue : Term depth) :
    satisfies env
        (isFunctionSection 𝒞 sectionFunction flat left base rightValue) ↔
      ℳ.IsFunctionSection 𝕀
        (sectionFunction.eval env) (flat.eval env)
        (left.eval env) (base.eval env) (rightValue.eval env) := by
  simp only [isFunctionSection, Structure.IsFunctionSection,
    satisfies_conj_iff, satisfies_forall_iff,
    satisfies_iff_iff, satisfies_exists_iff,
    satisfies_isFunctionFromTo_iff 𝕀 hExt,
    satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 展平函数公式与纸面语义一致。 -/
theorem satisfies_isFunctionUncurrying_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (input output product base : Term depth) :
    satisfies env
        (isFunctionUncurrying 𝒞 input output product base) ↔
      ℳ.IsFunctionUncurrying 𝕀
        (input.eval env) (output.eval env)
        (product.eval env) (base.eval env) := by
  simp only [isFunctionUncurrying, Structure.IsFunctionUncurrying,
    satisfies_conj_iff, satisfies_forall_iff,
    satisfies_iff_iff, satisfies_exists_iff,
    satisfies_isFunctionFromTo_iff 𝕀 hExt,
    satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 截面函数 schema 的纸面解释。 -/
theorem denote_functionSection_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 3) (rightValue sectionFunction : ℳ.Domain) :
    (BinarySchema.functionSection 𝒞).denote
        env rightValue sectionFunction ↔
      ℳ.IsFunctionSection 𝕀
        sectionFunction (env.bound 0) (env.bound 1)
        (env.bound 2) rightValue := by
  simpa [BinarySchema.functionSection, BinarySchema.denote,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push] using
      satisfies_isFunctionSection_iff 𝕀 hExt
        ((env.push rightValue).push sectionFunction)
        (.bound 0) (.bound 2) (.bound 3) (.bound 4) (.bound 1)

/-- 整体展平 schema 的纸面解释。 -/
theorem denote_uncurryFunctionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.uncurryFunctionValue 𝒞).denote
        env input output ↔
      ℳ.IsFunctionUncurrying 𝕀
        input output (env.bound 0) (env.bound 1) := by
  simpa [BinarySchema.uncurryFunctionValue, BinarySchema.denote,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push] using
      satisfies_isFunctionUncurrying_iff 𝕀 hExt
        ((env.push input).push output)
        (.bound 1) (.bound 0) (.bound 2) (.bound 3)

/-- 左坐标投影公式与纸面语义一致。 -/
theorem satisfies_isLeftFunctionProjection_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function input source left : Term depth) :
    satisfies env
        (isLeftFunctionProjection 𝒞 function input source left) ↔
      ℳ.IsLeftFunctionProjection 𝕀
        (function.eval env) (input.eval env)
        (source.eval env) (left.eval env) := by
  simp only [isLeftFunctionProjection,
    Structure.IsLeftFunctionProjection, satisfies_conj_iff,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_exists_iff,
    satisfies_isFunctionFromTo_iff 𝕀 hExt,
    satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 右坐标投影公式与纸面语义一致。 -/
theorem satisfies_isRightFunctionProjection_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function input source right : Term depth) :
    satisfies env
        (isRightFunctionProjection 𝒞 function input source right) ↔
      ℳ.IsRightFunctionProjection 𝕀
        (function.eval env) (input.eval env)
        (source.eval env) (right.eval env) := by
  simp only [isRightFunctionProjection,
    Structure.IsRightFunctionProjection, satisfies_conj_iff,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_exists_iff,
    satisfies_isFunctionFromTo_iff 𝕀 hExt,
    satisfies_orderedPairMem_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 值域拆分模式的纸面解释。 -/
theorem denote_splitFunctionCodomainValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 3) (input output : ℳ.Domain) :
    (BinarySchema.splitFunctionCodomainValue 𝒞).denote
        env input output ↔
      ℳ.IsFunctionCodomainSplit 𝕀
        (env.bound 0) (env.bound 1) (env.bound 2)
        input output := by
  simp only [BinarySchema.splitFunctionCodomainValue,
    BinarySchema.denote, Structure.IsFunctionCodomainSplit,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    satisfies_isLeftFunctionProjection_iff 𝕀 hExt,
    satisfies_isRightFunctionProjection_iff 𝕀 hExt,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push]
  rfl

/-- 并定义域函数拆分模式的纸面解释。 -/
theorem denote_splitFunctionDomainValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (input output : ℳ.Domain) :
    (BinarySchema.splitFunctionDomainValue 𝒞).denote
        env input output ↔
      ℳ.IsFunctionDomainSplit 𝕀
        (env.bound 0) (env.bound 1) input output := by
  simp only [BinarySchema.splitFunctionDomainValue,
    BinarySchema.denote, Structure.IsFunctionDomainSplit,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isRestriction_iff 𝕀,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl

end Formula

end Project
end Definitional

namespace ZF

/--
以函数集为值域的嵌套函数集，与笛卡尔积定义域上的平坦函数集等势。
-/
theorem equinumerous_nestedFunctionSpace
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {innerSpace sourceSpace targetSpace
      left right product base : ℳ.Domain}
    (hInnerSpace :
      ℳ.IsFunctionSpace 𝕀 innerSpace left base)
    (hSourceSpace :
      ℳ.IsFunctionSpace 𝕀 sourceSpace right innerSpace)
    (hProduct :
      ℳ.IsCartesianProduct 𝕀 product left right)
    (hTargetSpace :
      ℳ.IsFunctionSpace 𝕀 targetSpace product base) :
    ℳ.Equinumerous 𝕀 sourceSpace targetSpace := by
  let env : Env ℳ 2 := {
    bound := Fin.cases product <| Fin.cases base Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.uncurryFunctionValue 𝒞) env
  · intro input hInput
    have hInputFunction := (hSourceSpace input).mp hInput
    let inputEnv : Env ℳ 1 := {
      bound := fun _ => input
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 (Definitional.Project.BinarySchema.uncurriedFunctionValue 𝒞)
        inputEnv
        (source := product) (target := base)
        (by
          intro productValue hProductValue
          rcases (hProduct productValue).mp hProductValue with
            ⟨leftValue, hLeftValue,
              rightValue, hRightValue, hCode⟩
          rcases hInputFunction.2.2 rightValue hRightValue with
            ⟨innerFunction, hInnerFunctionMem, hInputPair⟩
          have hInnerFunction :=
            (hInnerSpace innerFunction).mp hInnerFunctionMem
          rcases hInnerFunction.2.2 leftValue hLeftValue with
            ⟨output, _, hInnerPair⟩
          exact ⟨output,
            (Definitional.Project.Formula.denote_uncurriedFunctionValue_iff
              𝕀 inputEnv productValue output).mpr
                ⟨leftValue, rightValue, innerFunction,
                  hCode, hInputPair, hInnerPair⟩⟩)
        (by
          intro productValue _ first second hFirst hSecond
          rw [Definitional.Project.Formula.denote_uncurriedFunctionValue_iff 𝕀]
            at hFirst hSecond
          rcases hFirst with
            ⟨firstLeft, firstRight, firstInner,
              hFirstCode, hFirstOuter, hFirstInner⟩
          rcases hSecond with
            ⟨secondLeft, secondRight, secondInner,
              hSecondCode, hSecondOuter, hSecondInner⟩
          rcases 𝕀.injective hFirstCode hSecondCode with
            ⟨hLeftEq, hRightEq⟩
          subst secondLeft
          subst secondRight
          have hInnerEq :=
            hInputFunction.1.2 firstRight firstInner secondInner
              hFirstOuter hSecondOuter
          subst secondInner
          have hInnerFunctionMem :=
            hInputFunction.output_mem_of_pairMember hFirstOuter
          have hInnerFunction :=
            (hInnerSpace firstInner).mp hInnerFunctionMem
          exact hInnerFunction.1.2 firstLeft first second
            hFirstInner hSecondInner)
        (by
          intro _ output _ hValue
          rw [Definitional.Project.Formula.denote_uncurriedFunctionValue_iff 𝕀]
            at hValue
          rcases hValue with
            ⟨_, _, innerFunction, _, hOuterPair, hInnerPair⟩
          have hInnerFunctionMem :=
            hInputFunction.output_mem_of_pairMember hOuterPair
          exact (hInnerSpace innerFunction).mp hInnerFunctionMem
            |>.output_mem_of_pairMember hInnerPair) with
      ⟨output, hOutputFunction, hOutputPairs⟩
    have hUncurrying :
        ℳ.IsFunctionUncurrying 𝕀 input output product base := by
      refine ⟨hOutputFunction, fun productValue value => ?_⟩
      rw [hOutputPairs productValue value,
        Definitional.Project.Formula.denote_uncurriedFunctionValue_iff 𝕀]
      constructor
      · exact fun h => h.2
      · rintro ⟨leftValue, rightValue, innerFunction,
          hCode, hOuterPair, hInnerPair⟩
        have hRightValue :=
          hInputFunction.input_mem_of_pairMember hOuterPair
        have hInnerFunctionMem :=
          hInputFunction.output_mem_of_pairMember hOuterPair
        have hLeftValue :=
          (hInnerSpace innerFunction).mp hInnerFunctionMem
            |>.input_mem_of_pairMember hInnerPair
        exact ⟨(hProduct productValue).mpr
            ⟨leftValue, hLeftValue,
              rightValue, hRightValue, hCode⟩,
          leftValue, rightValue, innerFunction,
          hCode, hOuterPair, hInnerPair⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_uncurryFunctionValue_iff
        𝕀 hZF.1 env input output).mpr hUncurrying⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_uncurryFunctionValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirst.1.1.1 hSecond.1.1.1
    intro productValue value
    rw [hFirst.2 productValue value, hSecond.2 productValue value]
  · intro _ output _ hValue
    rw [Definitional.Project.Formula.denote_uncurryFunctionValue_iff 𝕀 hZF.1]
      at hValue
    exact (hTargetSpace output).mpr hValue.1
  · intro first second output hFirstMem hSecondMem hFirst hSecond
    rw [Definitional.Project.Formula.denote_uncurryFunctionValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    have hFirstFunction := (hSourceSpace first).mp hFirstMem
    have hSecondFunction := (hSourceSpace second).mp hSecondMem
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirstFunction.1.1 hSecondFunction.1.1
    intro rightValue innerFunction
    constructor
    · intro hFirstPair
      have hRightValue :=
        hFirstFunction.input_mem_of_pairMember hFirstPair
      rcases hSecondFunction.2.2 rightValue hRightValue with
        ⟨secondInner, hSecondInnerMem, hSecondPair⟩
      have hFirstInnerMem :=
        hFirstFunction.output_mem_of_pairMember hFirstPair
      have hFirstInner := (hInnerSpace innerFunction).mp hFirstInnerMem
      have hSecondInner := (hInnerSpace secondInner).mp hSecondInnerMem
      have hInnerEq : innerFunction = secondInner := by
        apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
          hFirstInner.1.1 hSecondInner.1.1
        intro leftValue value
        constructor
        · intro hFirstInnerPair
          rcases 𝕀.total leftValue rightValue with
            ⟨productValue, hProductCode⟩
          have hOutputPair :=
            (hFirst.2 productValue value).mpr
              ⟨leftValue, rightValue, innerFunction,
                hProductCode, hFirstPair, hFirstInnerPair⟩
          rcases (hSecond.2 productValue value).mp hOutputPair with
            ⟨selectedLeft, selectedRight, selectedInner,
              hSelectedCode, hSelectedOuter, hSelectedInner⟩
          rcases 𝕀.injective hProductCode hSelectedCode with
            ⟨hLeftEq, hRightEq⟩
          subst selectedLeft
          subst selectedRight
          have hSelectedInnerEq :=
            hSecondFunction.1.2 rightValue selectedInner secondInner
              hSelectedOuter hSecondPair
          subst selectedInner
          exact hSelectedInner
        · intro hSecondInnerPair
          rcases 𝕀.total leftValue rightValue with
            ⟨productValue, hProductCode⟩
          have hOutputPair :=
            (hSecond.2 productValue value).mpr
              ⟨leftValue, rightValue, secondInner,
                hProductCode, hSecondPair, hSecondInnerPair⟩
          rcases (hFirst.2 productValue value).mp hOutputPair with
            ⟨selectedLeft, selectedRight, selectedInner,
              hSelectedCode, hSelectedOuter, hSelectedInner⟩
          rcases 𝕀.injective hProductCode hSelectedCode with
            ⟨hLeftEq, hRightEq⟩
          subst selectedLeft
          subst selectedRight
          have hSelectedInnerEq :=
            hFirstFunction.1.2 rightValue selectedInner innerFunction
              hSelectedOuter hFirstPair
          subst selectedInner
          exact hSelectedInner
      simpa [hInnerEq] using hSecondPair
    · intro hSecondPair
      have hRightValue :=
        hSecondFunction.input_mem_of_pairMember hSecondPair
      rcases hFirstFunction.2.2 rightValue hRightValue with
        ⟨firstInner, hFirstInnerMem, hFirstPair⟩
      have hSecondInnerMem :=
        hSecondFunction.output_mem_of_pairMember hSecondPair
      have hFirstInner := (hInnerSpace firstInner).mp hFirstInnerMem
      have hSecondInner := (hInnerSpace innerFunction).mp hSecondInnerMem
      have hInnerEq : firstInner = innerFunction := by
        apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
          hFirstInner.1.1 hSecondInner.1.1
        intro leftValue value
        constructor
        · intro hFirstInnerPair
          rcases 𝕀.total leftValue rightValue with
            ⟨productValue, hProductCode⟩
          have hOutputPair :=
            (hFirst.2 productValue value).mpr
              ⟨leftValue, rightValue, firstInner,
                hProductCode, hFirstPair, hFirstInnerPair⟩
          rcases (hSecond.2 productValue value).mp hOutputPair with
            ⟨selectedLeft, selectedRight, selectedInner,
              hSelectedCode, hSelectedOuter, hSelectedInner⟩
          rcases 𝕀.injective hProductCode hSelectedCode with
            ⟨hLeftEq, hRightEq⟩
          subst selectedLeft
          subst selectedRight
          have hSelectedInnerEq :=
            hSecondFunction.1.2 rightValue selectedInner innerFunction
              hSelectedOuter hSecondPair
          subst selectedInner
          exact hSelectedInner
        · intro hSecondInnerPair
          rcases 𝕀.total leftValue rightValue with
            ⟨productValue, hProductCode⟩
          have hOutputPair :=
            (hSecond.2 productValue value).mpr
              ⟨leftValue, rightValue, innerFunction,
                hProductCode, hSecondPair, hSecondInnerPair⟩
          rcases (hFirst.2 productValue value).mp hOutputPair with
            ⟨selectedLeft, selectedRight, selectedInner,
              hSelectedCode, hSelectedOuter, hSelectedInner⟩
          rcases 𝕀.injective hProductCode hSelectedCode with
            ⟨hLeftEq, hRightEq⟩
          subst selectedLeft
          subst selectedRight
          have hSelectedInnerEq :=
            hFirstFunction.1.2 rightValue selectedInner firstInner
              hSelectedOuter hFirstPair
          subst selectedInner
          exact hSelectedInner
      simpa [hInnerEq] using hFirstPair
  · intro output hOutput
    have hOutputFunction := (hTargetSpace output).mp hOutput
    let sectionEnv : Env ℳ 3 := {
      bound := Fin.cases output <|
        Fin.cases left <| Fin.cases base Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 (Definitional.Project.BinarySchema.functionSection 𝒞)
        sectionEnv
        (source := right) (target := innerSpace)
        (by
          intro rightValue hRightValue
          let valueEnv : Env ℳ 2 := {
            bound := Fin.cases output <|
              Fin.cases rightValue Fin.elim0
            free := fun _ => Classical.choice ℳ.nonempty
          }
          rcases exists_setFunctionFromTo_of_denote
              hZF 𝕀 (Definitional.Project.BinarySchema.functionSectionValue 𝒞)
              valueEnv
              (source := left) (target := base)
              (by
                intro leftValue hLeftValue
                rcases 𝕀.total leftValue rightValue with
                  ⟨productValue, hCode⟩
                have hProductValue := (hProduct productValue).mpr
                  ⟨leftValue, hLeftValue,
                    rightValue, hRightValue, hCode⟩
                rcases hOutputFunction.2.2 productValue hProductValue with
                  ⟨value, _, hOutputPair⟩
                exact ⟨value,
                  (Definitional.Project.Formula.denote_functionSectionValue_iff
                    𝕀 valueEnv leftValue value).mpr
                      ⟨productValue, hCode, hOutputPair⟩⟩)
              (by
                intro leftValue _ firstValue secondValue hFirst hSecond
                rw [Definitional.Project.Formula.denote_functionSectionValue_iff 𝕀]
                  at hFirst hSecond
                rcases hFirst with
                  ⟨firstProduct, hFirstCode, hFirstPair⟩
                rcases hSecond with
                  ⟨secondProduct, hSecondCode, hSecondPair⟩
                have hProductEq := 𝕀.unique hFirstCode hSecondCode
                subst secondProduct
                exact hOutputFunction.1.2 firstProduct firstValue secondValue
                  hFirstPair hSecondPair)
              (by
                intro _ value _ hValue
                rw [Definitional.Project.Formula.denote_functionSectionValue_iff 𝕀]
                  at hValue
                rcases hValue with ⟨_, _, hPair⟩
                exact hOutputFunction.output_mem_of_pairMember hPair) with
            ⟨sectionFunction, hSectionFunction, hSectionPairs⟩
          have hSection :
              ℳ.IsFunctionSection 𝕀
                sectionFunction output left base rightValue := by
            refine ⟨hSectionFunction, fun leftValue value => ?_⟩
            rw [hSectionPairs leftValue value,
              Definitional.Project.Formula.denote_functionSectionValue_iff 𝕀]
            constructor
            · exact fun h => h.2
            · rintro ⟨productValue, hCode, hPair⟩
              rcases (hProduct productValue).mp <|
                  hOutputFunction.input_mem_of_pairMember hPair with
                ⟨selectedLeft, hSelectedLeft,
                  selectedRight, _, hSelectedCode⟩
              have hLeftEq :=
                (𝕀.injective hCode hSelectedCode).1
              subst selectedLeft
              exact ⟨hSelectedLeft, productValue, hCode, hPair⟩
          exact ⟨sectionFunction,
            (Definitional.Project.Formula.denote_functionSection_iff
              𝕀 hZF.1 sectionEnv rightValue sectionFunction).mpr hSection⟩)
        (by
          intro rightValue _ firstSection secondSection hFirst hSecond
          rw [Definitional.Project.Formula.denote_functionSection_iff 𝕀 hZF.1]
            at hFirst hSecond
          apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
            hFirst.1.1.1 hSecond.1.1.1
          intro leftValue value
          rw [hFirst.2 leftValue value, hSecond.2 leftValue value])
        (by
          intro _ sectionFunction _ hValue
          rw [Definitional.Project.Formula.denote_functionSection_iff 𝕀 hZF.1]
            at hValue
          exact (hInnerSpace sectionFunction).mpr hValue.1) with
      ⟨input, hInputFunction, hInputPairs⟩
    have hInputMem := (hSourceSpace input).mpr hInputFunction
    have hUncurrying :
        ℳ.IsFunctionUncurrying 𝕀 input output product base := by
      refine ⟨hOutputFunction, fun productValue value => ?_⟩
      constructor
      · intro hOutputPair
        have hProductValue :=
          hOutputFunction.input_mem_of_pairMember hOutputPair
        rcases (hProduct productValue).mp hProductValue with
          ⟨leftValue, hLeftValue,
            rightValue, hRightValue, hCode⟩
        rcases hInputFunction.2.2 rightValue hRightValue with
          ⟨sectionFunction, hSectionMem, hInputPair⟩
        have hSection := (hInnerSpace sectionFunction).mp hSectionMem
        have hSectionDefinition :=
          (hInputPairs rightValue sectionFunction).mp hInputPair |>.2
        rw [Definitional.Project.Formula.denote_functionSection_iff 𝕀 hZF.1]
          at hSectionDefinition
        have hSectionPair :=
          (hSectionDefinition.2 leftValue value).mpr
            ⟨productValue, hCode, hOutputPair⟩
        exact ⟨leftValue, rightValue, sectionFunction,
          hCode, hInputPair, hSectionPair⟩
      · rintro ⟨leftValue, rightValue, sectionFunction,
          hCode, hInputPair, hSectionPair⟩
        have hSectionDefinition :=
          (hInputPairs rightValue sectionFunction).mp hInputPair |>.2
        rw [Definitional.Project.Formula.denote_functionSection_iff 𝕀 hZF.1]
          at hSectionDefinition
        rcases (hSectionDefinition.2 leftValue value).mp hSectionPair with
          ⟨selectedProduct, hSelectedCode, hOutputPair⟩
        have hProductEq := 𝕀.unique hCode hSelectedCode
        simpa [hProductEq] using hOutputPair
    exact ⟨input, hInputMem,
      (Definitional.Project.Formula.denote_uncurryFunctionValue_iff
        𝕀 hZF.1 env input output).mpr hUncurrying⟩

/--
取值于笛卡尔积的函数集与两个坐标函数集的笛卡尔积等势。
-/
theorem equinumerous_functionSpaceIntoProduct
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sourceSpace leftSpace rightSpace targetProduct
      source product left right : ℳ.Domain}
    (hSourceSpace :
      ℳ.IsFunctionSpace 𝕀 sourceSpace source product)
    (hLeftSpace :
      ℳ.IsFunctionSpace 𝕀 leftSpace source left)
    (hRightSpace :
      ℳ.IsFunctionSpace 𝕀 rightSpace source right)
    (hTargetProduct :
      ℳ.IsCartesianProduct 𝕀 targetProduct leftSpace rightSpace)
    (hProduct :
      ℳ.IsCartesianProduct 𝕀 product left right) :
    ℳ.Equinumerous 𝕀 sourceSpace targetProduct := by
  let env : Env ℳ 3 := {
    bound := Fin.cases source <|
      Fin.cases left <| Fin.cases right Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.splitFunctionCodomainValue 𝒞) env
  · intro input hInput
    have hInputFunction := (hSourceSpace input).mp hInput
    let inputEnv : Env ℳ 1 := {
      bound := fun _ => input
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 (Definitional.Project.BinarySchema.leftFunctionProjectionValue 𝒞)
        inputEnv
        (source := source) (target := left)
        (by
          intro argument hArgument
          rcases hInputFunction.2.2 argument hArgument with
            ⟨productValue, hProductValue, hInputPair⟩
          rcases (hProduct productValue).mp hProductValue with
            ⟨leftValue, _, rightValue, _, hCode⟩
          exact ⟨leftValue,
            (Definitional.Project.Formula.denote_leftFunctionProjectionValue_iff
              𝕀 inputEnv argument leftValue).mpr
                ⟨productValue, rightValue, hInputPair, hCode⟩⟩)
        (by
          intro argument _ first second hFirst hSecond
          rw [Definitional.Project.Formula.denote_leftFunctionProjectionValue_iff 𝕀]
            at hFirst hSecond
          rcases hFirst with
            ⟨firstProduct, firstRight, hFirstPair, hFirstCode⟩
          rcases hSecond with
            ⟨secondProduct, secondRight, hSecondPair, hSecondCode⟩
          have hProductEq :=
            hInputFunction.1.2 argument firstProduct secondProduct
              hFirstPair hSecondPair
          subst secondProduct
          exact (𝕀.injective hFirstCode hSecondCode).1)
        (by
          intro _ output _ hValue
          rw [Definitional.Project.Formula.denote_leftFunctionProjectionValue_iff 𝕀]
            at hValue
          rcases hValue with ⟨productValue, _, hPair, hCode⟩
          have hProductValue :=
            hInputFunction.output_mem_of_pairMember hPair
          rcases (hProduct productValue).mp hProductValue with
            ⟨leftValue, hLeftValue, rightValue, _, hProductCode⟩
          rcases 𝕀.injective hCode hProductCode with
            ⟨hLeftEq, _⟩
          simpa [hLeftEq] using hLeftValue) with
      ⟨leftFunction, hLeftFunction, hLeftPairs⟩
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 (Definitional.Project.BinarySchema.rightFunctionProjectionValue 𝒞)
        inputEnv
        (source := source) (target := right)
        (by
          intro argument hArgument
          rcases hInputFunction.2.2 argument hArgument with
            ⟨productValue, hProductValue, hInputPair⟩
          rcases (hProduct productValue).mp hProductValue with
            ⟨leftValue, _, rightValue, _, hCode⟩
          exact ⟨rightValue,
            (Definitional.Project.Formula.denote_rightFunctionProjectionValue_iff
              𝕀 inputEnv argument rightValue).mpr
                ⟨productValue, leftValue, hInputPair, hCode⟩⟩)
        (by
          intro argument _ first second hFirst hSecond
          rw [Definitional.Project.Formula.denote_rightFunctionProjectionValue_iff 𝕀]
            at hFirst hSecond
          rcases hFirst with
            ⟨firstProduct, firstLeft, hFirstPair, hFirstCode⟩
          rcases hSecond with
            ⟨secondProduct, secondLeft, hSecondPair, hSecondCode⟩
          have hProductEq :=
            hInputFunction.1.2 argument firstProduct secondProduct
              hFirstPair hSecondPair
          subst secondProduct
          exact (𝕀.injective hFirstCode hSecondCode).2)
        (by
          intro _ output _ hValue
          rw [Definitional.Project.Formula.denote_rightFunctionProjectionValue_iff 𝕀]
            at hValue
          rcases hValue with ⟨productValue, _, hPair, hCode⟩
          have hProductValue :=
            hInputFunction.output_mem_of_pairMember hPair
          rcases (hProduct productValue).mp hProductValue with
            ⟨leftValue, _, rightValue, hRightValue, hProductCode⟩
          rcases 𝕀.injective hCode hProductCode with
            ⟨_, hRightEq⟩
          simpa [hRightEq] using hRightValue) with
      ⟨rightFunction, hRightFunction, hRightPairs⟩
    have hLeftProjection :
        ℳ.IsLeftFunctionProjection 𝕀
          leftFunction input source left := by
      refine ⟨hLeftFunction, fun argument leftValue => ?_⟩
      rw [hLeftPairs argument leftValue,
        Definitional.Project.Formula.denote_leftFunctionProjectionValue_iff 𝕀]
      constructor
      · exact fun h => h.2
      · rintro ⟨productValue, rightValue, hPair, hCode⟩
        exact ⟨hInputFunction.input_mem_of_pairMember hPair,
          productValue, rightValue, hPair, hCode⟩
    have hRightProjection :
        ℳ.IsRightFunctionProjection 𝕀
          rightFunction input source right := by
      refine ⟨hRightFunction, fun argument rightValue => ?_⟩
      rw [hRightPairs argument rightValue,
        Definitional.Project.Formula.denote_rightFunctionProjectionValue_iff 𝕀]
      constructor
      · exact fun h => h.2
      · rintro ⟨productValue, leftValue, hPair, hCode⟩
        exact ⟨hInputFunction.input_mem_of_pairMember hPair,
          productValue, leftValue, hPair, hCode⟩
    rcases 𝕀.total leftFunction rightFunction with
      ⟨output, hOutputCode⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_splitFunctionCodomainValue_iff
        𝕀 hZF.1 env input output).mpr
          ⟨leftFunction, rightFunction,
            hLeftProjection, hRightProjection, hOutputCode⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_splitFunctionCodomainValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstRight,
        hFirstLeft, hFirstRight, hFirstCode⟩
    rcases hSecond with
      ⟨secondLeft, secondRight,
        hSecondLeft, hSecondRight, hSecondCode⟩
    have hLeftEq : firstLeft = secondLeft := by
      apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
        hFirstLeft.1.1.1 hSecondLeft.1.1.1
      intro argument value
      rw [hFirstLeft.2 argument value, hSecondLeft.2 argument value]
    have hRightEq : firstRight = secondRight := by
      apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
        hFirstRight.1.1.1 hSecondRight.1.1.1
      intro argument value
      rw [hFirstRight.2 argument value, hSecondRight.2 argument value]
    subst secondLeft
    subst secondRight
    exact 𝕀.unique hFirstCode hSecondCode
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_splitFunctionCodomainValue_iff 𝕀 hZF.1]
      at hValue
    rcases hValue with
      ⟨leftFunction, rightFunction,
        hLeftFunction, hRightFunction, hOutputCode⟩
    exact (hTargetProduct output).mpr
      ⟨leftFunction, (hLeftSpace leftFunction).mpr hLeftFunction.1,
        rightFunction, (hRightSpace rightFunction).mpr hRightFunction.1,
        hOutputCode⟩
  · intro first second output hFirstMem hSecondMem hFirst hSecond
    rw [Definitional.Project.Formula.denote_splitFunctionCodomainValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstRight,
        hFirstLeft, hFirstRight, hFirstCode⟩
    rcases hSecond with
      ⟨secondLeft, secondRight,
        hSecondLeft, hSecondRight, hSecondCode⟩
    rcases 𝕀.injective hFirstCode hSecondCode with
      ⟨hLeftEq, hRightEq⟩
    subst secondLeft
    subst secondRight
    have hFirstFunction := (hSourceSpace first).mp hFirstMem
    have hSecondFunction := (hSourceSpace second).mp hSecondMem
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirstFunction.1.1 hSecondFunction.1.1
    intro argument productValue
    constructor
    · intro hFirstPair
      have hProductValue :=
        hFirstFunction.output_mem_of_pairMember hFirstPair
      rcases (hProduct productValue).mp hProductValue with
        ⟨leftValue, hLeftValue,
          rightValue, hRightValue, hProductCode⟩
      rcases hSecondFunction.2.2 argument
          (hFirstFunction.input_mem_of_pairMember hFirstPair) with
        ⟨secondProduct, hSecondProduct, hSecondPair⟩
      rcases (hProduct secondProduct).mp hSecondProduct with
        ⟨secondLeftValue, _, secondRightValue, _, hSecondCode⟩
      have hFirstLeftPair :=
        (hFirstLeft.2 argument leftValue).mpr
          ⟨productValue, rightValue, hFirstPair, hProductCode⟩
      have hSecondLeftPair :=
        (hSecondLeft.2 argument secondLeftValue).mpr
          ⟨secondProduct, secondRightValue, hSecondPair, hSecondCode⟩
      have hLeftValueEq :=
        hFirstLeft.1.1.2 argument leftValue secondLeftValue
          hFirstLeftPair hSecondLeftPair
      have hFirstRightPair :=
        (hFirstRight.2 argument rightValue).mpr
          ⟨productValue, leftValue, hFirstPair, hProductCode⟩
      have hSecondRightPair :=
        (hSecondRight.2 argument secondRightValue).mpr
          ⟨secondProduct, secondLeftValue, hSecondPair, hSecondCode⟩
      have hRightValueEq :=
        hFirstRight.1.1.2 argument rightValue secondRightValue
          hFirstRightPair hSecondRightPair
      subst secondLeftValue
      subst secondRightValue
      have hProductEq := 𝕀.unique hProductCode hSecondCode
      simpa [hProductEq] using hSecondPair
    · intro hSecondPair
      have hProductValue :=
        hSecondFunction.output_mem_of_pairMember hSecondPair
      rcases (hProduct productValue).mp hProductValue with
        ⟨leftValue, hLeftValue,
          rightValue, hRightValue, hProductCode⟩
      rcases hFirstFunction.2.2 argument
          (hSecondFunction.input_mem_of_pairMember hSecondPair) with
        ⟨firstProduct, hFirstProduct, hFirstPair⟩
      rcases (hProduct firstProduct).mp hFirstProduct with
        ⟨firstLeftValue, _, firstRightValue, _, hFirstCode⟩
      have hSecondLeftPair :=
        (hSecondLeft.2 argument leftValue).mpr
          ⟨productValue, rightValue, hSecondPair, hProductCode⟩
      have hFirstLeftPair :=
        (hFirstLeft.2 argument firstLeftValue).mpr
          ⟨firstProduct, firstRightValue, hFirstPair, hFirstCode⟩
      have hLeftValueEq :=
        hFirstLeft.1.1.2 argument firstLeftValue leftValue
          hFirstLeftPair hSecondLeftPair
      have hSecondRightPair :=
        (hSecondRight.2 argument rightValue).mpr
          ⟨productValue, leftValue, hSecondPair, hProductCode⟩
      have hFirstRightPair :=
        (hFirstRight.2 argument firstRightValue).mpr
          ⟨firstProduct, firstLeftValue, hFirstPair, hFirstCode⟩
      have hRightValueEq :=
        hFirstRight.1.1.2 argument firstRightValue rightValue
          hFirstRightPair hSecondRightPair
      subst firstLeftValue
      subst firstRightValue
      have hProductEq := 𝕀.unique hFirstCode hProductCode
      simpa [hProductEq] using hFirstPair
  · intro output hOutput
    rcases (hTargetProduct output).mp hOutput with
      ⟨leftFunction, hLeftFunctionMem,
        rightFunction, hRightFunctionMem, hOutputCode⟩
    have hLeftFunction := (hLeftSpace leftFunction).mp hLeftFunctionMem
    have hRightFunction := (hRightSpace rightFunction).mp hRightFunctionMem
    let inputEnv : Env ℳ 2 := {
      bound := Fin.cases leftFunction <|
        Fin.cases rightFunction Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 (Definitional.Project.BinarySchema.combineFunctionCoordinatesValue 𝒞)
        inputEnv
        (source := source) (target := product)
        (by
          intro argument hArgument
          rcases hLeftFunction.2.2 argument hArgument with
            ⟨leftValue, _, hLeftPair⟩
          rcases hRightFunction.2.2 argument hArgument with
            ⟨rightValue, _, hRightPair⟩
          rcases 𝕀.total leftValue rightValue with
            ⟨productValue, hCode⟩
          exact ⟨productValue,
            (Definitional.Project.Formula.denote_combineFunctionCoordinatesValue_iff
              𝕀 inputEnv argument productValue).mpr
                ⟨leftValue, rightValue,
                  hLeftPair, hRightPair, hCode⟩⟩)
        (by
          intro argument _ firstProduct secondProduct hFirst hSecond
          rw [Definitional.Project.Formula.denote_combineFunctionCoordinatesValue_iff 𝕀]
            at hFirst hSecond
          rcases hFirst with
            ⟨firstLeft, firstRight,
              hFirstLeft, hFirstRight, hFirstCode⟩
          rcases hSecond with
            ⟨secondLeft, secondRight,
              hSecondLeft, hSecondRight, hSecondCode⟩
          have hLeftEq :=
            hLeftFunction.1.2 argument firstLeft secondLeft
              hFirstLeft hSecondLeft
          have hRightEq :=
            hRightFunction.1.2 argument firstRight secondRight
              hFirstRight hSecondRight
          subst secondLeft
          subst secondRight
          exact 𝕀.unique hFirstCode hSecondCode)
        (by
          intro _ productValue _ hValue
          rw [Definitional.Project.Formula.denote_combineFunctionCoordinatesValue_iff 𝕀]
            at hValue
          rcases hValue with
            ⟨leftValue, rightValue,
              hLeftPair, hRightPair, hCode⟩
          exact (hProduct productValue).mpr
            ⟨leftValue,
              hLeftFunction.output_mem_of_pairMember hLeftPair,
              rightValue,
              hRightFunction.output_mem_of_pairMember hRightPair,
              hCode⟩) with
      ⟨input, hInputFunction, hInputPairs⟩
    have hInputMem := (hSourceSpace input).mpr hInputFunction
    have hLeftProjection :
        ℳ.IsLeftFunctionProjection 𝕀
          leftFunction input source left := by
      refine ⟨hLeftFunction, fun argument leftValue => ?_⟩
      constructor
      · intro hLeftPair
        have hArgument :=
          hLeftFunction.input_mem_of_pairMember hLeftPair
        rcases hRightFunction.2.2 argument hArgument with
          ⟨rightValue, _, hRightPair⟩
        rcases 𝕀.total leftValue rightValue with
          ⟨productValue, hCode⟩
        have hInputPair := (hInputPairs argument productValue).mpr
          ⟨hArgument,
            (Definitional.Project.Formula.denote_combineFunctionCoordinatesValue_iff
              𝕀 inputEnv argument productValue).mpr
                ⟨leftValue, rightValue,
                  hLeftPair, hRightPair, hCode⟩⟩
        exact ⟨productValue, rightValue, hInputPair, hCode⟩
      · rintro ⟨productValue, rightValue, hInputPair, hCode⟩
        rcases (hInputPairs argument productValue).mp hInputPair with
          ⟨_, hValue⟩
        rw [Definitional.Project.Formula.denote_combineFunctionCoordinatesValue_iff 𝕀]
          at hValue
        rcases hValue with
          ⟨selectedLeft, selectedRight,
            hSelectedLeft, _, hSelectedCode⟩
        have hLeftEq :=
          (𝕀.injective hCode hSelectedCode).1
        simpa [hLeftEq] using hSelectedLeft
    have hRightProjection :
        ℳ.IsRightFunctionProjection 𝕀
          rightFunction input source right := by
      refine ⟨hRightFunction, fun argument rightValue => ?_⟩
      constructor
      · intro hRightPair
        have hArgument :=
          hRightFunction.input_mem_of_pairMember hRightPair
        rcases hLeftFunction.2.2 argument hArgument with
          ⟨leftValue, _, hLeftPair⟩
        rcases 𝕀.total leftValue rightValue with
          ⟨productValue, hCode⟩
        have hInputPair := (hInputPairs argument productValue).mpr
          ⟨hArgument,
            (Definitional.Project.Formula.denote_combineFunctionCoordinatesValue_iff
              𝕀 inputEnv argument productValue).mpr
                ⟨leftValue, rightValue,
                  hLeftPair, hRightPair, hCode⟩⟩
        exact ⟨productValue, leftValue, hInputPair, hCode⟩
      · rintro ⟨productValue, leftValue, hInputPair, hCode⟩
        rcases (hInputPairs argument productValue).mp hInputPair with
          ⟨_, hValue⟩
        rw [Definitional.Project.Formula.denote_combineFunctionCoordinatesValue_iff 𝕀]
          at hValue
        rcases hValue with
          ⟨selectedLeft, selectedRight,
            _, hSelectedRight, hSelectedCode⟩
        have hRightEq :=
          (𝕀.injective hCode hSelectedCode).2
        simpa [hRightEq] using hSelectedRight
    exact ⟨input, hInputMem,
      (Definitional.Project.Formula.denote_splitFunctionCodomainValue_iff
        𝕀 hZF.1 env input output).mpr
          ⟨leftFunction, rightFunction,
            hLeftProjection, hRightProjection, hOutputCode⟩⟩

/--
不交并上的函数集与两个分量函数集的笛卡尔积等势。
-/
theorem equinumerous_functionSpaceOverUnion
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sourceSpace leftSpace rightSpace targetProduct
      source left right target : ℳ.Domain}
    (hSourceSpace :
      ℳ.IsFunctionSpace 𝕀 sourceSpace source target)
    (hLeftSpace :
      ℳ.IsFunctionSpace 𝕀 leftSpace left target)
    (hRightSpace :
      ℳ.IsFunctionSpace 𝕀 rightSpace right target)
    (hTargetProduct :
      ℳ.IsCartesianProduct 𝕀 targetProduct leftSpace rightSpace)
    (hSourceUnion :
      ℳ.IsUnionOfTwo source left right)
    (hDisjoint :
      ℳ.IsDisjoint left right) :
    ℳ.Equinumerous 𝕀 sourceSpace targetProduct := by
  let env : Env ℳ 2 := {
    bound := Fin.cases left <| Fin.cases right Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.splitFunctionDomainValue 𝒞) env
  · intro input hInput
    have hInputFunction := (hSourceSpace input).mp hInput
    rcases exists_restriction hZF 𝕀 input left with
      ⟨leftFunction, hLeftRestriction⟩
    rcases exists_restriction hZF 𝕀 input right with
      ⟨rightFunction, hRightRestriction⟩
    rcases 𝕀.total leftFunction rightFunction with
      ⟨output, hOutputCode⟩
    exact ⟨output,
      (Definitional.Project.Formula.denote_splitFunctionDomainValue_iff
        𝕀 env input output).mpr
          ⟨leftFunction, rightFunction,
            hLeftRestriction, hRightRestriction, hOutputCode⟩⟩
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_splitFunctionDomainValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstRight,
        hFirstLeft, hFirstRight, hFirstCode⟩
    rcases hSecond with
      ⟨secondLeft, secondRight,
        hSecondLeft, hSecondRight, hSecondCode⟩
    have hLeftEq :=
      hFirstLeft.eq hZF.1 hSecondLeft
    have hRightEq :=
      hFirstRight.eq hZF.1 hSecondRight
    subst secondLeft
    subst secondRight
    exact 𝕀.unique hFirstCode hSecondCode
  · intro input output hInput hValue
    rw [Definitional.Project.Formula.denote_splitFunctionDomainValue_iff 𝕀]
      at hValue
    rcases hValue with
      ⟨leftFunction, rightFunction,
        hLeftRestriction, hRightRestriction, hOutputCode⟩
    have hInputFunction := (hSourceSpace input).mp hInput
    have hLeftFunction :=
      hLeftRestriction.isSetFunctionFromTo hInputFunction <|
        fun value hValue =>
          (hSourceUnion value).mpr <| Or.inl hValue
    have hRightFunction :=
      hRightRestriction.isSetFunctionFromTo hInputFunction <|
        fun value hValue =>
          (hSourceUnion value).mpr <| Or.inr hValue
    exact (hTargetProduct output).mpr
      ⟨leftFunction, (hLeftSpace leftFunction).mpr hLeftFunction,
        rightFunction, (hRightSpace rightFunction).mpr hRightFunction,
        hOutputCode⟩
  · intro first second output hFirstMem hSecondMem hFirst hSecond
    rw [Definitional.Project.Formula.denote_splitFunctionDomainValue_iff 𝕀]
      at hFirst hSecond
    rcases hFirst with
      ⟨firstLeft, firstRight,
        hFirstLeft, hFirstRight, hFirstCode⟩
    rcases hSecond with
      ⟨secondLeft, secondRight,
        hSecondLeft, hSecondRight, hSecondCode⟩
    rcases 𝕀.injective hFirstCode hSecondCode with
      ⟨hLeftEq, hRightEq⟩
    subst secondLeft
    subst secondRight
    have hFirstFunction := (hSourceSpace first).mp hFirstMem
    have hSecondFunction := (hSourceSpace second).mp hSecondMem
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirstFunction.1.1 hSecondFunction.1.1
    intro input value
    constructor
    · intro hFirstPair
      have hInput := hFirstFunction.input_mem_of_pairMember hFirstPair
      rcases (hSourceUnion input).mp hInput with
        hInputLeft | hInputRight
      · have hRestricted :=
          (hFirstLeft.2 input value).mpr ⟨hInputLeft, hFirstPair⟩
        exact (hSecondLeft.2 input value).mp hRestricted |>.2
      · have hRestricted :=
          (hFirstRight.2 input value).mpr ⟨hInputRight, hFirstPair⟩
        exact (hSecondRight.2 input value).mp hRestricted |>.2
    · intro hSecondPair
      have hInput := hSecondFunction.input_mem_of_pairMember hSecondPair
      rcases (hSourceUnion input).mp hInput with
        hInputLeft | hInputRight
      · have hRestricted :=
          (hSecondLeft.2 input value).mpr ⟨hInputLeft, hSecondPair⟩
        exact (hFirstLeft.2 input value).mp hRestricted |>.2
      · have hRestricted :=
          (hSecondRight.2 input value).mpr ⟨hInputRight, hSecondPair⟩
        exact (hFirstRight.2 input value).mp hRestricted |>.2
  · intro output hOutput
    rcases (hTargetProduct output).mp hOutput with
      ⟨leftFunction, hLeftFunctionMem,
        rightFunction, hRightFunctionMem, hOutputCode⟩
    have hLeftFunction := (hLeftSpace leftFunction).mp hLeftFunctionMem
    have hRightFunction := (hRightSpace rightFunction).mp hRightFunctionMem
    rcases KP.exists_unionOfTwo (modelsKP hZF)
        leftFunction rightFunction with
      ⟨input, hInputUnion⟩
    have hInputFunction :=
      hInputUnion.functionFromTo_of_disjoint
        hSourceUnion hDisjoint hLeftFunction hRightFunction
    have hInputMem := (hSourceSpace input).mpr hInputFunction
    have hUnionPairs (argument value : ℳ.Domain) :
        ℳ.PairMember 𝕀 argument value input ↔
          ℳ.PairMember 𝕀 argument value leftFunction ∨
            ℳ.PairMember 𝕀 argument value rightFunction := by
      constructor
      · rintro ⟨pair, hCode, hPair⟩
        rcases (hInputUnion pair).mp hPair with
          hPairLeft | hPairRight
        · exact Or.inl ⟨pair, hCode, hPairLeft⟩
        · exact Or.inr ⟨pair, hCode, hPairRight⟩
      · intro hPair
        rcases hPair with hPairLeft | hPairRight
        · rcases hPairLeft with ⟨pair, hCode, hPair⟩
          exact ⟨pair, hCode,
            (hInputUnion pair).mpr <| Or.inl hPair⟩
        · rcases hPairRight with ⟨pair, hCode, hPair⟩
          exact ⟨pair, hCode,
            (hInputUnion pair).mpr <| Or.inr hPair⟩
    have hLeftRestriction :
        ℳ.IsRestrictionOf 𝕀 leftFunction input left := by
      refine ⟨hLeftFunction.1.1, fun argument value => ?_⟩
      constructor
      · intro hPair
        exact ⟨hLeftFunction.input_mem_of_pairMember hPair,
          (hUnionPairs argument value).mpr <| Or.inl hPair⟩
      · rintro ⟨hArgument, hPair⟩
        rcases (hUnionPairs argument value).mp hPair with
          hPairLeft | hPairRight
        · exact hPairLeft
        · exact False.elim <| hDisjoint argument
            ⟨hArgument,
              hRightFunction.input_mem_of_pairMember hPairRight⟩
    have hRightRestriction :
        ℳ.IsRestrictionOf 𝕀 rightFunction input right := by
      refine ⟨hRightFunction.1.1, fun argument value => ?_⟩
      constructor
      · intro hPair
        exact ⟨hRightFunction.input_mem_of_pairMember hPair,
          (hUnionPairs argument value).mpr <| Or.inr hPair⟩
      · rintro ⟨hArgument, hPair⟩
        rcases (hUnionPairs argument value).mp hPair with
          hPairLeft | hPairRight
        · exact False.elim <| hDisjoint argument
            ⟨hLeftFunction.input_mem_of_pairMember hPairLeft,
              hArgument⟩
        · exact hPairRight
    exact ⟨input, hInputMem,
      (Definitional.Project.Formula.denote_splitFunctionDomainValue_iff
        𝕀 env input output).mpr
          ⟨leftFunction, rightFunction,
            hLeftRestriction, hRightRestriction, hOutputCode⟩⟩

/-- 空定义域上的函数集与任意单元素集等势。 -/
theorem equinumerous_functionSpaceFromEmpty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {space source target singleton value : ℳ.Domain}
    (hSpace : ℳ.IsFunctionSpace 𝕀 space source target)
    (hSourceEmpty : ∀ member, ¬ ℳ.mem member source)
    (hSingleton : ℳ.IsSingletonOf singleton value) :
    ℳ.Equinumerous 𝕀 space singleton := by
  have hEmptyFunction :
      ℳ.IsSetFunctionFromTo 𝕀 source source target := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro pair hPair
      exact False.elim <| hSourceEmpty pair hPair
    · intro input first second hFirst _
      rcases hFirst with ⟨pair, _, hPair⟩
      exact False.elim <| hSourceEmpty pair hPair
    · intro input
      constructor
      · intro hInput
        exact False.elim <| hSourceEmpty input hInput
      · rintro ⟨output, pair, _, hPair⟩
        exact False.elim <| hSourceEmpty pair hPair
    · intro input hInput
      exact False.elim <| hSourceEmpty input hInput
  have hSpaceSingleton : ℳ.IsSingletonOf space source := by
    intro function
    rw [hSpace function]
    constructor
    · intro hFunction
      apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
        hFunction.1.1 hEmptyFunction.1.1
      intro input output
      constructor
      · intro hPair
        exact False.elim <| hSourceEmpty input <|
          hFunction.input_mem_of_pairMember hPair
      · intro hPair
        rcases hPair with ⟨pair, _, hPair⟩
        exact False.elim <| hSourceEmpty pair hPair
    · intro hEq
      simpa [hEq] using hEmptyFunction
  exact exists_bijectionBetweenSingletons
    hZF 𝕀 hSpaceSingleton hSingleton

/-- 取值于单元素集的函数集与该单元素集等势。 -/
theorem equinumerous_functionSpaceIntoSingleton
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {space source target value : ℳ.Domain}
    (hSpace : ℳ.IsFunctionSpace 𝕀 space source target)
    (hTarget : ℳ.IsSingletonOf target value) :
    ℳ.Equinumerous 𝕀 space target := by
  have hValue : ℳ.mem value target :=
    (hTarget value).mpr rfl
  rcases exists_constantFunction hZF 𝕀 hValue with
    ⟨constant, hConstant, hConstantPairs⟩
  have hSpaceSingleton : ℳ.IsSingletonOf space constant := by
    intro function
    rw [hSpace function]
    constructor
    · intro hFunction
      apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
        hFunction.1.1 hConstant.1.1
      intro input output
      constructor
      · intro hPair
        exact (hConstantPairs input output).mpr
          ⟨hFunction.input_mem_of_pairMember hPair,
            (hTarget output).mp <|
              hFunction.output_mem_of_pairMember hPair⟩
      · intro hPair
        rcases (hConstantPairs input output).mp hPair with
          ⟨hInput, hOutputEq⟩
        rcases hFunction.2.2 input hInput with
          ⟨selected, hSelected, hSelectedPair⟩
        have hSelectedEq := (hTarget selected).mp hSelected
        simpa [hOutputEq, hSelectedEq] using hSelectedPair
    · intro hEq
      simpa [hEq] using hConstant
  exact exists_bijectionBetweenSingletons
    hZF 𝕀 hSpaceSingleton hTarget

/-- 非空定义域到空值域的函数集为空，并因而与该空值域等势。 -/
theorem equinumerous_functionSpaceIntoEmpty_of_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {space source target : ℳ.Domain}
    (hSpace : ℳ.IsFunctionSpace 𝕀 space source target)
    (hSourceNonempty : ∃ member, ℳ.mem member source)
    (hTargetEmpty : ∀ member, ¬ ℳ.mem member target) :
    ℳ.Equinumerous 𝕀 space target := by
  have hSpaceEmpty : ∀ function, ¬ ℳ.mem function space := by
    intro function hFunction
    have hSetFunction := (hSpace function).mp hFunction
    rcases hSourceNonempty with ⟨input, hInput⟩
    rcases hSetFunction.2.2 input hInput with
      ⟨output, hOutput, _⟩
    exact hTargetEmpty output hOutput
  have hEq : space = target := by
    apply hZF.1.eq_of_same_members
    intro member
    constructor
    · intro hMember
      exact False.elim <| hSpaceEmpty member hMember
    · intro hMember
      exact False.elim <| hTargetEmpty member hMember
  subst target
  exact Structure.Equinumerous.refl hZF 𝕀 space

end ZF

end SetTheory
end YesMetaZFC
