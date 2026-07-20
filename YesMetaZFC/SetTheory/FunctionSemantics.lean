import YesMetaZFC.SetTheory.Definitional.Project.Order
import YesMetaZFC.SetTheory.Extension
import YesMetaZFC.Automation.HostFocusedSequent

/-!
# 集合编码关系与函数的纸面语义

有序对公式本身只给出编码语法。`OrderedPairConvention.Interpretation` 明确记录一个模型
如何解释该编码，以及编码存在、唯一和坐标单射合同。上层关系、函数、定义域、值域与
限制语义只依赖这份合同，不依赖某个具体有序对实现。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Definitional.Project.OrderedPairConvention

/-- 有序对编码约定在一个集合结构中的完整纸面解释。 -/
structure Interpretation (𝒞 : OrderedPairConvention)
    (ℳ : Structure.{u}) where
  Codes : ℳ.Domain → ℳ.Domain → ℳ.Domain → Prop
  realizes :
    ∀ {depth : Nat} (env : Env ℳ depth)
      (pair left right : Term depth),
      Formula.satisfies env (𝒞.code pair left right) ↔
        Codes (pair.eval env) (left.eval env) (right.eval env)
  total :
    ∀ left right, ∃ pair, Codes pair left right
  unique :
    ∀ {first second left right},
      Codes first left right → Codes second left right →
        first = second
  injective :
    ∀ {pair firstLeft firstRight secondLeft secondRight},
      Codes pair firstLeft firstRight →
      Codes pair secondLeft secondRight →
        firstLeft = secondLeft ∧ firstRight = secondRight

namespace Interpretation

/-- 编码公式满足关系按合同展开。 -/
@[simp] theorem satisfies_code_iff
    {𝒞 : OrderedPairConvention} {ℳ : Structure.{u}}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (pair left right : Term depth) :
    Formula.satisfies env (𝒞.code pair left right) ↔
      𝕀.Codes
        (pair.eval env) (left.eval env) (right.eval env) :=
  𝕀.realizes env pair left right

end Interpretation
end OrderedPairConvention
end Project
end Definitional

namespace Structure

/-- 关系集合 `relation` 含有表示 `(left, right)` 的有序对。 -/
def PairMember {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left right relation : ℳ.Domain) : Prop :=
  ∃ pair, 𝕀.Codes pair left right ∧ ℳ.mem pair relation

/-- `relation` 的每个成员都编码某个有序对。 -/
def IsSetRelation {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation : ℳ.Domain) : Prop :=
  ∀ pair, ℳ.mem pair relation →
    ∃ left right, 𝕀.Codes pair left right

/-- `relation` 是只连接 `carrier` 中元素的集合编码关系。 -/
def IsSetRelationOn {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier : ℳ.Domain) : Prop :=
  IsSetRelation 𝕀 relation ∧
    ∀ left right, PairMember 𝕀 left right relation →
      ℳ.mem left carrier ∧ ℳ.mem right carrier

/-- `function` 是单值的集合编码关系。 -/
def IsSetFunction {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function : ℳ.Domain) : Prop :=
  IsSetRelation 𝕀 function ∧
    ∀ input first second,
      PairMember 𝕀 input first function →
      PairMember 𝕀 input second function →
        first = second

/-- `domain` 正好是 `relation` 的定义域。 -/
def IsDomainOf {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (domain relation : ℳ.Domain) : Prop :=
  ∀ input, ℳ.mem input domain ↔
    ∃ output, PairMember 𝕀 input output relation

/-- `range` 正好是 `relation` 的值域。 -/
def IsRangeOf {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (range relation : ℳ.Domain) : Prop :=
  ∀ output, ℳ.mem output range ↔
    ∃ input, PairMember 𝕀 input output relation

namespace IsDomainOf

/-- 同一关系的两个精确定义域相等。 -/
theorem eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {left right relation : ℳ.Domain}
    (hLeft : ℳ.IsDomainOf 𝕀 left relation)
    (hRight : ℳ.IsDomainOf 𝕀 right relation) :
    left = right := by
  prove_auto

end IsDomainOf

namespace IsRangeOf

/-- 同一关系的两个精确值域相等。 -/
theorem eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {left right relation : ℳ.Domain}
    (hLeft : ℳ.IsRangeOf 𝕀 left relation)
    (hRight : ℳ.IsRangeOf 𝕀 right relation) :
    left = right := by
  prove_auto

end IsRangeOf

register_prove_auto_sequent_rule IsRangeOf.eq PRIORITY 200

/-- `function` 是从 `source` 到 `target` 的集合编码函数。 -/
def IsSetFunctionFromTo {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function source target : ℳ.Domain) : Prop :=
  IsSetFunction 𝕀 function ∧
    IsDomainOf 𝕀 source function ∧
      ∀ input, ℳ.mem input source →
        ∃ output, ℳ.mem output target ∧
          PairMember 𝕀 input output function

/-- 集合编码函数在其定义域上是单射。 -/
def IsSetInjective {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function : ℳ.Domain) : Prop :=
  ∀ first second output,
    ℳ.PairMember 𝕀 first output function →
      ℳ.PairMember 𝕀 second output function →
        first = second

/-- 集合编码函数把 `source` 满射到 `target`。 -/
def IsSetSurjectiveOnto {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function source target : ℳ.Domain) : Prop :=
  ∀ output, ℳ.mem output target →
    ∃ input, ℳ.mem input source ∧
      ℳ.PairMember 𝕀 input output function

/-- `function` 是从 `source` 到 `target` 的集合编码单射。 -/
def IsSetInjectionFromTo {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function source target : ℳ.Domain) : Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 function source target ∧
    ℳ.IsSetInjective 𝕀 function

/-- `function` 是从 `source` 到 `target` 的集合编码双射。 -/
def IsSetBijectionFromTo {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function source target : ℳ.Domain) : Prop :=
  ℳ.IsSetInjectionFromTo 𝕀 function source target ∧
    ℳ.IsSetSurjectiveOnto 𝕀 function source target

namespace IsSetFunctionFromTo

/-- 函数图中的每个输入都属于其精确定义域。 -/
theorem input_mem_of_pairMember {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {function source target input output : ℳ.Domain}
    (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function source target)
    (hPair : ℳ.PairMember 𝕀 input output function) :
    ℳ.mem input source :=
  (hFunction.2.1 input).mpr ⟨output, hPair⟩

/-- 函数图中的每个输出都属于给定目标集。 -/
theorem output_mem_of_pairMember {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {function source target input output : ℳ.Domain}
    (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function source target)
    (hPair : ℳ.PairMember 𝕀 input output function) :
    ℳ.mem output target := by
  have hInput := hFunction.input_mem_of_pairMember hPair
  rcases hFunction.2.2 input hInput with
    ⟨selected, hSelectedTarget, hSelectedPair⟩
  have hOutputEq :=
    hFunction.1.2 input output selected hPair hSelectedPair
  simpa [hOutputEq] using hSelectedTarget

end IsSetFunctionFromTo

/-- `restriction` 正好是 `function` 在 `source` 上的限制。 -/
def IsRestrictionOf {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (restriction function source : ℳ.Domain) : Prop :=
  IsSetRelation 𝕀 restriction ∧
    ∀ input output,
      PairMember 𝕀 input output restriction ↔
        ℳ.mem input source ∧
          PairMember 𝕀 input output function

namespace IsSetRelation

/-- 关系集合的成员可由它编码的坐标和纸面关系成员性刻画。 -/
theorem mem_iff_pairMember {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation pair : ℳ.Domain}
    (hRelation : ℳ.IsSetRelation 𝕀 relation) :
    ℳ.mem pair relation ↔
      ∃ left right,
        𝕀.Codes pair left right ∧
          ℳ.PairMember 𝕀 left right relation := by
  constructor
  · intro hPair
    rcases hRelation pair hPair with ⟨left, right, hCode⟩
    exact ⟨left, right, hCode, pair, hCode, hPair⟩
  · rintro ⟨left, right, hCode, encoded, hEncoded, hMember⟩
    have hEq := 𝕀.unique hCode hEncoded
    simpa [hEq] using hMember

/-- 两个关系集合若编码完全相同的坐标对，则它们相等。 -/
theorem eq_of_pairMember_iff {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ) {left right : ℳ.Domain}
    (hLeft : ℳ.IsSetRelation 𝕀 left)
    (hRight : ℳ.IsSetRelation 𝕀 right)
    (hPairs : ∀ input output,
      ℳ.PairMember 𝕀 input output left ↔
        ℳ.PairMember 𝕀 input output right) :
    left = right := by
  apply hExt.eq_of_same_members left right
  intro pair
  rw [hLeft.mem_iff_pairMember, hRight.mem_iff_pairMember]
  constructor
  · rintro ⟨input, output, hCode, hMember⟩
    exact ⟨input, output, hCode, (hPairs input output).mp hMember⟩
  · rintro ⟨input, output, hCode, hMember⟩
    exact ⟨input, output, hCode, (hPairs input output).mpr hMember⟩

end IsSetRelation

register_prove_auto_sequent_rule
  IsSetRelation.eq_of_pairMember_iff PRIORITY 200

namespace IsRestrictionOf

/-- 单值函数的任意限制仍是单值函数。 -/
theorem isSetFunction {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {restriction function source : ℳ.Domain}
    (hRestriction :
      ℳ.IsRestrictionOf 𝕀 restriction function source)
    (hFunction : ℳ.IsSetFunction 𝕀 function) :
    ℳ.IsSetFunction 𝕀 restriction := by
  prove_auto

/-- 函数在其定义域子集上的限制以该子集为精确定义域。 -/
theorem isDomainOf {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {restriction function source domain : ℳ.Domain}
    (hRestriction :
      ℳ.IsRestrictionOf 𝕀 restriction function source)
    (hDomain : ℳ.IsDomainOf 𝕀 domain function)
    (hSubset : ∀ value, ℳ.mem value source → ℳ.mem value domain) :
    ℳ.IsDomainOf 𝕀 source restriction := by
  prove_auto

/-- 函数限制到定义域子集后仍取值于原目标集。 -/
theorem isSetFunctionFromTo {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {restriction function source domain target : ℳ.Domain}
    (hRestriction :
      ℳ.IsRestrictionOf 𝕀 restriction function source)
    (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function domain target)
    (hSubset : ∀ value, ℳ.mem value source → ℳ.mem value domain) :
    ℳ.IsSetFunctionFromTo 𝕀 restriction source target := by
  refine ⟨hRestriction.isSetFunction hFunction.1,
    hRestriction.isDomainOf hFunction.2.1 hSubset, ?_⟩
  intro input hInput
  rcases hFunction.2.2 input (hSubset input hInput) with
    ⟨output, hOutput, hPair⟩
  exact ⟨output, hOutput,
    (hRestriction.2 input output).mpr ⟨hInput, hPair⟩⟩

/-- 同一函数在同一源集上的两个限制相等。 -/
theorem eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {left right function source : ℳ.Domain}
    (hLeft : ℳ.IsRestrictionOf 𝕀 left function source)
    (hRight : ℳ.IsRestrictionOf 𝕀 right function source) :
    left = right := by
  prove_auto

/-- 先限制到外层源集、再限制到其子集，等于直接限制原函数。 -/
theorem trans {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {outerRestriction innerRestriction function outer inner : ℳ.Domain}
    (hOuter :
      ℳ.IsRestrictionOf 𝕀 outerRestriction function outer)
    (hInner :
      ℳ.IsRestrictionOf 𝕀 innerRestriction function inner)
    (hSubset : ∀ value, ℳ.mem value inner → ℳ.mem value outer) :
    ℳ.IsRestrictionOf 𝕀 innerRestriction outerRestriction inner := by
  prove_auto

end IsRestrictionOf

register_prove_auto_sequent_rule
  IsRestrictionOf.isSetFunction PRIORITY 200
register_prove_auto_sequent_rule
  IsRestrictionOf.isDomainOf PRIORITY 200
register_prove_auto_sequent_rule
  IsRestrictionOf.isSetFunctionFromTo PRIORITY 200

end Structure

namespace Definitional.Project.Formula

/-- schema 实例化与参数向量解释出的纸面关系一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_related_iff
    {ℳ : Structure.{u}} {parameterCount depth : Nat}
    (env : Env ℳ depth)
    (schema : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (input output : Term depth) :
    satisfies env (related schema parameters input output) ↔
      schema.denote (parameters.evalEnv env)
        (input.eval env) (output.eval env) := by
  unfold related BinarySchema.instantiate BinarySchema.denote
  rw [satisfies_bind]
  have hEnv :
      Definitional.Env.substitute env
          (Fin.cases output
            (fun previous => Fin.cases input parameters.get previous)) =
        ((parameters.evalEnv env).push (input.eval env)).push
          (output.eval env) := by
    rw [Env.mk.injEq]
    constructor
    · funext entry
      refine Fin.cases ?_ (fun previous => ?_) entry
      · rfl
      · refine Fin.cases ?_ (fun parameter => ?_) previous <;> rfl
    · rfl
  rw [hEnv]

/-- 有序对成员公式与纸面关系成员语义一致。 -/
theorem satisfies_orderedPairMem_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (left right relation : Term depth) :
    satisfies env (orderedPairMem 𝒞 left right relation) ↔
      ℳ.PairMember 𝕀
        (left.eval env) (right.eval env) (relation.eval env) := by
  simp only [orderedPairMem, Structure.PairMember,
    satisfies_exists_iff, satisfies_conj_iff,
    𝕀.satisfies_code_iff, satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 关系公式与纸面集合编码关系一致。 -/
theorem satisfies_isRelation_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth) (relation : Term depth) :
    satisfies env (isRelation 𝒞 relation) ↔
      ℳ.IsSetRelation 𝕀 (relation.eval env) := by
  simp only [isRelation, Structure.IsSetRelation,
    satisfies_forallMem_iff, satisfies_exists_iff,
    𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]

/-- 函数公式与纸面单值关系一致。 -/
theorem satisfies_isFunction_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (function : Term depth) :
    satisfies env (isFunction 𝒞 function) ↔
      ℳ.IsSetFunction 𝕀 (function.eval env) := by
  simp only [isFunction, satisfies_conj_iff,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_isRelation_iff 𝕀,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hRelation, hSingle⟩
    refine ⟨hRelation, ?_⟩
    intro input first second hFirst hSecond
    exact hExt.eq_of_same_members first second <|
      (satisfies_extensionalEq_iff
        (((env.push input).push first).push second)
        (.bound 1) (.bound 0)).mp
          (hSingle input first second ⟨hFirst, hSecond⟩)
  · rintro ⟨hRelation, hSingle⟩
    refine ⟨hRelation, ?_⟩
    intro input first second hPairs
    apply (satisfies_extensionalEq_iff
      (((env.push input).push first).push second)
      (.bound 1) (.bound 0)).mpr
    have hFirst :
        ℳ.PairMember 𝕀 input first
          (function.eval env) := by
      simpa using hPairs.1
    have hSecond :
        ℳ.PairMember 𝕀 input second
          (function.eval env) := by
      simpa using hPairs.2
    have hEq := hSingle input first second hFirst hSecond
    intro value
    change ℳ.mem value first ↔ ℳ.mem value second
    rw [hEq]

/-- 定义域公式与纸面定义域一致。 -/
theorem satisfies_isDomain_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (domain relation : Term depth) :
    satisfies env (isDomain 𝒞 domain relation) ↔
      ℳ.IsDomainOf 𝕀
        (domain.eval env) (relation.eval env) := by
  simp only [isDomain, Structure.IsDomainOf,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_exists_iff,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 值域公式与纸面值域一致。 -/
theorem satisfies_isRange_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (range relation : Term depth) :
    satisfies env (isRange 𝒞 range relation) ↔
      ℳ.IsRangeOf 𝕀
        (range.eval env) (relation.eval env) := by
  simp only [isRange, Structure.IsRangeOf,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_exists_iff,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 从源到目标的函数公式与纸面语义一致。 -/
theorem satisfies_isFunctionFromTo_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function source target : Term depth) :
    satisfies env
        (isFunctionFromTo 𝒞 function source target) ↔
      ℳ.IsSetFunctionFromTo 𝕀
        (function.eval env) (source.eval env) (target.eval env) := by
  simp only [isFunctionFromTo, Structure.IsSetFunctionFromTo,
    satisfies_conj_iff,
    satisfies_isFunction_iff 𝕀 hExt,
    satisfies_isDomain_iff 𝕀,
    satisfies_forallMem_iff, satisfies_existsMem_iff,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_weaken]

/-- 满射公式与纸面满射一致。 -/
theorem satisfies_isSurjectiveOnto_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function source target : Term depth) :
    satisfies env
        (isSurjectiveOnto 𝒞 function source target) ↔
      ℳ.IsSetSurjectiveOnto 𝕀
        (function.eval env) (source.eval env) (target.eval env) := by
  simp only [isSurjectiveOnto, Structure.IsSetSurjectiveOnto,
    satisfies_forallMem_iff, satisfies_existsMem_iff,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 函数限制公式与纸面限制一致。 -/
theorem satisfies_isRestriction_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (restriction function source : Term depth) :
    satisfies env
        (isRestriction 𝒞 restriction function source) ↔
      ℳ.IsRestrictionOf 𝕀
        (restriction.eval env) (function.eval env)
        (source.eval env) := by
  simp only [isRestriction, Structure.IsRestrictionOf,
    satisfies_conj_iff, satisfies_forall_iff,
    satisfies_iff_iff, satisfies_mem_iff,
    satisfies_isRelation_iff 𝕀,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_weaken]

end Formula

end Project
end Definitional
end SetTheory
end YesMetaZFC
