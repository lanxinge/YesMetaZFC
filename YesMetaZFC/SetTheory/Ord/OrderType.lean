import YesMetaZFC.SetTheory.Card.CantorBernstein
import YesMetaZFC.SetTheory.Foundation
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion
import YesMetaZFC.SetTheory.Ord.Arithmetic.Semantics

/-!
# 良序的序型

本文件为集合编码良序建立 Mostowski 坍缩所需的对象语言谓词与纸面语义。最终得到的
坍缩值和序型保持模型内部集合编码，不借用宿主层序数或宿主层函数。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

structure IsSetCodedWellOrder {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier : ℳ.Domain) : Prop where
  linear : ℳ.IsSetCodedLinearOrder 𝕀 relation carrier
  least :
    ∀ subset, ℳ.MemberSubset subset carrier →
      (∃ value, ℳ.mem value subset) →
        ∃ candidate, ℳ.mem candidate subset ∧
          ∀ value, ℳ.mem value subset →
            ℳ.SameMembers candidate value ∨
              ℳ.PairMember 𝕀 candidate value relation

def IsPredecessorSet {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (predecessors relation carrier current : ℳ.Domain) : Prop :=
  ∀ value, ℳ.mem value predecessors ↔
    ℳ.mem value carrier ∧
      ℳ.PairMember 𝕀 value current relation

def IsRelationInitialSegment {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (segment relation carrier : ℳ.Domain) : Prop :=
  ℳ.MemberSubset segment carrier ∧
    ∀ current, ℳ.mem current segment →
      ∀ predecessor, ℳ.mem predecessor carrier →
        ℳ.PairMember 𝕀 predecessor current relation →
          ℳ.mem predecessor segment

def IsWellOrderCollapseFunction {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (function relation carrier domain : ℳ.Domain) : Prop :=
  ℳ.IsSetFunction 𝕀 function ∧
    ℳ.IsDomainOf 𝕀 domain function ∧
      ℳ.IsRelationInitialSegment 𝕀 domain relation carrier ∧
        ∀ current, ℳ.mem current domain →
          ∀ value, ℳ.PairMember 𝕀 current value function →
            ∀ member, ℳ.mem member value ↔
              ∃ predecessor,
                ℳ.mem predecessor domain ∧
                  ℳ.PairMember 𝕀 predecessor current relation ∧
                    ℳ.PairMember 𝕀 predecessor member function

def IsWellOrderCollapseValue {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier current value : ℳ.Domain) : Prop :=
  ∃ predecessors function,
    ℳ.IsPredecessorSet 𝕀
        predecessors relation carrier current ∧
      ℳ.IsWellOrderCollapseFunction 𝕀
        function relation carrier predecessors ∧
        ℳ.IsRangeOf 𝕀 value function

end Structure

namespace Definitional
namespace Project
namespace Formula

def isSetCodedWellOrder (𝒞 : OrderedPairConvention)
    {depth : Nat} (relation carrier : Term depth) : Formula 1 depth :=
  .conj (isRelation 𝒞 relation)
    (isWellOrderRelation 𝒞 relation carrier)

def isPredecessorSet (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (predecessors relation carrier current : Term depth) :
    Formula 1 depth :=
  .forallE <| .iff
    (.mem Term.newest predecessors.weaken) <|
    .conj (.mem Term.newest carrier.weaken)
      (orderedPairMem 𝒞 Term.newest current.weaken
        relation.weaken)

def isRelationInitialSegment (𝒞 : OrderedPairConvention)
    {depth : Nat} (segment relation carrier : Term depth) :
    Formula 1 depth :=
  .conj (subset segment carrier) <|
    forallMem segment <| forallMem carrier.weaken <| .imp
      (orderedPairMem 𝒞 Term.newest (.bound 1)
        relation.weaken.weaken)
      (.mem Term.newest segment.weaken.weaken)

def isWellOrderCollapseFunction
    (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (function relation carrier domain : Term depth) :
    Formula 1 depth :=
  .conj (isFunction 𝒞 function) <| .conj
    (isDomain 𝒞 domain function) <| .conj
      (isRelationInitialSegment 𝒞 domain relation carrier) <|
      forallMem domain <| .forallE <| .imp
        (orderedPairMem 𝒞 (.bound 1) Term.newest
          function.weaken.weaken) <|
        .forallE <| .iff
          (.mem Term.newest (.bound 1)) <|
          existsMem domain.weaken.weaken.weaken <| .conj
            (orderedPairMem 𝒞 Term.newest (.bound 3)
              relation.weaken.weaken.weaken.weaken) <|
            orderedPairMem 𝒞 Term.newest (.bound 1)
              function.weaken.weaken.weaken.weaken

def isWellOrderCollapseValue
    (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (relation carrier current value : Term depth) :
    Formula 1 depth :=
  .existsE <| .existsE <| .conj
    (isPredecessorSet 𝒞 (.bound 1)
      relation.weaken.weaken carrier.weaken.weaken
      current.weaken.weaken) <| .conj
    (isWellOrderCollapseFunction 𝒞 Term.newest
      relation.weaken.weaken carrier.weaken.weaken (.bound 1))
    (isRange 𝒞 value.weaken.weaken Term.newest)

theorem satisfies_isPredecessorSet_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (predecessors relation carrier current : Term depth) :
    satisfies env
        (isPredecessorSet 𝒞
          predecessors relation carrier current) ↔
      ℳ.IsPredecessorSet 𝕀
        (predecessors.eval env) (relation.eval env)
        (carrier.eval env) (current.eval env) := by
  simp only [isPredecessorSet, Structure.IsPredecessorSet,
    satisfies_forall_iff, satisfies_iff_iff, satisfies_conj_iff,
    satisfies_mem_iff, satisfies_orderedPairMem_iff 𝕀,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 集合编码良序公式与纸面语义一致。 -/
theorem satisfies_isSetCodedWellOrder_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (relation carrier : Term depth) :
    satisfies env
        (isSetCodedWellOrder 𝒞 relation carrier) ↔
      ℳ.IsSetCodedWellOrder 𝕀
        (relation.eval env) (carrier.eval env) := by
  rw [isSetCodedWellOrder]
  simp only [satisfies_conj_iff]
  constructor
  · rintro ⟨hRelation, hWellOrder⟩
    rw [isWellOrderRelation, isWellOrderOn,
      satisfies_conj_iff] at hWellOrder
    rcases hWellOrder with ⟨hLinear, hLeast⟩
    have hLinearSemantic :
        ℳ.IsSetCodedLinearOrder 𝕀
          (relation.eval env) (carrier.eval env) := by
      apply
        (satisfies_isSetCodedLinearOrder_iff
          𝕀 env relation carrier).mp
      rw [isSetCodedLinearOrder, isLinearOrderRelation,
        satisfies_conj_iff]
      exact ⟨hRelation, hLinear⟩
    refine ⟨hLinearSemantic, ?_⟩
    intro subset hSubset ⟨value, hValue⟩
    have hLeastSemantic :
        ∀ subset,
          ℳ.MemberSubset subset (carrier.eval env) →
            ∀ value, ℳ.mem value subset →
              ∃ candidate, ℳ.mem candidate subset ∧
                ∀ other, ℳ.mem other subset →
                  ℳ.SameMembers candidate other ∨
                    ℳ.PairMember 𝕀 candidate other
                      (relation.eval env) := by
      simpa [satisfies_forall_iff, satisfies_imp_iff,
        satisfies_conj_iff, satisfies_existsMem_iff,
        satisfies_truth_iff, satisfies_exists_iff,
        satisfies_forallMem_iff, satisfies_mem_iff,
        satisfies_disj_iff, isLeastOf, lessOrEqual,
        satisfies_related_iff,
        BinarySchema.denote_setCoded_iff 𝕀,
        satisfies_extensionalEq_iff, satisfies_subset_iff,
        TermVector.evalEnv_weaken,
        TermVector.evalEnv_singleton_bound,
        Term.eval_bound_zero_push, Term.eval_bound_one_push,
        Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
        Structure.MemberSubset, Structure.SameMembers] using hLeast
    exact hLeastSemantic subset hSubset value hValue
  · rintro ⟨hLinearSemantic, hLeastSemantic⟩
    have hLinearFormula :=
      (satisfies_isSetCodedLinearOrder_iff
        𝕀 env relation carrier).mpr hLinearSemantic
    rw [isSetCodedLinearOrder, isLinearOrderRelation,
      satisfies_conj_iff] at hLinearFormula
    rcases hLinearFormula with ⟨hRelation, hLinear⟩
    refine ⟨hRelation, ?_⟩
    rw [isWellOrderRelation, isWellOrderOn,
      satisfies_conj_iff]
    refine ⟨hLinear, ?_⟩
    have hLeast :
        ∀ subset,
          ℳ.MemberSubset subset (carrier.eval env) →
            ∀ value, ℳ.mem value subset →
              ∃ candidate, ℳ.mem candidate subset ∧
                ∀ other, ℳ.mem other subset →
                  ℳ.SameMembers candidate other ∨
                    ℳ.PairMember 𝕀 candidate other
                      (relation.eval env) := by
      intro subset hSubset value hValue
      exact hLeastSemantic subset hSubset ⟨value, hValue⟩
    simpa [satisfies_forall_iff, satisfies_imp_iff,
      satisfies_conj_iff, satisfies_existsMem_iff,
      satisfies_truth_iff, satisfies_exists_iff,
      satisfies_forallMem_iff, satisfies_mem_iff,
      satisfies_disj_iff, isLeastOf, lessOrEqual,
      satisfies_related_iff,
      BinarySchema.denote_setCoded_iff 𝕀,
      satisfies_extensionalEq_iff, satisfies_subset_iff,
      TermVector.evalEnv_weaken,
      TermVector.evalEnv_singleton_bound,
      Term.eval_bound_zero_push, Term.eval_bound_one_push,
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
      Structure.MemberSubset, Structure.SameMembers] using hLeast

theorem satisfies_isRelationInitialSegment_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (segment relation carrier : Term depth) :
    satisfies env
        (isRelationInitialSegment 𝒞 segment relation carrier) ↔
      ℳ.IsRelationInitialSegment 𝕀
        (segment.eval env) (relation.eval env)
        (carrier.eval env) := by
  simp only [isRelationInitialSegment,
    Structure.IsRelationInitialSegment, satisfies_conj_iff,
    satisfies_subset_iff, satisfies_forallMem_iff,
    satisfies_imp_iff, satisfies_orderedPairMem_iff 𝕀,
    satisfies_mem_iff, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken, Term.eval_bound_zero_push,
    Term.eval_bound_one_push, Structure.MemberSubset]

theorem satisfies_isWellOrderCollapseFunction_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (function relation carrier domain : Term depth) :
    satisfies env
        (isWellOrderCollapseFunction 𝒞
          function relation carrier domain) ↔
      ℳ.IsWellOrderCollapseFunction 𝕀
        (function.eval env) (relation.eval env)
        (carrier.eval env) (domain.eval env) := by
  simp only [isWellOrderCollapseFunction,
    Structure.IsWellOrderCollapseFunction, satisfies_conj_iff,
    satisfies_isFunction_iff 𝕀 hExt,
    satisfies_isDomain_iff 𝕀,
    satisfies_isRelationInitialSegment_iff 𝕀,
    satisfies_forallMem_iff, satisfies_existsMem_iff,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_iff_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_mem_iff, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push]

theorem satisfies_isWellOrderCollapseValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (relation carrier current value : Term depth) :
    satisfies env
        (isWellOrderCollapseValue 𝒞
          relation carrier current value) ↔
      ℳ.IsWellOrderCollapseValue 𝕀
        (relation.eval env) (carrier.eval env)
        (current.eval env) (value.eval env) := by
  simp only [isWellOrderCollapseValue,
    Structure.IsWellOrderCollapseValue, satisfies_exists_iff,
    satisfies_conj_iff,
    satisfies_isPredecessorSet_iff 𝕀,
    satisfies_isWellOrderCollapseFunction_iff 𝕀 hExt,
    satisfies_isRange_iff 𝕀,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

end Formula

namespace BinarySchema

/-- 用逆双射把序数隶属关系传输到目标载体。 -/
def transportedOrdinalMembership
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := .existsE <| .existsE <| .conj
    (Formula.orderedPairMem 𝒞
      (.bound 3) (.bound 1) (.bound 4)) <| .conj
    (Formula.orderedPairMem 𝒞
      (.bound 2) (.bound 0) (.bound 4))
    (.mem (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

def wellOrderCollapseValue
    (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := Formula.isWellOrderCollapseValue 𝒞
    (.bound 2) (.bound 3) (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.isWellOrderCollapseValue,
      Formula.isPredecessorSet,
      Formula.isWellOrderCollapseFunction,
      Formula.isRelationInitialSegment,
      Formula.isFunction, Formula.isRelation,
      Formula.isDomain, Formula.isRange,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]

end BinarySchema

namespace UnarySchema

/-- 从固定载体中分离当前点的全部严格前驱。 -/
def wellOrderPredecessorMembership
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := Formula.orderedPairMem 𝒞
    Term.newest (.bound 2) (.bound 1)
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 从良序载体中分离函数值落入固定子集的输入。 -/
def wellOrderRangePreimageMembership
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := Formula.existsMem (.bound 2) <|
    Formula.orderedPairMem 𝒞
      (.bound 1) Term.newest (.bound 2)
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.existsMem,
      Formula.FreeClosed, Term.newest]

/-- 当前点的良序坍缩值存在且唯一。 -/
def wellOrderCollapseValueExistsUnique
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := .conj
    (.existsE <| Formula.isWellOrderCollapseValue 𝒞
      (.bound 2) (.bound 3) (.bound 1) (.bound 0)) <|
    .forallE <| .forallE <| .imp
      (.conj
        (Formula.isWellOrderCollapseValue 𝒞
          (.bound 3) (.bound 4) (.bound 2) (.bound 1))
        (Formula.isWellOrderCollapseValue 𝒞
          (.bound 3) (.bound 4) (.bound 2) (.bound 0)))
      (Formula.extensionalEq (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isWellOrderCollapseValue,
      Formula.isPredecessorSet,
      Formula.isWellOrderCollapseFunction,
      Formula.isRelationInitialSegment,
      Formula.isFunction, Formula.isRelation,
      Formula.isDomain, Formula.isRange,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]

end UnarySchema

namespace Formula

/-- 传输后的序关系由逆双射像之间的序数隶属关系精确刻画。 -/
theorem denote_transportedOrdinalMembership_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (left right : ℳ.Domain) :
    (BinarySchema.transportedOrdinalMembership 𝒞).denote
        env left right ↔
      ∃ leftOrdinal rightOrdinal,
        ℳ.PairMember 𝕀 left leftOrdinal (env.bound 0) ∧
          ℳ.PairMember 𝕀 right rightOrdinal (env.bound 0) ∧
            ℳ.mem leftOrdinal rightOrdinal := by
  simp only [BinarySchema.transportedOrdinalMembership,
    BinarySchema.denote,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push]
  rfl

/-- 前驱成员模式的纸面语义。 -/
theorem satisfies_wellOrderPredecessorMembership_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (value : ℳ.Domain) :
    satisfies (env.push value)
        (UnarySchema.wellOrderPredecessorMembership 𝒞).body ↔
      ℳ.PairMember 𝕀 value (env.bound 1) (env.bound 0) := by
  change
    satisfies (env.push value)
        (Formula.orderedPairMem 𝒞
          Term.newest (.bound 2) (.bound 1)) ↔
      ℳ.PairMember 𝕀 value (env.bound 1) (env.bound 0)
  rw [satisfies_orderedPairMem_iff 𝕀]
  rfl

/-- 良序值域逆像成员模式的纸面语义。 -/
theorem satisfies_wellOrderRangePreimageMembership_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (input : ℳ.Domain) :
    satisfies (env.push input)
        (UnarySchema.wellOrderRangePreimageMembership 𝒞).body ↔
      ∃ output,
        ℳ.mem output (env.bound 1) ∧
          ℳ.PairMember 𝕀 input output (env.bound 0) := by
  change
    satisfies (env.push input)
        (Formula.existsMem (.bound 2)
          (Formula.orderedPairMem 𝒞
            (.bound 1) Term.newest (.bound 2))) ↔
      ∃ output,
        ℳ.mem output (env.bound 1) ∧
          ℳ.PairMember 𝕀 input output (env.bound 0)
  simp only [satisfies_existsMem_iff,
    satisfies_orderedPairMem_iff 𝕀]
  rfl

theorem denote_wellOrderCollapseValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 2) (current value : ℳ.Domain) :
    (BinarySchema.wellOrderCollapseValue 𝒞).denote
        env current value ↔
      ℳ.IsWellOrderCollapseValue 𝕀
        (env.bound 0) (env.bound 1) current value := by
  change
    satisfies ((env.push current).push value)
        (Formula.isWellOrderCollapseValue 𝒞
          (.bound 2) (.bound 3) (.bound 1) (.bound 0)) ↔
      ℳ.IsWellOrderCollapseValue 𝕀
        (env.bound 0) (env.bound 1) current value
  rw [satisfies_isWellOrderCollapseValue_iff 𝕀 hExt]
  rfl

/-- 坍缩值存在唯一模式的纸面语义。 -/
theorem satisfies_wellOrderCollapseValueExistsUnique_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 2) (current : ℳ.Domain) :
    satisfies (env.push current)
        (UnarySchema.wellOrderCollapseValueExistsUnique 𝒞).body ↔
      ∃ value,
        ℳ.IsWellOrderCollapseValue 𝕀
            (env.bound 0) (env.bound 1) current value ∧
          ∀ other,
            ℳ.IsWellOrderCollapseValue 𝕀
                (env.bound 0) (env.bound 1) current other →
              other = value := by
  simp only [UnarySchema.wellOrderCollapseValueExistsUnique,
    satisfies_conj_iff, satisfies_exists_iff,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_isWellOrderCollapseValue_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound, and_imp]
  change
    ((∃ value,
        ℳ.IsWellOrderCollapseValue 𝕀
          (env.bound 0) (env.bound 1) current value) ∧
      ∀ first second,
        ℳ.IsWellOrderCollapseValue 𝕀
            (env.bound 0) (env.bound 1) current first →
          ℳ.IsWellOrderCollapseValue 𝕀
              (env.bound 0) (env.bound 1) current second →
            first = second) ↔
      ∃ value,
        ℳ.IsWellOrderCollapseValue 𝕀
            (env.bound 0) (env.bound 1) current value ∧
          ∀ other,
            ℳ.IsWellOrderCollapseValue 𝕀
                (env.bound 0) (env.bound 1) current other →
              other = value
  constructor
  · rintro ⟨⟨value, hValue⟩, hUnique⟩
    exact ⟨value, hValue, fun other hOther =>
      hUnique other value hOther hValue⟩
  · rintro ⟨value, hValue, hUnique⟩
    refine ⟨⟨value, hValue⟩, ?_⟩
    intro first second hFirst hSecond
    exact (hUnique first hFirst).trans
      (hUnique second hSecond).symm

end Formula

end Project
end Definitional

namespace Structure.IsSetCodedWellOrder

/-- 良序关系没有载体内自环。 -/
theorem irrefl {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation carrier value : ℳ.Domain}
    (hOrder : ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hValue : ℳ.mem value carrier) :
    ¬ ℳ.PairMember 𝕀 value value relation :=
  hOrder.linear.2.1.1 value hValue

/-- 良序关系在载体上保持传递。 -/
theorem trans {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation carrier left middle right : ℳ.Domain}
    (hOrder : ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hLeft : ℳ.mem left carrier)
    (hMiddle : ℳ.mem middle carrier)
    (hRight : ℳ.mem right carrier)
    (hLeftMiddle : ℳ.PairMember 𝕀 left middle relation)
    (hMiddleRight : ℳ.PairMember 𝕀 middle right relation) :
    ℳ.PairMember 𝕀 left right relation :=
  hOrder.linear.2.1.2 left hLeft middle hMiddle right hRight
    hLeftMiddle hMiddleRight

/-- 良序关系在线性载体上给出三分比较。 -/
theorem compare {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {relation carrier left right : ℳ.Domain}
    (hOrder : ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hLeft : ℳ.mem left carrier)
    (hRight : ℳ.mem right carrier) :
    ℳ.SameMembers left right ∨
      ℳ.PairMember 𝕀 left right relation ∨
        ℳ.PairMember 𝕀 right left relation :=
  hOrder.linear.2.2 left hLeft right hRight

/--
若反例类能在载体内分离成集合，则集合编码良序支持对应的良序归纳。
-/
theorem induction
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {relation carrier : ℳ.Domain}
    (hOrder : ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (property : ℳ.Domain → Prop)
    (hCounterexamples :
      ∃ counterexamples, ∀ value,
        ℳ.mem value counterexamples ↔
          ℳ.mem value carrier ∧ ¬ property value)
    (hProgressive :
      ∀ current, ℳ.mem current carrier →
        (∀ predecessor, ℳ.mem predecessor carrier →
          ℳ.PairMember 𝕀 predecessor current relation →
            property predecessor) →
          property current) :
    ∀ current, ℳ.mem current carrier → property current := by
  intro current hCurrent
  apply Classical.byContradiction
  intro hCurrentProperty
  rcases hCounterexamples with
    ⟨counterexamples, hCounterexamples⟩
  have hCurrentCounterexample :
      ℳ.mem current counterexamples :=
    (hCounterexamples current).mpr
      ⟨hCurrent, hCurrentProperty⟩
  have hCounterexamplesSubset :
      ℳ.MemberSubset counterexamples carrier := by
    intro value hValue
    exact (hCounterexamples value).mp hValue |>.1
  rcases hOrder.least counterexamples
      hCounterexamplesSubset
      ⟨current, hCurrentCounterexample⟩ with
    ⟨least, hLeastCounterexample, hLeast⟩
  have hLeastData :=
    (hCounterexamples least).mp hLeastCounterexample
  apply hLeastData.2
  apply hProgressive least hLeastData.1
  intro predecessor hPredecessorCarrier hPredecessorLeast
  apply Classical.byContradiction
  intro hPredecessorProperty
  have hPredecessorCounterexample :
      ℳ.mem predecessor counterexamples :=
    (hCounterexamples predecessor).mpr
      ⟨hPredecessorCarrier, hPredecessorProperty⟩
  rcases hLeast predecessor hPredecessorCounterexample with
    hSame | hLeastPredecessor
  · have hEq := hExt.eq_of_same_members least predecessor hSame
    subst predecessor
    exact hOrder.irrefl hLeastData.1 hPredecessorLeast
  · exact hOrder.irrefl hLeastData.1 <|
      hOrder.trans hLeastData.1 hPredecessorCarrier hLeastData.1
        hLeastPredecessor hPredecessorLeast

end Structure.IsSetCodedWellOrder

namespace Structure.IsPredecessorSet

/-- 同一载体中同一点的两个前驱集相等。 -/
theorem eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {left right relation carrier current : ℳ.Domain}
    (hLeft :
      ℳ.IsPredecessorSet 𝕀 left relation carrier current)
    (hRight :
      ℳ.IsPredecessorSet 𝕀 right relation carrier current) :
    left = right := by
  apply hExt.eq_of_same_members
  intro value
  rw [hLeft value, hRight value]

/-- 良序中某一点的前驱集是真初段所需的向下闭初段。 -/
theorem isInitialSegment {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {predecessors relation carrier current : ℳ.Domain}
    (hOrder : ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hCurrent : ℳ.mem current carrier)
    (hPredecessors :
      ℳ.IsPredecessorSet 𝕀
        predecessors relation carrier current) :
    ℳ.IsRelationInitialSegment 𝕀
      predecessors relation carrier := by
  constructor
  · intro value hValue
    exact (hPredecessors value).mp hValue |>.1
  · intro middle hMiddle value hValue hValueMiddle
    have hMiddleData := (hPredecessors middle).mp hMiddle
    exact (hPredecessors value).mpr
      ⟨hValue,
        hOrder.trans hValue hMiddleData.1
          hCurrent
          hValueMiddle hMiddleData.2⟩

end Structure.IsPredecessorSet

namespace Structure.IsRelationInitialSegment

/-- 整个载体是自身的向下闭初段。 -/
theorem refl {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier : ℳ.Domain) :
    ℳ.IsRelationInitialSegment 𝕀 carrier relation carrier :=
  ⟨fun _ h => h, fun _ _ _ h _ => h⟩

end Structure.IsRelationInitialSegment

namespace ZF

/-- ZF 中集合编码关系的载体内前驱集存在。 -/
theorem exists_wellOrderPredecessorSet
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier current : ℳ.Domain) :
    ∃ predecessors,
      ℳ.IsPredecessorSet 𝕀
        predecessors relation carrier current := by
  let env : Env ℳ 2 := {
    bound := Fin.cases relation <| Fin.cases current Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.wellOrderPredecessorMembership 𝒞)
      env carrier with
    ⟨predecessors, hPredecessors⟩
  refine ⟨predecessors, fun value => ?_⟩
  rw [hPredecessors value,
    Definitional.Project.Formula.satisfies_wellOrderPredecessorMembership_iff
      𝕀 env value]
  rfl

end ZF

namespace Structure.IsWellOrderCollapseFunction

/-- 坍缩函数限制到定义域内一点的前驱集后仍满足同一坍缩方程。 -/
theorem restriction
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function relation carrier domain current predecessors
      restricted : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hFunction :
      ℳ.IsWellOrderCollapseFunction 𝕀
        function relation carrier domain)
    (hCurrent : ℳ.mem current domain)
    (hPredecessors :
      ℳ.IsPredecessorSet 𝕀
        predecessors relation carrier current)
    (hRestriction :
      ℳ.IsRestrictionOf 𝕀 restricted function predecessors) :
    ℳ.IsWellOrderCollapseFunction 𝕀
      restricted relation carrier predecessors := by
  have hCurrentCarrier :
      ℳ.mem current carrier :=
    hFunction.2.2.1.1 current hCurrent
  have hPredecessorsSubsetDomain :
      ℳ.MemberSubset predecessors domain := by
    intro predecessor hPredecessor
    have hData := (hPredecessors predecessor).mp hPredecessor
    exact hFunction.2.2.1.2 current hCurrent
      predecessor hData.1 hData.2
  refine ⟨hRestriction.isSetFunction hFunction.1,
    hRestriction.isDomainOf hFunction.2.1
      hPredecessorsSubsetDomain,
    hPredecessors.isInitialSegment hOrder hCurrentCarrier, ?_⟩
  intro index hIndex value hValue member
  have hIndexDomain :=
    hPredecessorsSubsetDomain index hIndex
  have hValueFunction :=
    ((hRestriction.2 index value).mp hValue).2
  rw [hFunction.2.2.2 index hIndexDomain value
    hValueFunction member]
  constructor
  · rintro ⟨predecessor, hPredecessorDomain,
      hPredecessorIndex, hPredecessorValue⟩
    have hIndexData := (hPredecessors index).mp hIndex
    have hPredecessorCarrier :=
      hFunction.2.2.1.1 predecessor hPredecessorDomain
    have hPredecessorCurrent :=
      hOrder.trans hPredecessorCarrier hIndexData.1
        hCurrentCarrier hPredecessorIndex hIndexData.2
    have hPredecessorPredecessors :=
      (hPredecessors predecessor).mpr
        ⟨hPredecessorCarrier, hPredecessorCurrent⟩
    exact ⟨predecessor, hPredecessorPredecessors,
      hPredecessorIndex,
      (hRestriction.2 predecessor member).mpr
        ⟨hPredecessorPredecessors, hPredecessorValue⟩⟩
  · rintro ⟨predecessor, hPredecessorPredecessors,
      hPredecessorIndex, hPredecessorValue⟩
    exact ⟨predecessor,
      hPredecessorsSubsetDomain predecessor
        hPredecessorPredecessors,
      hPredecessorIndex,
      ((hRestriction.2 predecessor member).mp
        hPredecessorValue).2⟩

/-- 坍缩函数在定义域内一点的函数值正是该点的坍缩值。 -/
theorem collapseValue_of_pairMember
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function relation carrier domain current value : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hFunction :
      ℳ.IsWellOrderCollapseFunction 𝕀
        function relation carrier domain)
    (hCurrent : ℳ.mem current domain)
    (hValue : ℳ.PairMember 𝕀 current value function) :
    ℳ.IsWellOrderCollapseValue 𝕀
      relation carrier current value := by
  rcases ZF.exists_wellOrderPredecessorSet
      hZF 𝕀 relation carrier current with
    ⟨predecessors, hPredecessors⟩
  rcases ZF.exists_restriction hZF 𝕀 function predecessors with
    ⟨restricted, hRestriction⟩
  have hRestricted :=
    hFunction.restriction 𝕀 hOrder
      hCurrent hPredecessors hRestriction
  refine ⟨predecessors, restricted,
    hPredecessors, hRestricted, fun member => ?_⟩
  rw [hFunction.2.2.2 current hCurrent value hValue member]
  constructor
  · rintro ⟨predecessor, hPredecessorDomain,
      hPredecessorCurrent, hPredecessorValue⟩
    have hPredecessorCarrier :=
      hFunction.2.2.1.1 predecessor hPredecessorDomain
    exact ⟨predecessor,
      (hRestriction.2 predecessor member).mpr
        ⟨(hPredecessors predecessor).mpr
          ⟨hPredecessorCarrier, hPredecessorCurrent⟩,
          hPredecessorValue⟩⟩
  · rintro ⟨predecessor, hPredecessorValue⟩
    have hPredecessorData :=
      (hRestriction.2 predecessor member).mp hPredecessorValue
    have hPredecessorSetData :=
      (hPredecessors predecessor).mp hPredecessorData.1
    exact ⟨predecessor,
      hFunction.2.2.1.2 current hCurrent
        predecessor hPredecessorSetData.1
        hPredecessorSetData.2,
      hPredecessorSetData.2, hPredecessorData.2⟩

/--
同一初段上的两个坍缩函数若各点坍缩值唯一，则两个函数图相等。
-/
theorem eq_of_collapseValue_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left right relation carrier domain : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hLeft :
      ℳ.IsWellOrderCollapseFunction 𝕀
        left relation carrier domain)
    (hRight :
      ℳ.IsWellOrderCollapseFunction 𝕀
        right relation carrier domain)
    (hUnique :
      ∀ current, ℳ.mem current domain →
        ∀ first second,
          ℳ.IsWellOrderCollapseValue 𝕀
              relation carrier current first →
            ℳ.IsWellOrderCollapseValue 𝕀
                relation carrier current second →
              first = second) :
    left = right := by
  apply hLeft.1.1.eq_of_pairMember_iff hZF.1 hRight.1.1
  intro current value
  have transfer
      {first second : ℳ.Domain}
      (hFirst :
        ℳ.IsWellOrderCollapseFunction 𝕀
          first relation carrier domain)
      (hSecond :
        ℳ.IsWellOrderCollapseFunction 𝕀
          second relation carrier domain)
      (hPair : ℳ.PairMember 𝕀 current value first) :
      ℳ.PairMember 𝕀 current value second := by
    have hCurrent :
        ℳ.mem current domain :=
      (hFirst.2.1 current).mpr ⟨value, hPair⟩
    rcases (hSecond.2.1 current).mp hCurrent with
      ⟨selected, hSelected⟩
    have hValueCollapse :=
      hFirst.collapseValue_of_pairMember
        hZF 𝕀 hOrder hCurrent hPair
    have hSelectedCollapse :=
      hSecond.collapseValue_of_pairMember
        hZF 𝕀 hOrder hCurrent hSelected
    have hEq :=
      hUnique current hCurrent value selected
        hValueCollapse hSelectedCollapse
    simpa [hEq] using hSelected
  exact ⟨transfer hLeft hRight, transfer hRight hLeft⟩

/-- 全载体坍缩函数是单射。 -/
theorem isSetInjective
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function relation carrier : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hFunction :
      ℳ.IsWellOrderCollapseFunction 𝕀
        function relation carrier carrier) :
    ℳ.IsSetInjective 𝕀 function := by
  intro first second output hFirst hSecond
  have hFirstCarrier :
      ℳ.mem first carrier :=
    (hFunction.2.1 first).mpr ⟨output, hFirst⟩
  have hSecondCarrier :
      ℳ.mem second carrier :=
    (hFunction.2.1 second).mpr ⟨output, hSecond⟩
  rcases hOrder.compare hFirstCarrier hSecondCarrier with
    hSame | hFirstSecond | hSecondFirst
  · exact hZF.1.eq_of_same_members first second hSame
  · have hSelf : ℳ.mem output output :=
      (hFunction.2.2.2 second hSecondCarrier
        output hSecond output).mpr
        ⟨first, hFirstCarrier, hFirstSecond, hFirst⟩
    exact False.elim <|
      KP.mem_irrefl (ZF.modelsKP hZF) output hSelf
  · have hSelf : ℳ.mem output output :=
      (hFunction.2.2.2 first hFirstCarrier
        output hFirst output).mpr
        ⟨second, hSecondCarrier, hSecondFirst, hSecond⟩
    exact False.elim <|
      KP.mem_irrefl (ZF.modelsKP hZF) output hSelf

/-- 坍缩函数把原良序关系精确变为值域上的隶属关系。 -/
theorem relation_iff_mem
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function relation carrier first second firstValue secondValue :
      ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hFunction :
      ℳ.IsWellOrderCollapseFunction 𝕀
        function relation carrier carrier)
    (hFirst :
      ℳ.PairMember 𝕀 first firstValue function)
    (hSecond :
      ℳ.PairMember 𝕀 second secondValue function) :
    ℳ.PairMember 𝕀 first second relation ↔
      ℳ.mem firstValue secondValue := by
  have hFirstCarrier :
      ℳ.mem first carrier :=
    (hFunction.2.1 first).mpr ⟨firstValue, hFirst⟩
  have hSecondCarrier :
      ℳ.mem second carrier :=
    (hFunction.2.1 second).mpr ⟨secondValue, hSecond⟩
  constructor
  · intro hFirstSecond
    exact
      (hFunction.2.2.2 second hSecondCarrier
        secondValue hSecond firstValue).mpr
        ⟨first, hFirstCarrier, hFirstSecond, hFirst⟩
  · intro hMember
    rcases
        (hFunction.2.2.2 second hSecondCarrier
          secondValue hSecond firstValue).mp hMember with
      ⟨predecessor, hPredecessorCarrier,
        hPredecessorSecond, hPredecessorValue⟩
    have hEq :=
      hFunction.isSetInjective hZF 𝕀 hOrder
        first predecessor firstValue hFirst hPredecessorValue
    simpa [hEq] using hPredecessorSecond

end Structure.IsWellOrderCollapseFunction

namespace ZF

/--
若某个向下闭初段上每一点的坍缩值都存在唯一，则这些值可由 Replacement 收集成该
初段上的坍缩函数。
-/
theorem exists_wellOrderCollapseFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {relation carrier domain : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hInitial :
      ℳ.IsRelationInitialSegment 𝕀 domain relation carrier)
    (hValues :
      ∀ current, ℳ.mem current domain →
        ∃ value,
          ℳ.IsWellOrderCollapseValue 𝕀
              relation carrier current value ∧
            ∀ other,
              ℳ.IsWellOrderCollapseValue 𝕀
                  relation carrier current other →
                other = value) :
    ∃ function,
      ℳ.IsWellOrderCollapseFunction 𝕀
        function relation carrier domain := by
  let env : Env ℳ 2 := {
    bound := Fin.cases relation <| Fin.cases carrier Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let valueSchema :=
    Definitional.Project.BinarySchema.wellOrderCollapseValue 𝒞
  have hGraphTotal :
      ∀ current, ℳ.mem current domain →
        ∃ pair,
          (valueSchema.functionGraph 𝒞).denote
            env current pair := by
    intro current hCurrent
    rcases hValues current hCurrent with
      ⟨value, hValue, _⟩
    rcases 𝕀.total current value with ⟨pair, hCode⟩
    exact ⟨pair,
      (Definitional.Project.Formula.denote_functionGraph_iff
        𝕀 valueSchema env current pair).mpr
          ⟨value,
            (Definitional.Project.Formula.denote_wellOrderCollapseValue_iff
              𝕀 hZF.1 env current value).mpr hValue,
            hCode⟩⟩
  have hGraphUnique :
      ∀ current, ℳ.mem current domain →
        ∀ first second,
          (valueSchema.functionGraph 𝒞).denote
              env current first →
            (valueSchema.functionGraph 𝒞).denote
              env current second →
            first = second := by
    intro current hCurrent first second hFirst hSecond
    rcases
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 valueSchema env current first).mp hFirst with
      ⟨firstValue, hFirstValue, hFirstCode⟩
    rcases
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 valueSchema env current second).mp hSecond with
      ⟨secondValue, hSecondValue, hSecondCode⟩
    rcases hValues current hCurrent with
      ⟨selected, hSelected, hUnique⟩
    have hValueEq :=
      hUnique secondValue <|
        (Definitional.Project.Formula.denote_wellOrderCollapseValue_iff
          𝕀 hZF.1 env current secondValue).mp hSecondValue
    have hFirstEq :=
      hUnique firstValue <|
        (Definitional.Project.Formula.denote_wellOrderCollapseValue_iff
          𝕀 hZF.1 env current firstValue).mp hFirstValue
    rw [hFirstEq] at hFirstCode
    rw [hValueEq] at hSecondCode
    exact 𝕀.unique hFirstCode hSecondCode
  rcases exists_functionalImageOn hZF
      (valueSchema.functionGraph 𝒞) env domain
      hGraphTotal hGraphUnique with
    ⟨function, hFunctionMembers⟩
  have hPairMember (current value : ℳ.Domain) :
      ℳ.PairMember 𝕀 current value function ↔
        ℳ.mem current domain ∧
          ℳ.IsWellOrderCollapseValue 𝕀
            relation carrier current value := by
    constructor
    · rintro ⟨pair, hCode, hPair⟩
      rcases (hFunctionMembers pair).mp hPair with
        ⟨source, hSource, hGraph⟩
      rcases
          (Definitional.Project.Formula.denote_functionGraph_iff
            𝕀 valueSchema env source pair).mp hGraph with
        ⟨output, hOutput, hGraphCode⟩
      rcases 𝕀.injective hCode hGraphCode with
        ⟨hSourceEq, hOutputEq⟩
      subst source
      subst output
      exact ⟨hSource,
        (Definitional.Project.Formula.denote_wellOrderCollapseValue_iff
          𝕀 hZF.1 env current value).mp hOutput⟩
    · rintro ⟨hCurrent, hValue⟩
      rcases 𝕀.total current value with ⟨pair, hCode⟩
      refine ⟨pair, hCode, (hFunctionMembers pair).mpr ?_⟩
      exact ⟨current, hCurrent,
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 valueSchema env current pair).mpr
            ⟨value,
              (Definitional.Project.Formula.denote_wellOrderCollapseValue_iff
                𝕀 hZF.1 env current value).mpr hValue,
              hCode⟩⟩
  have hRelation : ℳ.IsSetRelation 𝕀 function := by
    intro pair hPair
    rcases (hFunctionMembers pair).mp hPair with
      ⟨current, _, hGraph⟩
    rcases
        (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 valueSchema env current pair).mp hGraph with
      ⟨value, _, hCode⟩
    exact ⟨current, value, hCode⟩
  have hFunction : ℳ.IsSetFunction 𝕀 function := by
    refine ⟨hRelation, ?_⟩
    intro current first second hFirst hSecond
    have hCurrent := ((hPairMember current first).mp hFirst).1
    rcases hValues current hCurrent with
      ⟨selected, hSelected, hUnique⟩
    exact
      (hUnique first
        ((hPairMember current first).mp hFirst).2).trans <|
      (hUnique second
        ((hPairMember current second).mp hSecond).2).symm
  have hDomain : ℳ.IsDomainOf 𝕀 domain function := by
    intro current
    constructor
    · intro hCurrent
      rcases hValues current hCurrent with ⟨value, hValue, _⟩
      exact ⟨value,
        (hPairMember current value).mpr ⟨hCurrent, hValue⟩⟩
    · rintro ⟨value, hValue⟩
      exact ((hPairMember current value).mp hValue).1
  refine ⟨function, hFunction, hDomain, hInitial, ?_⟩
  intro current hCurrent value hValue member
  have hValueCollapse :=
    ((hPairMember current value).mp hValue).2
  rcases hValueCollapse with
    ⟨predecessors, prior, hPredecessors,
      hPrior, hRange⟩
  rw [hRange member]
  constructor
  · rintro ⟨predecessor, hPredecessorValue⟩
    have hPredecessorPredecessors :
        ℳ.mem predecessor predecessors :=
      (hPrior.2.1 predecessor).mpr
        ⟨member, hPredecessorValue⟩
    have hPredecessorData :=
      (hPredecessors predecessor).mp
        hPredecessorPredecessors
    have hPredecessorDomain :=
      hInitial.2 current hCurrent predecessor
        hPredecessorData.1 hPredecessorData.2
    have hPredecessorCollapse :=
      hPrior.collapseValue_of_pairMember
        hZF 𝕀 hOrder hPredecessorPredecessors
        hPredecessorValue
    exact ⟨predecessor, hPredecessorDomain,
      hPredecessorData.2,
      (hPairMember predecessor member).mpr
        ⟨hPredecessorDomain, hPredecessorCollapse⟩⟩
  · rintro ⟨predecessor, hPredecessorDomain,
      hPredecessorCurrent, hPredecessorValue⟩
    have hPredecessorCarrier :=
      hInitial.1 predecessor hPredecessorDomain
    have hPredecessorPredecessors :=
      (hPredecessors predecessor).mpr
        ⟨hPredecessorCarrier, hPredecessorCurrent⟩
    rcases (hPrior.2.1 predecessor).mp
        hPredecessorPredecessors with
      ⟨priorValue, hPriorValue⟩
    have hCurrentCollapse :=
      ((hPairMember predecessor member).mp
        hPredecessorValue).2
    have hPriorCollapse :=
      hPrior.collapseValue_of_pairMember
        hZF 𝕀 hOrder hPredecessorPredecessors hPriorValue
    rcases hValues predecessor hPredecessorDomain with
      ⟨selected, hSelected, hUnique⟩
    have hEq :=
      hUnique member hCurrentCollapse
    have hPriorEq :=
      hUnique priorValue hPriorCollapse
    exact ⟨predecessor, by
      simpa [hEq, hPriorEq] using hPriorValue⟩

end ZF

namespace Structure

/-- `ordinal` 是集合编码良序的规范坍缩值域。 -/
def IsWellOrderType {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier ordinal : ℳ.Domain) : Prop :=
  ∃ function,
    ℳ.IsWellOrderCollapseFunction 𝕀
        function relation carrier carrier ∧
      ℳ.IsRangeOf 𝕀 ordinal function

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- `ordinal` 是集合编码良序的规范坍缩值域。 -/
def isWellOrderType (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (relation carrier ordinal : Term depth) : Formula 1 depth :=
  .existsE <| .conj
    (isWellOrderCollapseFunction 𝒞 Term.newest
      relation.weaken carrier.weaken carrier.weaken)
    (isRange 𝒞 ordinal.weaken Term.newest)

/-- 良序规范序型公式与纸面坍缩值域一致。 -/
theorem satisfies_isWellOrderType_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (relation carrier ordinal : Term depth) :
    satisfies env
        (isWellOrderType 𝒞 relation carrier ordinal) ↔
      ℳ.IsWellOrderType 𝕀
        (relation.eval env) (carrier.eval env)
        (ordinal.eval env) := by
  simp only [isWellOrderType, Structure.IsWellOrderType,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isWellOrderCollapseFunction_iff 𝕀 hExt,
    satisfies_isRange_iff 𝕀,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Formula

end Project
end Definitional

namespace ZF

/-- 集合编码良序中每一点的规范坍缩值都存在且唯一。 -/
theorem wellOrderCollapseValue_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {relation carrier : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier) :
    ∀ current, ℳ.mem current carrier →
      ∃ value,
        ℳ.IsWellOrderCollapseValue 𝕀
            relation carrier current value ∧
          ∀ other,
            ℳ.IsWellOrderCollapseValue 𝕀
                relation carrier current other →
              other = value := by
  let env : Env ℳ 2 := {
    bound := Fin.cases relation <| Fin.cases carrier Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∃ value,
      ℳ.IsWellOrderCollapseValue 𝕀
          relation carrier current value ∧
        ∀ other,
          ℳ.IsWellOrderCollapseValue 𝕀
              relation carrier current other →
            other = value
  have hEnvRelation : env.bound 0 = relation := by
    rfl
  have hEnvCarrier : env.bound 1 = carrier := by
    rfl
  apply hOrder.induction hZF.1 property
  · rcases exists_separation hZF
        (Definitional.Project.UnarySchema.wellOrderCollapseValueExistsUnique
          𝒞).neg
        env carrier with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun current => ?_⟩
    rw [hCounterexamples current]
    simp only [Definitional.Project.UnarySchema.neg,
      Definitional.Project.Formula.satisfies_neg_iff,
      property,
      hEnvRelation, hEnvCarrier,
      Definitional.Project.Formula.satisfies_wellOrderCollapseValueExistsUnique_iff
        𝕀 hZF.1 env current]
  · intro current hCurrent hPrevious
    rcases exists_wellOrderPredecessorSet
        hZF 𝕀 relation carrier current with
      ⟨predecessors, hPredecessors⟩
    have hPredecessorValues :
        ∀ predecessor, ℳ.mem predecessor predecessors →
          ∃ value,
            ℳ.IsWellOrderCollapseValue 𝕀
                relation carrier predecessor value ∧
              ∀ other,
                ℳ.IsWellOrderCollapseValue 𝕀
                    relation carrier predecessor other →
                  other = value := by
      intro predecessor hPredecessor
      have hData := (hPredecessors predecessor).mp hPredecessor
      exact hPrevious predecessor hData.1 hData.2
    rcases exists_wellOrderCollapseFunction hZF 𝕀 hOrder
        (hPredecessors.isInitialSegment hOrder hCurrent)
        hPredecessorValues with
      ⟨function, hFunction⟩
    rcases exists_range_of_setFunction hZF 𝕀
        hFunction.1 hFunction.2.1 with
      ⟨value, hRange⟩
    have hValue :
        ℳ.IsWellOrderCollapseValue 𝕀
          relation carrier current value :=
      ⟨predecessors, function,
        hPredecessors, hFunction, hRange⟩
    refine ⟨value, hValue, ?_⟩
    intro other hOther
    rcases hOther with
      ⟨otherPredecessors, otherFunction,
        hOtherPredecessors, hOtherFunction, hOtherRange⟩
    have hPredecessorEq :=
      hOtherPredecessors.eq hZF.1 hPredecessors
    subst otherPredecessors
    have hFunctionEq :=
      hOtherFunction.eq_of_collapseValue_unique
        hZF 𝕀 hOrder hFunction <| by
          intro predecessor hPredecessor first second
            hFirst hSecond
          have hData :=
            (hPredecessors predecessor).mp hPredecessor
          rcases hPrevious predecessor hData.1 hData.2 with
            ⟨selected, hSelected, hUnique⟩
          exact (hUnique first hFirst).trans
            (hUnique second hSecond).symm
    subst otherFunction
    exact hOtherRange.eq hZF.1 hRange

/-- 每个集合编码良序都有唯一的规范坍缩序型。 -/
theorem wellOrderType_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {relation carrier : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier) :
    ∃ ordinal,
      ℳ.IsWellOrderType 𝕀 relation carrier ordinal ∧
        ∀ other,
          ℳ.IsWellOrderType 𝕀 relation carrier other →
            other = ordinal := by
  have hValues :=
    wellOrderCollapseValue_existsUnique hZF 𝕀 hOrder
  rcases exists_wellOrderCollapseFunction hZF 𝕀 hOrder
      (Structure.IsRelationInitialSegment.refl
        𝕀 relation carrier)
      hValues with
    ⟨function, hFunction⟩
  rcases exists_range_of_setFunction hZF 𝕀
      hFunction.1 hFunction.2.1 with
    ⟨ordinal, hRange⟩
  refine ⟨ordinal, ⟨function, hFunction, hRange⟩, ?_⟩
  intro other hOther
  rcases hOther with
    ⟨otherFunction, hOtherFunction, hOtherRange⟩
  have hFunctionEq :=
    hOtherFunction.eq_of_collapseValue_unique
      hZF 𝕀 hOrder hFunction <| by
        intro current hCurrent first second hFirst hSecond
        rcases hValues current hCurrent with
          ⟨selected, hSelected, hUnique⟩
        exact (hUnique first hFirst).trans
          (hUnique second hSecond).symm
  subst otherFunction
  exact hOtherRange.eq hZF.1 hRange

end ZF

namespace Structure.IsWellOrderType

/-- 良序载体与其规范序型等势。 -/
theorem equinumerous
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {relation carrier ordinal : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hType :
      ℳ.IsWellOrderType 𝕀 relation carrier ordinal) :
    ℳ.Equinumerous 𝕀 carrier ordinal := by
  rcases hType with ⟨function, hFunction, hRange⟩
  have hIntoOrdinal :
      ∀ input, ℳ.mem input carrier →
        ∃ output, ℳ.mem output ordinal ∧
          ℳ.PairMember 𝕀 input output function := by
    intro input hInput
    rcases (hFunction.2.1 input).mp hInput with
      ⟨output, hOutput⟩
    exact ⟨output, (hRange output).mpr ⟨input, hOutput⟩,
      hOutput⟩
  have hSurjective :
      ℳ.IsSetSurjectiveOnto 𝕀
        function carrier ordinal := by
    intro output hOutput
    rcases (hRange output).mp hOutput with
      ⟨input, hInput⟩
    exact ⟨input,
      (hFunction.2.1 input).mpr ⟨output, hInput⟩,
      hInput⟩
  exact ⟨function,
    ⟨⟨⟨hFunction.1, hFunction.2.1, hIntoOrdinal⟩,
      hFunction.isSetInjective hZF 𝕀 hOrder⟩,
      hSurjective⟩⟩

/-- 良序的规范坍缩值域是序数。 -/
theorem isOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {relation carrier ordinal : ℳ.Domain}
    (hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier)
    (hType :
      ℳ.IsWellOrderType 𝕀 relation carrier ordinal) :
    ℳ.IsOrdinal ordinal := by
  rcases hType with ⟨function, hFunction, hRange⟩
  have hInjective :=
    hFunction.isSetInjective hZF 𝕀 hOrder
  have hTransitive : ℳ.TransitiveSet ordinal := by
    intro middle hMiddle member hMember
    rcases (hRange middle).mp hMiddle with
      ⟨current, hCurrentValue⟩
    have hCurrent :
        ℳ.mem current carrier :=
      (hFunction.2.1 current).mpr
        ⟨middle, hCurrentValue⟩
    rcases
        (hFunction.2.2.2 current hCurrent
          middle hCurrentValue member).mp hMember with
      ⟨predecessor, _, _, hPredecessorValue⟩
    exact (hRange member).mpr
      ⟨predecessor, hPredecessorValue⟩
  refine ⟨hTransitive, ?_⟩
  refine ⟨?_, ?_⟩
  · refine {
      irrefl := ?_
      trans := ?_
      compare := ?_
    }
    · intro value _ hSelf
      exact KP.mem_irrefl (ZF.modelsKP hZF) value hSelf
    · intro left hLeft middle hMiddle right hRight
        hLeftMiddle hMiddleRight
      rcases (hRange left).mp hLeft with
        ⟨leftInput, hLeftValue⟩
      rcases (hRange middle).mp hMiddle with
        ⟨middleInput, hMiddleValue⟩
      rcases (hRange right).mp hRight with
        ⟨rightInput, hRightValue⟩
      have hLeftMiddleRelation :=
        (hFunction.relation_iff_mem hZF 𝕀 hOrder
          hLeftValue hMiddleValue).mpr hLeftMiddle
      have hMiddleRightRelation :=
        (hFunction.relation_iff_mem hZF 𝕀 hOrder
          hMiddleValue hRightValue).mpr hMiddleRight
      have hLeftInputCarrier :=
        (hFunction.2.1 leftInput).mpr
          ⟨left, hLeftValue⟩
      have hMiddleInputCarrier :=
        (hFunction.2.1 middleInput).mpr
          ⟨middle, hMiddleValue⟩
      have hRightInputCarrier :=
        (hFunction.2.1 rightInput).mpr
          ⟨right, hRightValue⟩
      exact
        (hFunction.relation_iff_mem hZF 𝕀 hOrder
          hLeftValue hRightValue).mp <|
          hOrder.trans hLeftInputCarrier
            hMiddleInputCarrier hRightInputCarrier
            hLeftMiddleRelation hMiddleRightRelation
    · intro left hLeft right hRight
      rcases (hRange left).mp hLeft with
        ⟨leftInput, hLeftValue⟩
      rcases (hRange right).mp hRight with
        ⟨rightInput, hRightValue⟩
      have hLeftInputCarrier :=
        (hFunction.2.1 leftInput).mpr
          ⟨left, hLeftValue⟩
      have hRightInputCarrier :=
        (hFunction.2.1 rightInput).mpr
          ⟨right, hRightValue⟩
      rcases hOrder.compare
          hLeftInputCarrier hRightInputCarrier with
        hSame | hLeftRight | hRightLeft
      · have hInputEq :=
          hZF.1.eq_of_same_members
            leftInput rightInput hSame
        subst rightInput
        have hValueEq :=
          hFunction.1.2 leftInput left right
            hLeftValue hRightValue
        exact Or.inl <| by
          intro member
          simp [hValueEq]
      · exact Or.inr <| Or.inl <|
          (hFunction.relation_iff_mem hZF 𝕀 hOrder
            hLeftValue hRightValue).mp hLeftRight
      · exact Or.inr <| Or.inr <|
          (hFunction.relation_iff_mem hZF 𝕀 hOrder
            hRightValue hLeftValue).mp hRightLeft
  · intro subset hSubset ⟨value, hValue⟩
    let env : Env ℳ 2 := {
      bound := Fin.cases function <| Fin.cases subset Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases ZF.exists_separation hZF
        (Definitional.Project.UnarySchema.wellOrderRangePreimageMembership
          𝒞)
        env carrier with
      ⟨preimage, hPreimage⟩
    have hPreimageSemantic (input : ℳ.Domain) :
        ℳ.mem input preimage ↔
          ℳ.mem input carrier ∧
            ∃ output, ℳ.mem output subset ∧
              ℳ.PairMember 𝕀 input output function := by
      rw [hPreimage input,
        Definitional.Project.Formula.satisfies_wellOrderRangePreimageMembership_iff
          𝕀 env input]
      rfl
    have hPreimageSubset :
        ℳ.MemberSubset preimage carrier := by
      intro input hInput
      exact (hPreimageSemantic input).mp hInput |>.1
    have hPreimageNonempty :
        ∃ input, ℳ.mem input preimage := by
      have hValueOrdinal := hSubset value hValue
      rcases (hRange value).mp hValueOrdinal with
        ⟨input, hInputValue⟩
      exact ⟨input, (hPreimageSemantic input).mpr
        ⟨(hFunction.2.1 input).mpr
          ⟨value, hInputValue⟩,
          value, hValue, hInputValue⟩⟩
    rcases hOrder.least preimage
        hPreimageSubset hPreimageNonempty with
      ⟨leastInput, hLeastInput, hLeast⟩
    rcases (hPreimageSemantic leastInput).mp hLeastInput with
      ⟨hLeastCarrier, leastValue,
        hLeastValueSubset, hLeastValue⟩
    refine ⟨leastValue, hLeastValueSubset, ?_⟩
    intro otherValue hOtherValue
    have hOtherOrdinal := hSubset otherValue hOtherValue
    rcases (hRange otherValue).mp hOtherOrdinal with
      ⟨otherInput, hOtherInputValue⟩
    have hOtherInputPreimage :
        ℳ.mem otherInput preimage :=
      (hPreimageSemantic otherInput).mpr
        ⟨(hFunction.2.1 otherInput).mpr
          ⟨otherValue, hOtherInputValue⟩,
          otherValue, hOtherValue, hOtherInputValue⟩
    rcases hLeast otherInput hOtherInputPreimage with
      hSame | hLeastOther
    · have hInputEq :=
        hZF.1.eq_of_same_members
          leastInput otherInput hSame
      subst otherInput
      have hValueEq :=
        hFunction.1.2 leastInput
          leastValue otherValue
          hLeastValue hOtherInputValue
      exact Or.inl <| by
        intro member
        simp [hValueEq]
    · exact Or.inr <|
        (hFunction.relation_iff_mem hZF 𝕀 hOrder
          hLeastValue hOtherInputValue).mp hLeastOther

end Structure.IsWellOrderType

namespace ZF

/--
序数经模型内部单射传到目标集合的值域后，得到目标子集上的集合编码良序，且其规范
序型仍是原序数。
-/
theorem exists_wellOrderRealization_of_ordinalInjection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {α source function : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hInjection :
      ℳ.IsSetInjectionFromTo 𝕀 function α source) :
    ∃ carrier relation,
      ℳ.MemberSubset carrier source ∧
        ℳ.IsSetRelationOn 𝕀 relation carrier ∧
          ℳ.IsSetCodedWellOrder 𝕀 relation carrier ∧
            ℳ.IsWellOrderType 𝕀 relation carrier α := by
  rcases exists_range_of_setFunction hZF 𝕀
      hInjection.1.1 hInjection.1.2.1 with
    ⟨carrier, hCarrierRange⟩
  have hCarrierSubset : ℳ.MemberSubset carrier source := by
    intro output hOutput
    rcases (hCarrierRange output).mp hOutput with
      ⟨input, hPair⟩
    exact hInjection.1.output_mem_of_pairMember hPair
  have hForwardBijection :
      ℳ.IsSetBijectionFromTo 𝕀 function α carrier := by
    have hForwardFunction :
        ℳ.IsSetFunctionFromTo 𝕀 function α carrier := by
      refine ⟨hInjection.1.1, hInjection.1.2.1, ?_⟩
      intro input hInput
      rcases hInjection.1.2.2 input hInput with
        ⟨output, _, hPair⟩
      exact ⟨output, (hCarrierRange output).mpr
        ⟨input, hPair⟩, hPair⟩
    have hForwardSurjective :
        ℳ.IsSetSurjectiveOnto 𝕀 function α carrier := by
      intro output hOutput
      rcases (hCarrierRange output).mp hOutput with
        ⟨input, hPair⟩
      exact ⟨input,
        hInjection.1.input_mem_of_pairMember hPair, hPair⟩
    exact ⟨⟨hForwardFunction, hInjection.2⟩,
      hForwardSurjective⟩
  rcases exists_inverseBijectionWithPairs hZF 𝕀
      hForwardBijection with
    ⟨inverse, hInverse, _⟩
  let env : Env ℳ 1 := {
    bound := fun _ => inverse
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_setRelationOn_of_denote hZF 𝕀
      (Definitional.Project.BinarySchema.transportedOrdinalMembership 𝒞)
      env carrier with
    ⟨relation, hRelationOn, hRelationPairs⟩
  have hRelation (left right : ℳ.Domain) :
      ℳ.PairMember 𝕀 left right relation ↔
        ℳ.mem left carrier ∧
          ℳ.mem right carrier ∧
            ∃ leftOrdinal rightOrdinal,
              ℳ.PairMember 𝕀 left leftOrdinal inverse ∧
                ℳ.PairMember 𝕀 right rightOrdinal inverse ∧
                  ℳ.mem leftOrdinal rightOrdinal := by
    rw [hRelationPairs left right,
      Definitional.Project.Formula.denote_transportedOrdinalMembership_iff 𝕀]
  have hOrder :
      ℳ.IsSetCodedWellOrder 𝕀 relation carrier := by
    refine ⟨⟨hRelationOn.1, ?_⟩, ?_⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro value hValue hSelf
        rcases (hRelation value value).mp hSelf with
          ⟨_, _, leftOrdinal, rightOrdinal,
            hLeftValue, hRightValue, hMember⟩
        have hOrdinalEq :=
          hInverse.1.1.1.2 value leftOrdinal rightOrdinal
            hLeftValue hRightValue
        subst rightOrdinal
        exact hα.wellOrder.linear.irrefl leftOrdinal
          (hInverse.1.1.output_mem_of_pairMember hLeftValue)
          hMember
      · intro left hLeft middle hMiddle right hRight
          hLeftMiddle hMiddleRight
        rcases (hRelation left middle).mp hLeftMiddle with
          ⟨_, _, leftOrdinal, firstMiddleOrdinal,
            hLeftValue, hFirstMiddleValue, hLeftMember⟩
        rcases (hRelation middle right).mp hMiddleRight with
          ⟨_, _, secondMiddleOrdinal, rightOrdinal,
            hSecondMiddleValue, hRightValue, hRightMember⟩
        have hMiddleEq :=
          hInverse.1.1.1.2 middle
            firstMiddleOrdinal secondMiddleOrdinal
            hFirstMiddleValue hSecondMiddleValue
        subst secondMiddleOrdinal
        have hTransitive :=
          hα.wellOrder.linear.trans leftOrdinal
            (hInverse.1.1.output_mem_of_pairMember hLeftValue)
            firstMiddleOrdinal
            (hInverse.1.1.output_mem_of_pairMember
              hFirstMiddleValue)
            rightOrdinal
            (hInverse.1.1.output_mem_of_pairMember hRightValue)
            hLeftMember hRightMember
        exact (hRelation left right).mpr
          ⟨hLeft, hRight, leftOrdinal, rightOrdinal,
            hLeftValue, hRightValue, hTransitive⟩
      · intro left hLeft right hRight
        rcases hInverse.1.1.2.2 left hLeft with
          ⟨leftOrdinal, hLeftOrdinal, hLeftValue⟩
        rcases hInverse.1.1.2.2 right hRight with
          ⟨rightOrdinal, hRightOrdinal, hRightValue⟩
        rcases hα.wellOrder.linear.compare
            leftOrdinal hLeftOrdinal
            rightOrdinal hRightOrdinal with
          hSame | hLeftRight | hRightLeft
        · have hOrdinalEq :=
            hZF.1.eq_of_same_members
              leftOrdinal rightOrdinal hSame
          subst rightOrdinal
          have hValueEq :=
            hInverse.1.2 left right leftOrdinal
              hLeftValue hRightValue
          exact Or.inl <| by
            intro member
            simp [hValueEq]
        · exact Or.inr <| Or.inl <|
            (hRelation left right).mpr
              ⟨hLeft, hRight, leftOrdinal, rightOrdinal,
                hLeftValue, hRightValue, hLeftRight⟩
        · exact Or.inr <| Or.inr <|
            (hRelation right left).mpr
              ⟨hRight, hLeft, rightOrdinal, leftOrdinal,
                hRightValue, hLeftValue, hRightLeft⟩
    · intro subset hSubset ⟨selected, hSelected⟩
      rcases exists_restriction hZF 𝕀 inverse subset with
        ⟨restricted, hRestricted⟩
      have hRestrictedFunction :
          ℳ.IsSetFunctionFromTo 𝕀 restricted subset α :=
        hRestricted.isSetFunctionFromTo hInverse.1.1 hSubset
      rcases exists_range_of_setFunction hZF 𝕀
          hRestrictedFunction.1 hRestrictedFunction.2.1 with
        ⟨image, hImageRange⟩
      have hImageSubset : ℳ.MemberSubset image α := by
        intro output hOutput
        rcases (hImageRange output).mp hOutput with
          ⟨input, hPair⟩
        exact hRestrictedFunction.output_mem_of_pairMember hPair
      have hImageNonempty : ∃ output, ℳ.mem output image := by
        rcases hRestrictedFunction.2.2 selected hSelected with
          ⟨output, _, hPair⟩
        exact ⟨output, (hImageRange output).mpr
          ⟨selected, hPair⟩⟩
      rcases hα.wellOrder.least image
          hImageSubset hImageNonempty with
        ⟨leastOrdinal, hLeastOrdinal, hLeast⟩
      rcases (hImageRange leastOrdinal).mp hLeastOrdinal with
        ⟨least, hLeastValueRestricted⟩
      have hLeastSubset :
          ℳ.mem least subset :=
        hRestrictedFunction.input_mem_of_pairMember
          hLeastValueRestricted
      have hLeastValue :
          ℳ.PairMember 𝕀 least leastOrdinal inverse :=
        (hRestricted.2 least leastOrdinal).mp
          hLeastValueRestricted |>.2
      refine ⟨least, hLeastSubset, ?_⟩
      intro other hOther
      rcases hRestrictedFunction.2.2 other hOther with
        ⟨otherOrdinal, _, hOtherValueRestricted⟩
      have hOtherOrdinalImage :
          ℳ.mem otherOrdinal image :=
        (hImageRange otherOrdinal).mpr
          ⟨other, hOtherValueRestricted⟩
      have hOtherValue :
          ℳ.PairMember 𝕀 other otherOrdinal inverse :=
        (hRestricted.2 other otherOrdinal).mp
          hOtherValueRestricted |>.2
      rcases hLeast otherOrdinal hOtherOrdinalImage with
        hSame | hMember
      · have hOrdinalEq :=
          hZF.1.eq_of_same_members leastOrdinal otherOrdinal hSame
        subst otherOrdinal
        have hValueEq :=
          hInverse.1.2 least other leastOrdinal
            hLeastValue hOtherValue
        exact Or.inl <| by
          intro member
          simp [hValueEq]
      · exact Or.inr <| (hRelation least other).mpr
          ⟨hSubset least hLeastSubset,
            hSubset other hOther,
            leastOrdinal, otherOrdinal,
            hLeastValue, hOtherValue, hMember⟩
  have hInverseRange : ℳ.IsRangeOf 𝕀 α inverse := by
    intro output
    constructor
    · intro hOutput
      rcases hInverse.2 output hOutput with
        ⟨input, _, hPair⟩
      exact ⟨input, hPair⟩
    · rintro ⟨input, hPair⟩
      exact hInverse.1.1.output_mem_of_pairMember hPair
  have hCollapse :
      ℳ.IsWellOrderCollapseFunction 𝕀
        inverse relation carrier carrier := by
    refine ⟨hInverse.1.1.1, hInverse.1.1.2.1,
      Structure.IsRelationInitialSegment.refl
        𝕀 relation carrier, ?_⟩
    intro current hCurrent value hCurrentValue member
    constructor
    · intro hMember
      have hValueOrdinal :=
        hInverse.1.1.output_mem_of_pairMember hCurrentValue
      have hMemberOrdinal :=
        hα.transitive value hValueOrdinal member hMember
      rcases hInverse.2 member hMemberOrdinal with
        ⟨predecessor, hPredecessor, hPredecessorValue⟩
      exact ⟨predecessor, hPredecessor,
        (hRelation predecessor current).mpr
          ⟨hPredecessor, hCurrent,
            member, value,
            hPredecessorValue, hCurrentValue, hMember⟩,
        hPredecessorValue⟩
    · rintro ⟨predecessor, _, hPredecessorCurrent,
        hPredecessorValue⟩
      rcases (hRelation predecessor current).mp
          hPredecessorCurrent with
        ⟨_, _, leftOrdinal, rightOrdinal,
          hLeftValue, hRightValue, hMember⟩
      have hLeftEq :=
        hInverse.1.1.1.2 predecessor
          leftOrdinal member hLeftValue hPredecessorValue
      have hRightEq :=
        hInverse.1.1.1.2 current
          rightOrdinal value hRightValue hCurrentValue
      simpa [hLeftEq, hRightEq] using hMember
  exact ⟨carrier, relation, hCarrierSubset, hRelationOn,
    hOrder, inverse, hCollapse, hInverseRange⟩

end ZF

end SetTheory
end YesMetaZFC
