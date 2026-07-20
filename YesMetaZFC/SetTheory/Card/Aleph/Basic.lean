import YesMetaZFC.SetTheory.Card.Aleph.Syntax
import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion

/-!
# Aleph 数的基础语义

本层把 Aleph 相关公式解释为普通 Lean 谓词，并把 Aleph 枚举接入现有超限递归内核。
这里只建立定义和语义桥，不证明基数后继存在性、Aleph 枚举存在唯一性或后续算术律。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `κ` 是相对于 `ω` 的无限基数。 -/
def IsInfiniteCardinal {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω κ : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 κ ∧
    ℳ.CardinalLessOrEqual 𝕀 ω κ

/-- `set` 与 `ω` 等势，即 `set` 是可数无限集。 -/
def IsCountablyInfinite {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω set : ℳ.Domain) : Prop :=
  ℳ.Equinumerous 𝕀 set ω

/-- `set` 的基数不超过 `ω`。 -/
def IsAtMostCountable {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω set : ℳ.Domain) : Prop :=
  ℳ.CardinalLessOrEqual 𝕀 set ω

/--
`successor` 是严格大于 `predecessor` 的最小基数。

这里使用初始序数的隶属次序表达“严格大于”和最小性。
-/
def IsCardinalSuccessor {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (successor predecessor : ℳ.Domain) : Prop :=
  ℳ.IsCardinal 𝕀 successor ∧
    ℳ.mem predecessor successor ∧
      ∀ candidate,
        ℳ.IsCardinal 𝕀 candidate →
          ℳ.mem predecessor candidate →
            successor = candidate ∨
              ℳ.mem successor candidate

/-- 基数后继在非序数输入上的空集总化。 -/
def IsAlephSuccessorOperation {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (previous output : ℳ.Domain) : Prop :=
  (ℳ.IsOrdinal previous ∧
      ℳ.IsCardinalSuccessor 𝕀 output previous) ∨
    (¬ ℳ.IsOrdinal previous ∧
      ∀ value, ¬ ℳ.mem value output)

/-- 以 `ω` 为首项、后继处取基数后继、极限处取并的 Aleph 递归步。 -/
def IsAlephStep {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω sequence output : ℳ.Domain) : Prop :=
  ℳ.IsZeroSuccessorLimitStep 𝕀
    (fun initial => initial = ω)
    (ℳ.IsAlephSuccessorOperation 𝕀)
    sequence output

/-- `aleph` 是以 `ω` 为首项的 Aleph 枚举在 `index` 处的递归值。 -/
def IsAlephNumber {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω index aleph : ℳ.Domain) : Prop :=
  ℳ.IsRecursionValue 𝕀
    (ℳ.IsAlephStep 𝕀 ω) index aleph

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- 无限基数公式与纸面定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isInfiniteCardinal_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω κ : Term depth) :
    satisfies env (isInfiniteCardinal 𝒞 ω κ) ↔
      ℳ.IsInfiniteCardinal 𝕀
        (ω.eval env) (κ.eval env) := by
  simp only [isInfiniteCardinal, Structure.IsInfiniteCardinal,
    satisfies_conj_iff,
    satisfies_isCardinal_iff 𝕀 hExt,
    satisfies_cardinalLessOrEqual_iff 𝕀 hExt]

/-- 可数无限公式与纸面等势定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCountablyInfinite_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω set : Term depth) :
    satisfies env (isCountablyInfinite 𝒞 ω set) ↔
      ℳ.IsCountablyInfinite 𝕀
        (ω.eval env) (set.eval env) := by
  simp only [isCountablyInfinite, Structure.IsCountablyInfinite,
    satisfies_equinumerous_iff 𝕀 hExt]

/-- 至多可数公式与纸面基数比较定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isAtMostCountable_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω set : Term depth) :
    satisfies env (isAtMostCountable 𝒞 ω set) ↔
      ℳ.IsAtMostCountable 𝕀
        (ω.eval env) (set.eval env) := by
  simp only [isAtMostCountable, Structure.IsAtMostCountable,
    satisfies_cardinalLessOrEqual_iff 𝕀 hExt]

/-- 基数后继公式与最小严格更大基数的纸面定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCardinalSuccessor_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (successor predecessor : Term depth) :
    satisfies env
        (isCardinalSuccessor 𝒞 successor predecessor) ↔
      ℳ.IsCardinalSuccessor 𝕀
        (successor.eval env) (predecessor.eval env) := by
  simp only [isCardinalSuccessor, Structure.IsCardinalSuccessor,
    satisfies_conj_iff, satisfies_mem_iff,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_disj_iff,
    satisfies_isCardinal_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hSuccessorCardinal, hStrict, hLeast⟩
    exact ⟨hSuccessorCardinal, hStrict,
      fun candidate hCandidateCardinal hCandidateStrict =>
        hLeast candidate ⟨hCandidateCardinal, hCandidateStrict⟩⟩
  · rintro ⟨hSuccessorCardinal, hStrict, hLeast⟩
    exact ⟨hSuccessorCardinal, hStrict,
      fun candidate hCandidate =>
        hLeast candidate hCandidate.1 hCandidate.2⟩

end Formula

namespace BinarySchema

/-- Aleph 递归算子的 schema 解释与纸面三分支定义一致。 -/
@[prove_auto_norm semantic]
theorem denote_alephOperator_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (sequence output : ℳ.Domain) :
    (alephOperator 𝒞).denote env sequence output ↔
      ℳ.IsAlephStep 𝕀
        (env.bound 0) sequence output := by
  simp only [alephOperator, denote,
    Structure.IsAlephStep,
    Structure.IsZeroSuccessorLimitStep,
    Structure.IsAlephSuccessorOperation,
    Formula.satisfies_disj_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,
    Formula.satisfies_neg_iff,
    Formula.satisfies_isZeroLengthSequence_iff 𝕀 hExt,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff
      𝕀 hExt,
    Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isCardinalSuccessor_iff 𝕀 hExt,
    Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_newest]
  rfl

/-- Aleph 类关系的 schema 解释与纸面递归值定义一致。 -/
@[prove_auto_norm semantic]
theorem denote_aleph_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (index value : ℳ.Domain) :
    (aleph 𝒞).denote env index value ↔
      ℳ.IsAlephNumber 𝕀
        (env.bound 0) index value := by
  have hOperator :
      (alephOperator 𝒞).denote env =
        ℳ.IsAlephStep 𝕀 (env.bound 0) := by
    funext sequence output
    apply propext
    exact denote_alephOperator_iff
      𝕀 hExt env sequence output
  rw [aleph]
  rw [Formula.denote_transfiniteRecursion_iff
    𝕀 hExt env (alephOperator 𝒞) index value]
  rw [hOperator]
  rfl

end BinarySchema

namespace Formula

/-- Aleph 数公式与纸面递归值定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isAlephNumber_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω index aleph : Term depth) :
    satisfies env
        (isAlephNumber 𝒞 ω index aleph) ↔
      ℳ.IsAlephNumber 𝕀
        (ω.eval env) (index.eval env) (aleph.eval env) := by
  rw [isAlephNumber, satisfies_related_iff]
  exact BinarySchema.denote_aleph_iff
    𝕀 hExt ((TermVector.singleton ω).evalEnv env)
      (index.eval env) (aleph.eval env)

end Formula

end Project
end Definitional
end SetTheory
end YesMetaZFC
