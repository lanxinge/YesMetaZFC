import YesMetaZFC.SetTheory.Axioms.ZF

/-!
# 分离模式的语义接口与常用集合构造

本层先把任意一元公式模式的分离公理整理为稳定的语义接口；ZF 消费任意模式，KP
消费带 `Δ₀` 证据的模式。差集与交集等常用构造继续作为 KP 的具体实例提供。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Axioms.Schema

/-- 分离核心公式恰好给出原集合中满足 schema 的子集。 -/
theorem satisfies_separationCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : Definitional.Project.UnarySchema parameterCount) :
    Definitional.Project.Formula.satisfies env (separationCore schema) ↔
      ∀ source, ∃ subset, ∀ value,
        ℳ.mem value subset ↔
          ℳ.mem value source ∧
            Definitional.Project.Formula.satisfies (env.push value) schema.body := by
  simp only [separationCore,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_iff_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Term.eval]
  constructor
  · intro h source
    rcases h source with ⟨subset, hSubset⟩
    refine ⟨subset, fun value => ?_⟩
    have hValue := hSubset value
    rw [Definitional.Project.Formula.satisfies_rename] at hValue
    simpa only [Env.reindex_push_unaryUnderTwo] using hValue
  · intro h source
    rcases h source with ⟨subset, hSubset⟩
    refine ⟨subset, fun value => ?_⟩
    rw [Definitional.Project.Formula.satisfies_rename]
    simpa only [Env.reindex_push_unaryUnderTwo] using hSubset value

end Axioms.Schema

namespace ZF

/-- ZF 分离任意公式模式在给定参数环境下定义的子类。 -/
theorem exists_separation {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat}
    (schema : Definitional.Project.UnarySchema parameterCount)
    (env : Env ℳ parameterCount) (source : ℳ.Domain) :
    ∃ subset, ∀ value,
      ℳ.mem value subset ↔
        ℳ.mem value source ∧
          Definitional.Project.Formula.satisfies (env.push value) schema.body := by
  have hSentence :=
    hZF.2 (Axioms.Schema.separation schema)
      (Axiom.separation schema) env.free
  have hCore :
      Definitional.Project.Formula.satisfies env
        (Axioms.Schema.separationCore schema) := by
    have hAll :=
      (Definitional.Project.Formula.satisfies_forallClosure_iff env.free
        (Axioms.Schema.separationCore schema)).mp hSentence
    simpa only using hAll env.bound
  exact
    (Axioms.Schema.satisfies_separationCore_iff env schema).mp
      hCore source

end ZF

namespace KP

/-- KP 分离带 `Δ₀` 证据的公式模式。 -/
theorem exists_separation {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    {parameterCount : Nat}
    (schema : Definitional.Project.Delta0UnarySchema parameterCount)
    (env : Env ℳ parameterCount) (source : ℳ.Domain) :
    ∃ subset, ∀ value,
      ℳ.mem value subset ↔
        ℳ.mem value source ∧
          Definitional.Project.Formula.satisfies (env.push value) schema.body := by
  have hSentence :=
    hKP.2
      (Axioms.Schema.separation schema.toUnarySchema)
      (Axiom.separation schema) env.free
  have hCore :
      Definitional.Project.Formula.satisfies env
        (Axioms.Schema.separationCore schema.toUnarySchema) := by
    have hAll :=
      (Definitional.Project.Formula.satisfies_forallClosure_iff env.free
        (Axioms.Schema.separationCore schema.toUnarySchema)).mp
          hSentence
    simpa only using hAll env.bound
  exact
    (Axioms.Schema.satisfies_separationCore_iff
      env schema.toUnarySchema).mp hCore source

/-- 固定右参数后，从给定集合中分离出不属于右参数的元素。 -/
def differenceSchema : Definitional.Project.Delta0UnarySchema 1 where
  body := .neg (.mem (.bound 0) (.bound 1))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed]
  delta0 := .neg (.mem _ _)

/-- KP 中任意两个集合都有差集。 -/
theorem exists_difference {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (left right : ℳ.Domain) :
    ∃ difference, ∀ value,
      ℳ.mem value difference ↔
        ℳ.mem value right ∧ ¬ ℳ.mem value left := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases KP.exists_separation hKP differenceSchema env right with
    ⟨difference, hDifference⟩
  refine ⟨difference, fun value => ?_⟩
  simpa [differenceSchema, Definitional.Project.Formula.satisfies,
    Definitional.Semantics.satisfies, Definitional.Term.eval, Env.push, env] using
      hDifference value

/-- 固定右参数后，从给定集合中分离出同时属于右参数的元素。 -/
def intersectionSchema : Definitional.Project.Delta0UnarySchema 1 where
  body := .mem (.bound 0) (.bound 1)
  freeClosed := by
    simp [Definitional.Formula.FreeClosed]
  delta0 := .mem _ _

/-- KP 中任意两个集合都有交集。 -/
theorem exists_intersection {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (left right : ℳ.Domain) :
    ∃ intersection, ∀ value,
      ℳ.mem value intersection ↔
        ℳ.mem value left ∧ ℳ.mem value right := by
  let env : Env ℳ 1 := {
    bound := fun _ => right
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases KP.exists_separation hKP intersectionSchema env left with
    ⟨intersection, hIntersection⟩
  refine ⟨intersection, fun value => ?_⟩
  simpa [intersectionSchema, Definitional.Project.Formula.satisfies,
    Definitional.Semantics.satisfies, Definitional.Term.eval, Env.push, env] using
      hIntersection value

end KP

end SetTheory
end YesMetaZFC
