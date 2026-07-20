import YesMetaZFC.SetTheory.Axioms.ZF

/-!
# 收集模式的语义接口

本层把 ZF 与 KP 的收集公理整理为模型内可直接消费的纸面语义。输入集合中的每个元素
只要求在收集集合中找到一个对应输出；函数性和精确像集由后续替换/分离论证负责。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Axioms.Schema

/-- 收集核心公式恰好给出输入集合上所有输出的一个共同上界集合。 -/
theorem satisfies_collectionCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : Definitional.Project.BinarySchema parameterCount) :
    Definitional.Project.Formula.satisfies env (collectionCore schema) ↔
      ∀ source,
        (∀ input, ℳ.mem input source →
          ∃ output,
            Definitional.Project.Formula.satisfies ((env.push input).push output)
              schema.body) →
        ∃ collection, ∀ input, ℳ.mem input source →
          ∃ output, ℳ.mem output collection ∧
            Definitional.Project.Formula.satisfies ((env.push input).push output)
              schema.body := by
  simp only [collectionCore,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff,
    Definitional.Project.Formula.satisfies_forallMem_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_existsMem_iff]
  constructor
  · intro h source hTotal
    have hAntecedent :
        ∀ input, ℳ.mem input source →
          ∃ output,
            Definitional.Project.Formula.satisfies
              (((env.push source).push input).push output)
                (schema.body.rename
                  BoundEmbedding.binaryUnderOne) := by
      intro input hInput
      rcases hTotal input hInput with ⟨output, hOutput⟩
      refine ⟨output, ?_⟩
      rw [Definitional.Project.Formula.satisfies_rename]
      simpa only [Env.reindex_push_binaryUnderOne] using hOutput
    rcases h source hAntecedent with ⟨collection, hCollection⟩
    refine ⟨collection, fun input hInput => ?_⟩
    rcases hCollection input hInput with
      ⟨output, hOutputMem, hOutput⟩
    refine ⟨output, hOutputMem, ?_⟩
    rw [Definitional.Project.Formula.satisfies_rename] at hOutput
    simpa only [Env.reindex_push_binaryUnderTwo] using hOutput
  · intro h source hAntecedent
    have hTotal :
        ∀ input, ℳ.mem input source →
          ∃ output,
            Definitional.Project.Formula.satisfies
              ((env.push input).push output) schema.body := by
      intro input hInput
      rcases hAntecedent input hInput with ⟨output, hOutput⟩
      refine ⟨output, ?_⟩
      rw [Definitional.Project.Formula.satisfies_rename] at hOutput
      simpa only [Env.reindex_push_binaryUnderOne] using hOutput
    rcases h source hTotal with ⟨collection, hCollection⟩
    refine ⟨collection, fun input hInput => ?_⟩
    rcases hCollection input hInput with
      ⟨output, hOutputMem, hOutput⟩
    refine ⟨output, hOutputMem, ?_⟩
    rw [Definitional.Project.Formula.satisfies_rename]
    simpa only [Env.reindex_push_binaryUnderTwo] using hOutput

end Axioms.Schema

namespace ZF

/-- ZF 收集任意二元公式模式在输入集合上的一组见证。 -/
theorem exists_collection {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount)
    (env : Env ℳ parameterCount) (source : ℳ.Domain)
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output,
        Definitional.Project.Formula.satisfies ((env.push input).push output)
          schema.body) :
    ∃ collection, ∀ input, ℳ.mem input source →
      ∃ output, ℳ.mem output collection ∧
        Definitional.Project.Formula.satisfies ((env.push input).push output)
          schema.body := by
  have hSentence :=
    hZF.2 (Axioms.Schema.collection schema)
      (Axiom.collection schema) env.free
  have hCore :
      Definitional.Project.Formula.satisfies env
        (Axioms.Schema.collectionCore schema) := by
    have hAll :=
      (Definitional.Project.Formula.satisfies_forallClosure_iff env.free
        (Axioms.Schema.collectionCore schema)).mp hSentence
    simpa only using hAll env.bound
  exact
    (Axioms.Schema.satisfies_collectionCore_iff env schema).mp
      hCore source hTotal

end ZF

namespace KP

/-- KP 收集带 `Δ₀` 证据的二元公式模式。 -/
theorem exists_collection {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    {parameterCount : Nat}
    (schema : Definitional.Project.Delta0BinarySchema parameterCount)
    (env : Env ℳ parameterCount) (source : ℳ.Domain)
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output,
        Definitional.Project.Formula.satisfies ((env.push input).push output)
          schema.body) :
    ∃ collection, ∀ input, ℳ.mem input source →
      ∃ output, ℳ.mem output collection ∧
        Definitional.Project.Formula.satisfies ((env.push input).push output)
          schema.body := by
  have hSentence :=
    hKP.2
      (Axioms.Schema.collection schema.toBinarySchema)
      (Axiom.collection schema) env.free
  have hCore :
      Definitional.Project.Formula.satisfies env
        (Axioms.Schema.collectionCore
          schema.toBinarySchema) := by
    have hAll :=
      (Definitional.Project.Formula.satisfies_forallClosure_iff env.free
        (Axioms.Schema.collectionCore
          schema.toBinarySchema)).mp hSentence
    simpa only using hAll env.bound
  exact
    (Axioms.Schema.satisfies_collectionCore_iff
      env schema.toBinarySchema).mp hCore source hTotal

end KP

end SetTheory
end YesMetaZFC
