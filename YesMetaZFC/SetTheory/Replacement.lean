import YesMetaZFC.SetTheory.Collection
import YesMetaZFC.SetTheory.FunctionSemantics
import YesMetaZFC.SetTheory.Separation

/-!
# 函数式替换的语义接口

ZF 当前以全收集加全分离为公理呈现。本文件把二者组合成精确函数像集，供递归、
函数图与后续替换论证直接消费。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace BinaryImageEmbedding

/-- 像集成员公式中，原二元模式的输出、输入与参数位置。 -/
def body {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 3) :=
  Fin.cases 1 <| Fin.cases 0 fun parameter =>
    ⟨parameter.val + 3, by omega⟩

end BinaryImageEmbedding

namespace Definitional.Project.BinarySchema

/-- 给定源集参数后，`output` 属于二元模式在源集上的关系像。 -/
def imageMembership {parameterCount : Nat}
    (schema : BinarySchema parameterCount) :
    UnarySchema (parameterCount + 1) where
  body :=
    Definitional.Project.Formula.existsMem (.bound 1) <|
      schema.body.rename BinaryImageEmbedding.body
  freeClosed := by
    simp [Definitional.Project.Formula.existsMem,
      Definitional.Formula.FreeClosed, schema.freeClosed]

end BinarySchema
end Project
end Definitional

namespace Definitional.Project.Formula

private theorem reindex_binaryImageBody {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (source output input : ℳ.Domain) :
    (((env.push source).push output).push input).reindex
        (BinaryImageEmbedding.body
          (parameterCount := parameterCount)) =
      (env.push input).push output := by
  rw [Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry
    · rfl
    · refine Fin.cases ?_ (fun parameter => ?_) previous <;> rfl
  · rfl

/-- 关系像成员模式与纸面的“存在源元素映到该输出”一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_imageMembership_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : Definitional.Project.BinarySchema parameterCount)
    (source output : ℳ.Domain) :
    satisfies ((env.push source).push output)
        schema.imageMembership.body ↔
      ∃ input, ℳ.mem input source ∧
        schema.denote env input output := by
  simp only [Definitional.Project.BinarySchema.imageMembership,
    satisfies_existsMem_iff]
  constructor
  · rintro ⟨input, hInput, hBody⟩
    refine ⟨input, hInput, ?_⟩
    rw [satisfies_rename] at hBody
    simpa only [reindex_binaryImageBody] using hBody
  · rintro ⟨input, hInput, hBody⟩
    refine ⟨input, hInput, ?_⟩
    rw [satisfies_rename]
    simpa only [reindex_binaryImageBody] using hBody

end Formula
end Project
end Definitional

namespace ZF

/--
在给定源集上全定义且单值的二元模式有精确像集。

这就是当前“收集 + 分离”公理呈现下可直接使用的函数式替换接口。
-/
theorem exists_functionalImageOn {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount)
    (env : Env ℳ parameterCount) (source : ℳ.Domain)
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output, schema.denote env input output)
    (hUnique : ∀ input, ℳ.mem input source → ∀ first second,
      schema.denote env input first →
      schema.denote env input second →
      first = second) :
    ∃ image, ∀ output,
      ℳ.mem output image ↔
        ∃ input, ℳ.mem input source ∧
          schema.denote env input output := by
  rcases SetTheory.ZF.exists_collection hZF schema env source
      (by simpa [Definitional.Project.BinarySchema.denote] using hTotal) with
    ⟨collection, hCollection⟩
  rcases SetTheory.ZF.exists_separation hZF schema.imageMembership
      (env.push source) collection with
    ⟨image, hImage⟩
  refine ⟨image, fun output => ?_⟩
  rw [hImage output,
    Definitional.Project.Formula.satisfies_imageMembership_iff
      env schema source output]
  constructor
  · rintro ⟨_, input, hInput, hOutput⟩
    exact ⟨input, hInput, hOutput⟩
  · rintro ⟨input, hInput, hOutput⟩
    rcases hCollection input hInput with
      ⟨selected, hSelectedMem, hSelected⟩
    have hSelected' : schema.denote env input selected := by
      simpa [Definitional.Project.BinarySchema.denote] using hSelected
    have hEq :=
      hUnique input hInput output selected hOutput hSelected'
    subst selected
    exact ⟨hSelectedMem, input, hInput, hOutput⟩

/-- 全定义且全域单值的模式在任意源集上有精确像集。 -/
theorem exists_functionalImage {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount)
    (env : Env ℳ parameterCount) (source : ℳ.Domain)
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output, schema.denote env input output)
    (hUnique : ∀ input first second,
      schema.denote env input first →
      schema.denote env input second →
      first = second) :
    ∃ image, ∀ output,
      ℳ.mem output image ↔
        ∃ input, ℳ.mem input source ∧
          schema.denote env input output :=
  exists_functionalImageOn hZF schema env source hTotal
    fun input _ => hUnique input

end ZF

end SetTheory
end YesMetaZFC
