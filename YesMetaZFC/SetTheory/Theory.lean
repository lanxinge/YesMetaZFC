import YesMetaZFC.SetTheory.Definitional.Project

/-!
# 项目原子核理论与语义蕴涵

理论只接收项目原子核的 Jech 句子。旧纯 `∈` 语义只在
`YesMetaZFC.SetTheory.Definitional.Audit` 中作为数学审计层使用。
-/

namespace YesMetaZFC
namespace SetTheory

universe u v

/-- 项目原子核理论是项目句子的谓词。 -/
abbrev Theory := Definitional.Project.Theory

namespace Theory

def empty : Theory :=
  fun _ => False

def singleton (sentence : Definitional.Project.Sentence) : Theory :=
  fun candidate => candidate = sentence

def insert (sentence : Definitional.Project.Sentence) (theory : Theory) :
    Theory :=
  fun candidate => candidate = sentence ∨ theory candidate

def union (left right : Theory) : Theory :=
  fun sentence => left sentence ∨ right sentence

end Theory

namespace Structure

/-- 一个结构满足项目句子：任意 free 环境下都满足其公式。 -/
def SatisfiesSentence (ℳ : SetTheory.Structure.{v})
    (sentence : Definitional.Project.Sentence) : Prop :=
  Definitional.Structure.SatisfiesSentence
    Definitional.Project.kernel ℳ sentence

/-- 项目句子语义通过项目公式的按需解释器读取。 -/
theorem satisfiesSentence_iff (ℳ : SetTheory.Structure.{v})
    (sentence : Definitional.Project.Sentence) :
    ℳ.SatisfiesSentence sentence ↔
      ∀ free : FreeVarId → ℳ.Domain,
        Definitional.Project.Formula.satisfies
          ({ bound := Fin.elim0, free := free } : Env ℳ 0)
          sentence.formula := by
  rfl

/-- 一个外延隶属结构满足项目理论中的全部句子。 -/
def Models (ℳ : SetTheory.Structure.{v}) (theory : Theory) : Prop :=
  Extensional ℳ ∧
    ∀ sentence, theory sentence → ℳ.SatisfiesSentence sentence

end Structure

/-- 固定模型 universe 的项目原子核语义蕴涵。 -/
def SemanticallyEntails (theory : Theory)
    (target : Definitional.Project.Sentence) : Prop :=
  ∀ ℳ : Structure.{v}, ℳ.Models theory → ℳ.SatisfiesSentence target

scoped infix:50 " ⊨ₛ " => SemanticallyEntails

namespace Theory

theorem entails_of_mem {theory : Theory}
    {target : Definitional.Project.Sentence}
    (hTarget : theory target) :
    SemanticallyEntails.{v} theory target := by
  intro ℳ hModels
  exact hModels.2 target hTarget

theorem entails_weaken {strong weak : Theory}
    {target : Definitional.Project.Sentence}
    (hSubset : ∀ sentence, weak sentence → strong sentence)
    (hEntails : SemanticallyEntails.{v} weak target) :
    SemanticallyEntails.{v} strong target := by
  intro ℳ hModels
  apply hEntails ℳ
  refine ⟨hModels.1, ?_⟩
  intro sentence hSentence
  exact hModels.2 sentence (hSubset sentence hSentence)

end Theory

end SetTheory
end YesMetaZFC
