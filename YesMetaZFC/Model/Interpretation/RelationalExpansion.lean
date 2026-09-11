import YesMetaZFC.Model.Interpretation.RelationalSemantics
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # 由函数图的存在唯一性构造模型扩张

元层选择只构造模型解释函数，不向对象语言加入选择算子或新公理。
关系符号直接按其定义解释；一般语义正确性随后把全部源推导传到目标模型。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
universe x
variable {σ τ : Signature.{0, 0, 0}}

/-- 函数图对任意对象参数都有且仅有一个输出。 -/
def Functional (I : Interpretation σ τ) (M : Structure.{0, 0, 0, x} τ) : Prop :=
  ∀ symbol (args : Values (fun sort => M.Carrier (I.sort sort)) (σ.funcDomain symbol)),
    ∃ output, (I.function symbol).satisfies (templateEnv (.cons output (mapValues I args))) ∧
      ∀ other, (I.function symbol).satisfies (templateEnv (.cons other (mapValues I args))) → other = output

/-- 从已证明存在唯一的图取其模型解释；不需要额外源模型参数。 -/
noncomputable def expansion {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (h : Functional I M) : Expansion I M where
  function symbol args := Classical.choose (h symbol args)
  relation symbol args := (I.relation symbol).satisfies (templateEnv (mapValues I args))

/-- 上述实际构造实现全部函数和关系的定义图。 -/
theorem expansion_realizes {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (h : Functional I M) : Realizes (expansion h) where
  function symbol args output := by
    obtain ⟨hExists, hUnique⟩ := Classical.choose_spec (h symbol args)
    constructor
    · exact hUnique output
    · intro hEq
      exact hEq ▸ hExists
  relation _ _ := Iff.rfl

/-- 理论逐句翻译后的像，不把模型实现条件混入源理论。 -/
def theory (I : Interpretation σ τ) (T : Theory σ) : Theory τ :=
  fun target => ∃ source, T source ∧ target = sentence I source

/-- 全部翻译公理为真当且仅当源扩张满足原理论。 -/
theorem models_iff {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (h : Functional I M) (T : Theory σ) :
    Theory.Models M (theory I T) ↔ Theory.Models (expansion h).model T := by
  constructor
  · intro hModels source hSource
    exact (sentence_correct (expansion h) (expansion_realizes h) source).mp
      (hModels _ ⟨source, hSource, rfl⟩)
  · intro hModels target hTarget
    obtain ⟨source, hSource, rfl⟩ := hTarget
    exact (sentence_correct (expansion h) (expansion_realizes h) source).mpr (hModels source hSource)

/-- 任意普通源 Hilbert 推导在满足翻译公理的目标模型中成立。 -/
theorem derives_sound {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (h : Functional I M) {T : Theory σ} {input : Sentence σ}
    (hDerives : Derives T [] input) (hModels : Theory.Models M (theory I T)) :
    (sentence I input).TrueIn M :=
  (sentence_correct (expansion h) (expansion_realizes h) input).mpr
    (hDerives.semantically_entails (expansion h).model ((models_iff h T).mp hModels))

end YesMetaZFC.Automation.RelationalTranslation
