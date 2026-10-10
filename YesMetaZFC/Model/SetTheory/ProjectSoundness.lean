import YesMetaZFC.Model.SetTheory.ProjectSemantics
import YesMetaZFC.Model.Semantics.Background

/-! # 任意 Project 模型直接接入原推导核

保留对象域与隶属关系，构造纯一阶结构，再使用已有逐公式语义对应和六规则可靠性。
模型不要求可数、外部良基或标准；构造不选择对象或表示。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
universe u

def model_l (M : SetTheory.Structure.{u}) : Logic.FirstOrder.Structure.{0,0,0,u} ℒ where
  Carrier _ := M.Domain
  nonempty _ := M.nonempty
  funcInterp f := nomatch f
  relInterp | .membership, .cons x (.cons y .nil) => M.mem x y

theorem model_models_l {M : SetTheory.Structure.{u}} {T : SetTheory.Theory} (hM : M.Models T) :
    Logic.FirstOrder.Theory.Models (model_l M) (fo_theory T) :=
  (models_iff (ℳ := model_l M) hM.1 T).mpr hM

/-- 原 Project 可推导句子在每个实际 Project 模型中成立。 -/
theorem sound_l {M : SetTheory.Structure.{u}} {T : SetTheory.Theory} (hM : M.Models T)
    {s : Project.Sentence} (h : Project.Derives T s) : M.SatisfiesSentence s :=
  (sentence_correct (ℳ := model_l M) hM.1 s).mp
    (Logic.FirstOrder.Derives.semantically_entails h (model_l M) (model_models_l hM))

/-- 实际模型直接给出原 Project 理论的一致性。 -/
theorem consistent_l {M : SetTheory.Structure.{u}} {T : SetTheory.Theory} (hM : M.Models T) :
    Project.Consistent T := Model.Native.consistent (model_l M) (model_models_l hM)

end YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
