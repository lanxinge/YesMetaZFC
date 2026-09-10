import YesMetaZFC.Automation.ObjectDiagonalFixedPoint
import YesMetaZFC.Automation.ObjectParameterDiagonal

/-! # 当前 quotation 下的实际 liar 固定点

候选真谓词允许任意有限参数列；在对应的原自代入构造中代入其否定。
原无参数闭句入口保持独立，`Parameters` 导出保留参数的开放反例。
-/
namespace YesMetaZFC.Automation.ObjectTarski
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def negativeTemplate_m (P : FormulaTemplate.Unary) : FormulaTemplate.Unary := ⟨¬ₘ P.body⟩

theorem negative_apply_m (P : FormulaTemplate.Unary) {bound free : SetContext}
    (s : SetTerm bound free) : negativeTemplate_m P s = (¬ₘ P s) := rfl

/-- 由具体自代入算法生成句子，使用原码域和完整结构 quotation。 -/
def liarSentence_m (D : Delta0CodeDomain) (P : FormulaTemplate.Unary) : SetSentence :=
  ObjectDiagonal.fixedPoint D (negativeTemplate_m P)

theorem liar_fixed_point_m {T : SetTheory} (S : ObjectDiagonal.Support T)
    (P : FormulaTemplate.Unary) :
    Derives T [] (liarSentence_m S.core.code_domain P ↔ₘ
      ¬ₘ P (IntrinsicQuotation.quote (liarSentence_m S.core.code_domain P))) := by
  simpa only [liarSentence_m, negative_apply_m] using
    ObjectDiagonal.fixedPoint_spec S (negativeTemplate_m P)

namespace Parameters
variable {parameters : SetContext}

def liarFormula_m (D : Delta0CodeDomain) (P : ObjectDiagonal.ParameterFormula_m parameters) :
    SetOpenFormula parameters := ObjectParameterDiagonal.fixedPoint_m D (¬ₘ P)

theorem liar_fixed_point_m {T : SetTheory} (S : ObjectDiagonal.Support T)
    (P : ObjectDiagonal.ParameterFormula_m parameters) :
    Derives T [] (liarFormula_m S.core.code_domain P ↔ₘ
      ¬ₘ P.instantiateFreeTop (ObjectParameterDiagonal.quote_m (liarFormula_m S.core.code_domain P))) := by
  simpa only [liarFormula_m, Formula.instantiateFreeTop_neg] using
    ObjectParameterDiagonal.fixed_point_m S (¬ₘ P)

end Parameters

end YesMetaZFC.Automation.ObjectTarski
