import YesMetaZFC.SetTheory.Notation.Syntax
import YesMetaZFC.SetTheory.Definitional.Project.Ord.Syntax

/-!
# 序数纸面记号

序数记号扩展统一的纯集合论 surface syntax；其编译结果仍然只有原始隶属关系。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Surface

syntax:max "Trans" "(" setTerm ")" : setFormula
syntax:max "Ord" "(" setTerm ")" : setFormula
syntax:50 setTerm:51 " <ₒ " setTerm:51 : setFormula
syntax:50 setTerm:51 " ≤ₒ " setTerm:51 : setFormula

end Surface
end SetTheory
end YesMetaZFC
