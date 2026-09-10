import YesMetaZFC.Automation.ObjectNumeralReflection

/-! # 固定自由上下文的数码参数槽位

有效位置使用自由变量，越界位置填零的数码；不改变公式的实际自由变量。
-/
namespace YesMetaZFC.Automation.ObjectCodeParameters
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def terms : (free : SetContext) → Nat → SetOpenTerm free
  | .nil, _ => numₘ(ObjectNumeralSyntax.zeroCode)
  | .set :: free, index => ObjectCodeInstantiation.prepend (.fvar .here)
      (fun i => (terms free i).weakenFree SetSort.set) index

end YesMetaZFC.Automation.ObjectCodeParameters
