import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Numeral
import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.NatPairing

/-! # 编译图在标准自然数上的计算正确性

直接专门化任意模型数码表示，避免另维护一套标准历史证明。
标准对应和任意模型内部总性仍是分别命名的接口。
-/
namespace YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
open Logic FirstOrder Logic.Arithmetic Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false

theorem relation_standard_m (c : code_m) (x y : Nat) :
    relation_l (ℳ := standard_m) c x y ↔ eval_l c x = y := by
  have h (n : Nat) : Numeral.value_l (ℳ := standard_m) n = n :=
    (Numeral.eval_m Env.empty n).symm.trans (Arithmetic.numeral_eval_m Env.empty n)
  simpa only [h] using numeral_iff_m pa_models_m c x y

theorem standard_m (c : code_m) {Γ Δ : SortContext signature_m}
    (η : Env Arithmetic.standard_m Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (graph_m c s t).satisfies η ↔ eval_l c (s.eval η) = t.eval η :=
  (graph_sat_m c η s t).trans (relation_standard_m c _ _)

end YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
