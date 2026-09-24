import YesMetaZFC.Logic.Arithmetic.Signature
import YesMetaZFC.Model.Henkin.OpenCompleteness
import YesMetaZFC.Model.Henkin.SyntaxNatCoding

/-! # 算术语言的可选完备性接口

有限符号编码实际生成公平 Henkin 调度。这里只从所有模型中的真值
取得原 Derives，不把标准模型真值反射为可证性；核心入口不导入本模块。
-/
namespace YesMetaZFC.Model.Arithmetic.Completeness
open Logic FirstOrder Logic.Arithmetic
open FirstOrder.Completeness.Henkin Automation.SyntaxNatCoding
set_option autoImplicit false

def function_coding_m : NatCoding func_m where
  encode | .zero => 0 | .succ => 1 | .add => 2 | .mul => 3
  injective := by intro f g h; cases f <;> cases g <;> simp_all

def coding_m : SymbolCoding signature_m where
  sort := ⟨fun _ => 0, by intro s t _; cases s; cases t; rfl⟩
  function := function_coding_m
  relation := ⟨(fun r => nomatch r), by intro r; cases r⟩

theorem derives_m {T : Theory signature_m} {Δ : SortContext signature_m}
    {Γ : Context signature_m Δ} {φ : OpenFormula signature_m Δ}
    (h : ∀ (ℳ : Structure.{0, 0, 0, 0} signature_m), Theory.Models ℳ T →
      ∀ η : Env ℳ [] Δ, φ.satisfies η) : Derives T Γ φ :=
  Derives.context_weaken (Γ := []) (by intro φ hφ; cases hφ)
    (Automation.SemanticTransfer.derives_open_m (schedule coding_m) h)

end YesMetaZFC.Model.Arithmetic.Completeness
