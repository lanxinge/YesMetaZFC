import YesMetaZFC.Logic.Arithmetic.Z2.Syntax
import YesMetaZFC.Model.Arithmetic.Completeness

/-! # 双排序算术的可选完备性接口

使用全部一阶双排序模型，而非只使用完全幂集模型。符号编码仅服务于
元层公平调度，不是对象算术内部的语法表示。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2.Completeness
open Logic FirstOrder Logic.Arithmetic.Z2
open Automation.SyntaxNatCoding
set_option autoImplicit false

def coding_m : SymbolCoding signature_m where
  sort := ⟨fun s => match s with | .num => 0 | .set => 1,
    by intro s t h; cases s <;> cases t <;> simp_all⟩
  function := Arithmetic.Completeness.function_coding_m
  relation := ⟨fun _ => 0, by intro r s _; cases r; cases s; rfl⟩

theorem derives_m {T : Theory signature_m} {Δ : SortContext signature_m}
    {Γ : Context signature_m Δ} {φ : OpenFormula signature_m Δ}
    (h : ∀ (ℳ : Structure.{0, 0, 0, 0} signature_m), Theory.Models ℳ T →
      ∀ η : Env ℳ [] Δ, φ.satisfies η) : Derives T Γ φ :=
  Derives.context_weaken (Γ := []) (by intro φ hφ; cases hφ)
    (Automation.SemanticTransfer.derives_open_m (schedule coding_m) h)

end YesMetaZFC.Model.Arithmetic.Z2.Completeness
