import YesMetaZFC.Model.SetTheory.LevyReflection.Decode

/-! # 原 ZF 中的 Lévy 有限公式反射定理

任意有限原公式族和任意集合 A 都有一个包含 A 的实际累积层 V_α，同时反射
各公式的全部层内参数。内部 ω 递归、见证收集和秩界都已构造，不添加反射公理。
公式族是给定的有限生产语法；结论不声称某一层初等于整个集合宇宙。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

abbrev Lr_formula := Σ n, {φ : Formula 1 n // φ.FreeClosed}

include I in
theorem ZF.lr_finite_l (hZF : M.Models ZF) (Φ : List Lr_formula) (A : M.Domain) :
    ∃ α X, V_d I α X ∧ M.mem A X ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val X := by
  obtain ⟨ω, hω⟩ := exists_omega hZF
  obtain ⟨α, X, hV, hAX, hc⟩ := lr_closed_layer_l I hZF hω
    (Φ.flatMap (fun q : Lr_formula => @lr_queries_l q.1 q.2.val q.2.property)) A
  refine ⟨α, X, hV, hAX, fun q hq ρ hρ => ?_⟩
  exact lr_reflect_core_l q.2.val q.2.property
    (fun r hr => hc r (List.mem_flatMap.mpr ⟨q, hq, hr⟩))
    ρ (ρ.push X) .newest (fun i => .bound i.succ) rfl (fun _ => rfl) hρ

/-- 单公式调用自动处理其全部量词子公式与反例，无须调用者提供子公式闭包。 -/
theorem ZF.lr_reflect_l (hZF : M.Models ZF) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (A : M.Domain) :
    ∃ α X, V_d I α X ∧ M.mem A X ∧ Lr_reflect_d φ X := by
  obtain ⟨α, X, hV, hAX, h⟩ := lr_finite_l I hZF [⟨n, φ, hφ⟩] A
  exact ⟨α, X, hV, hAX, h ⟨n, φ, hφ⟩ (List.mem_cons_self ..)⟩

end YesMetaZFC.SetTheory
