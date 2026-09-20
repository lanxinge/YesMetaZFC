import YesMetaZFC.Model.Arithmetic.Pairing
import YesMetaZFC.Model.Arithmetic.Completeness

/-! # 配对正向图的纯逻辑可证性

原项及互补条件分支已保证正向总性和函数性，不要求 Q 或 PA。
本模块使用可选完备性桥，不进入基础入口。
-/
namespace YesMetaZFC.Model.Arithmetic.Pairing.Provability
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
variable {T : Theory signature_m} {Δ : SortContext signature_m} {Γ : Context signature_m Δ}

theorem total_m (m n : Term signature_m [] Δ .num) :
    Derives T Γ (Logic.Arithmetic.Pairing.domain_m m n) := by
  apply Completeness.derives_m
  intro ℳ _ η
  exact (domain_sat_m η m n).mpr ⟨_, rfl⟩

theorem functional_m (m n p q : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (Logic.Arithmetic.Pairing.graph_m m n p)
      (.imp (Logic.Arithmetic.Pairing.graph_m m n q) (.equal p q))) := by
  apply Completeness.derives_m
  intro ℳ _ η
  simp only [Formula.satisfies, graph_sat_m]
  exact fun h₁ h₂ => h₁.symm.trans h₂

end YesMetaZFC.Model.Arithmetic.Pairing.Provability
