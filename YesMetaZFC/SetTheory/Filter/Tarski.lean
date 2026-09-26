import YesMetaZFC.SetTheory.Filter

/-!
# 滤子超滤扩张与 Zorn 原理

对固定基滤子，包含它的真滤子在包含关系下的非空链可以取并作上界。
因此一般的极大性原理推出 Tarski 超滤扩张定理。本文件将该原理作为显式
命题前提；这里不加入全局公理，也不声称已经从 Lean 的选择公理推出 Zorn。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Filter

universe u

/-- 子滤子族按包含关系成链。 -/
def IsChain {α : Type u} (C : Filter α → Prop) : Prop :=
  ∀ F G, C F → C G → Extends F G ∨ Extends G F

/-- `U` 是 `C` 关于滤子包含关系的上界。 -/
def IsUpperBound {α : Type u} (C : Filter α → Prop) (U : Filter α) : Prop :=
  ∀ F, C F → Extends F U

/-- 滤子偏序上的非空链版 Zorn 原理。 -/
def HasZornProperty (α : Type u) : Prop :=
  ∀ P : Filter α → Prop, (∃ F, P F) →
    (∀ C, (∀ F, C F → P F) → IsChain C → (∃ F, C F) →
      ∃ U, P U ∧ IsUpperBound C U) →
    ∃ U, P U ∧ ∀ G, P G → Extends U G → Extends G U

/-- 每个真滤子在显式滤子 Zorn 原理下都可扩张到极大真滤子。
证明通过链上滤子的并构造上界；未在此处隐藏地选择代表元。 -/
theorem tarski_filter_extension_of_zorn_l {α : Type u}
    (hZorn : HasZornProperty α) (F : Filter α) (hF : Proper F) :
    ∃ U : Filter α, IsUltrafilter U ∧ Extends F U := by
  let P : Filter α → Prop := fun G => Proper G ∧ Extends F G
  have hNonempty : ∃ G, P G := ⟨F, hF, fun _ h => h⟩
  have hChainBound : ∀ C, (∀ G, C G → P G) → IsChain C →
      (∃ G, C G) → ∃ U, P U ∧ IsUpperBound C U := by
    intro C hC hChain hCn
    rcases hCn with ⟨G₀, hG₀⟩
    let U : Filter α := {
      sets := fun s => ∃ G, C G ∧ G.sets s
      univ_mem := ⟨G₀, hG₀, G₀.univ_mem⟩
      upward := by
        intro s t hs hst
        rcases hs with ⟨G, hG, hGs⟩
        exact ⟨G, hG, G.upward hGs hst⟩
      inter_mem := by
        intro s t hs ht
        rcases hs with ⟨G, hG, hGs⟩
        rcases ht with ⟨H, hH, hHt⟩
        rcases hChain G H hG hH with hGH | hHG
        · exact ⟨H, hH, H.inter_mem (hGH s hGs) hHt⟩
        · exact ⟨G, hG, G.inter_mem hGs (hHG t hHt)⟩
    }
    have hUProper : Proper U := by
      intro hEmpty
      rcases hEmpty with ⟨G, hG, hGEmpty⟩
      exact (hC G hG).1 hGEmpty
    have hUExtends : Extends F U := by
      intro s hs
      exact ⟨G₀, hG₀, (hC G₀ hG₀).2 s hs⟩
    refine ⟨U, ⟨hUProper, hUExtends⟩, ?_⟩
    intro G hG s hs
    exact ⟨G, hG, hs⟩
  rcases hZorn P hNonempty hChainBound with ⟨U, hU, hMax⟩
  have hMaxProper : IsMaximalProper U := by
    refine ⟨hU.1, ?_⟩
    intro G hUG hG s hs
    have hPG : P G := ⟨hG, fun t ht => hUG t (hU.2 t ht)⟩
    exact hMax G hPG hUG s hs
  exact ⟨U, hMaxProper, hU.2⟩

end Filter
end SetTheory
end YesMetaZFC
