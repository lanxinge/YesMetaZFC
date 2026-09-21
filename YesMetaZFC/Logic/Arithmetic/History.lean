import YesMetaZFC.Logic.Arithmetic.Beta

/-! # 原始递归的有限计算历史公式

F 给出初值，G 给出带参数和时刻的下一状态。历史长度与 β 码都是对象数目项。
-/
namespace YesMetaZFC.Logic.Arithmetic.History
open FirstOrder
set_option autoImplicit false

abbrev binary_m := ∀ {Γ Δ : SortContext signature_m},
  Term signature_m Γ Δ .num → Term signature_m Γ Δ .num → Formula signature_m Γ Δ

abbrev quaternary_m := ∀ {Γ Δ : SortContext signature_m},
  Term signature_m Γ Δ .num → Term signature_m Γ Δ .num →
  Term signature_m Γ Δ .num → Term signature_m Γ Δ .num → Formula signature_m Γ Δ

def initial_m (F : binary_m) {Γ Δ : SortContext signature_m} (b c x : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .existsE .num (.conj
  (F (x.weakenBound sort_m.num) (.bvar .here))
  (Beta.graph_m (b.weakenBound sort_m.num) (c.weakenBound sort_m.num) zero_m (.bvar .here)))

def transition_m (G : quaternary_m) {Γ Δ : SortContext signature_m}
    (b c x i : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (Beta.graph_m ((b.weakenBound sort_m.num).weakenBound sort_m.num)
      ((c.weakenBound sort_m.num).weakenBound sort_m.num)
      ((i.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)))
    (.conj (Beta.graph_m ((b.weakenBound sort_m.num).weakenBound sort_m.num)
      ((c.weakenBound sort_m.num).weakenBound sort_m.num)
      (succ_m ((i.weakenBound sort_m.num).weakenBound sort_m.num)) (.bvar .here))
      (G ((x.weakenBound sort_m.num).weakenBound sort_m.num)
        ((i.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here)))))

def steps_m (G : quaternary_m) {Γ Δ : SortContext signature_m}
    (b c x n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.imp (lt_m (.bvar .here) (n.weakenBound sort_m.num))
    (transition_m G (b.weakenBound sort_m.num) (c.weakenBound sort_m.num)
      (x.weakenBound sort_m.num) (.bvar .here)))

def graph_m (F : binary_m) (G : quaternary_m) {Γ Δ : SortContext signature_m}
    (x n y : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (initial_m F (.bvar (.there .here)) (.bvar .here)
      ((x.weakenBound sort_m.num).weakenBound sort_m.num))
    (.conj (Beta.graph_m (.bvar (.there .here)) (.bvar .here)
      ((n.weakenBound sort_m.num).weakenBound sort_m.num)
      ((y.weakenBound sort_m.num).weakenBound sort_m.num))
      (steps_m G (.bvar (.there .here)) (.bvar .here)
        ((x.weakenBound sort_m.num).weakenBound sort_m.num)
        ((n.weakenBound sort_m.num).weakenBound sort_m.num)))))

end YesMetaZFC.Logic.Arithmetic.History
