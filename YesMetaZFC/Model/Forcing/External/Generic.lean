import YesMetaZFC.Model.Forcing.Order.Density
import Init.Data.Nat.Lemmas

/-! # 条件滤子与可数稠密族

泛型性总是相对于明确给出的稠密族。递降序列直接生成滤子；Rasiowa–Sikorski
只在存在命题内部选择逐步加强，不导出不可计算的滤子实例。
-/

namespace YesMetaZFC.Model.Forcing
universe u v
variable {P : Type u} (R : PO_pre P)

structure PO_filter where
  mem : P → Prop
  inhabited : ∃ p, mem p
  upward : ∀ {p q}, mem p → R.le p q → mem q
  directed : ∀ {p q}, mem p → mem q → ∃ r, mem r ∧ R.le r p ∧ R.le r q

namespace PO_filter
variable {R}

def Meets_l (G : PO_filter R) (D : P → Prop) : Prop := ∃ p, G.mem p ∧ D p

def Generic_l (G : PO_filter R) (𝒟 : (P → Prop) → Prop) : Prop :=
  ∀ D, 𝒟 D → R.Dense_l D → G.Meets_l D

def principal_l (p : P) : PO_filter R where
  mem q := R.le p q
  inhabited := ⟨p, R.le_refl p⟩
  upward h k := R.le_trans h k
  directed h k := ⟨p, R.le_refl p, h, k⟩

theorem descending_le_l (s : Nat → P) (h : ∀ n, R.le (s (n+1)) (s n))
    {m n : Nat} (k : m ≤ n) : R.le (s n) (s m) := by
  induction k with
  | refl => exact R.le_refl _
  | @step n _ ih => exact R.le_trans (h n) ih

/-- 递降链的向上闭包；共同加强由两下标的最大值显式给出。 -/
def sequence_l (s : Nat → P) (h : ∀ n, R.le (s (n+1)) (s n)) : PO_filter R where
  mem p := ∃ n, R.le (s n) p
  inhabited := ⟨s 0, 0, R.le_refl _⟩
  upward := fun ⟨n, h⟩ k => ⟨n, R.le_trans h k⟩
  directed := by
    rintro p q ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨s (max m n), ⟨max m n, R.le_refl _⟩,
      R.le_trans (descending_le_l s h (Nat.le_max_left _ _)) hm,
      R.le_trans (descending_le_l s h (Nat.le_max_right _ _)) hn⟩

end PO_filter

/-- 从任意起始条件构造遇到给定可数稠密族的滤子。 -/
theorem generic_countable_l (D : Nat → P → Prop) (h : ∀ n, R.Dense_l (D n))
    (p : P) : ∃ G : PO_filter R, G.mem p ∧ ∀ n, G.Meets_l (D n) := by
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice fun n => Classical.axiomOfChoice (h n)
  let s : Nat → P := Nat.rec p (fun n q => f n q)
  have hs n : R.le (s (n+1)) (s n) := (hf n (s n)).1
  refine ⟨PO_filter.sequence_l s hs, ⟨0, R.le_refl p⟩, fun n => ?_⟩
  exact ⟨s (n+1), ⟨n+1, R.le_refl _⟩, (hf n (s n)).2⟩

end YesMetaZFC.Model.Forcing
