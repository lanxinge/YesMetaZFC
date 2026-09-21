import YesMetaZFC.Logic.Arithmetic.Beta
import YesMetaZFC.Model.Arithmetic.PA.Division

/-! # 任意 PA 模型中的 β 读取

模数始终为后继数，包括 c=0 的情况。读取总性不等于任意有限函数可编码。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Beta
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def modulus_l (c i : num_l ℳ) : num_l ℳ := succ_l (mul_l (succ_l i) c)

def graph_l (b c i a : num_l ℳ) : Prop := ∃ q, Division.graph_l b (modulus_l c i) q a

theorem modulus_eval_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (c i : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Beta.modulus_m c i).eval η = modulus_l (c.eval η) (i.eval η) := rfl

theorem graph_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c i a : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Beta.graph_m b c i a).satisfies η ↔
      graph_l (b.eval η) (c.eval η) (i.eval η) (a.eval η) := by
  simp only [Logic.Arithmetic.Beta.graph_m, Formula.satisfies, Division.graph_sat_m,
    Term.eval_weakenBound, modulus_eval_m]
  rfl

theorem domain_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (b c i : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Beta.domain_m b c i).satisfies η ↔
      ∃ a, graph_l (b.eval η) (c.eval η) (i.eval η) a := by
  simp only [Logic.Arithmetic.Beta.domain_m, Formula.satisfies, graph_sat_m,
    Term.eval_weakenBound]
  rfl

theorem bound_m {b c i a : num_l ℳ} (h : graph_l b c i a) : lt_l a (modulus_l c i) := by
  obtain ⟨q, h⟩ := h
  exact h.2

theorem total_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m) (b c i : num_l ℳ) :
    ∃ a, graph_l b c i a := by
  obtain ⟨q, a, h⟩ := Division.exists_m hPA b (modulus_l c i)
    (Q.nonzero_m (q_models_m hPA) _)
  exact ⟨a, q, h⟩

theorem unique_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m) {b c i a d : num_l ℳ}
    (ha : graph_l b c i a) (hd : graph_l b c i d) : a = d := by
  obtain ⟨q, hq⟩ := ha
  obtain ⟨r, hr⟩ := hd
  exact (Division.unique_m hPA hq hr).2

/-- 零参数给出模 1 的退化读取，而不是未定义的除零情形。 -/
theorem zero_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m) (b i : num_l ℳ) :
    graph_l b (zero_l ℳ) i (zero_l ℳ) := by
  refine ⟨b, ?_⟩
  change Division.graph_l b (succ_l (mul_l (succ_l i) (zero_l ℳ))) b (zero_l ℳ)
  rw [Q.mul_zero_m (q_models_m hPA)]
  exact ⟨(Q.add_zero_m (q_models_m hPA) _).trans (mul_one_m hPA b),
    (lt_succ_m hPA).mpr (le_refl_m hPA _)⟩

end YesMetaZFC.Model.Arithmetic.PA.Beta
