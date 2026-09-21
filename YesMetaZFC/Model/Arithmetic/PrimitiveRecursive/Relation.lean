import YesMetaZFC.Logic.Arithmetic.PrimitiveRecursive.Formula
import YesMetaZFC.Model.Arithmetic.PA.HistoryUniqueness
import YesMetaZFC.Model.Arithmetic.PA.Unpairing

/-! # 原始递归图的任意模型解释

关系解释不预设标准数域；递归分支读取内部 β 历史。存在与唯一性另行证明。
-/
namespace YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
open Logic FirstOrder Logic.Arithmetic Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def relation_l : code_m → num_l ℳ → num_l ℳ → Prop
  | .zero => fun _ y => zero_l ℳ = y
  | .succ => fun x y => succ_l x = y
  | .left => fun x y => ∃ z, Pairing.value_l y z = x
  | .right => fun x y => ∃ z, Pairing.value_l z y = x
  | .pair c d => fun x y => ∃ a b, relation_l c x a ∧ relation_l d x b ∧ Pairing.value_l a b = y
  | .comp c d => fun x y => ∃ a, relation_l d x a ∧ relation_l c a y
  | .prec c d => fun x y => ∃ a n, Pairing.value_l a n = x ∧
      PA.History.graph_l (relation_l c)
        (fun a i v w => relation_l d (Pairing.value_l a (Pairing.value_l i v)) w) a n y

theorem iteration_sat_m (G : History.binary_m) (R : num_l ℳ → num_l ℳ → Prop)
    (hG : ∀ {Γ Δ} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num),
      (G s t).satisfies η ↔ R (s.eval η) (t.eval η))
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (x i a d : Term signature_m Γ Δ .num) :
    (iteration_m G x i a d).satisfies η ↔
      R (Pairing.value_l (x.eval η) (Pairing.value_l (i.eval η) (a.eval η))) (d.eval η) := by
  simp only [iteration_m, Formula.satisfies, Pairing.graph_sat_m, hG, Term.eval_weakenBound]
  change (∃ p q, Pairing.value_l (i.eval η) (a.eval η) = p ∧
    Pairing.value_l (x.eval η) p = q ∧ R q (d.eval η)) ↔ _
  constructor
  · rintro ⟨p, q, rfl, rfl, h⟩; exact h
  · intro h; exact ⟨_, _, rfl, rfl, h⟩

theorem graph_sat_m (c : code_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (graph_m c s t).satisfies η ↔ relation_l c (s.eval η) (t.eval η) := by
  induction c generalizing Γ Δ with
  | zero => rfl
  | succ => rfl
  | left =>
      simp only [graph_m, Logic.Arithmetic.Pairing.left_m, Formula.satisfies,
        Pairing.graph_sat_m, Term.eval_weakenBound]
      rfl
  | right =>
      simp only [graph_m, Logic.Arithmetic.Pairing.right_m, Formula.satisfies,
        Pairing.graph_sat_m, Term.eval_weakenBound]
      rfl
  | pair c d hc hd =>
      simp only [graph_m, pair_m, Formula.satisfies, hc, hd,
        Pairing.graph_sat_m, Term.eval_weakenBound]
      rfl
  | comp c d hc hd =>
      simp only [graph_m, comp_m, Formula.satisfies, hc, hd, Term.eval_weakenBound]
      rfl
  | prec c d hc hd =>
      simp only [graph_m, prec_m, Formula.satisfies, Pairing.graph_sat_m,
        PA.History.graph_sat_m (graph_m c) (iteration_m (graph_m d)) (relation_l c)
          (fun a i v w => relation_l d (Pairing.value_l a (Pairing.value_l i v)) w)
          hc (iteration_sat_m (graph_m d) (relation_l d) hd), Term.eval_weakenBound]
      rfl

end YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
