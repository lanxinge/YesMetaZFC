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

/-- 递归步的两个配对见证保持为关系，不选择任何内部数。 -/
def iteration_l (R : num_l ℳ → num_l ℳ → Prop) (a i v w : num_l ℳ) : Prop :=
  ∃ p q, Pairing.graph_l i v p ∧ Pairing.graph_l a p q ∧ R q w

def relation_l : code_m → num_l ℳ → num_l ℳ → Prop
  | .zero => fun _ y => zero_l ℳ = y
  | .succ => fun x y => succ_l x = y
  | .left => fun x y => ∃ z, Pairing.graph_l y z x
  | .right => fun x y => ∃ z, Pairing.graph_l z y x
  | .pair c d => fun x y => ∃ a b, relation_l c x a ∧ relation_l d x b ∧ Pairing.graph_l a b y
  | .comp c d => fun x y => ∃ a, relation_l d x a ∧ relation_l c a y
  | .prec c d => fun x y => ∃ a n, Pairing.graph_l a n x ∧
      PA.History.graph_l (relation_l c)
        (iteration_l (relation_l d)) a n y

theorem iteration_sat_m (G : History.binary_m) (R : num_l ℳ → num_l ℳ → Prop)
    (hG : ∀ {Γ Δ} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num),
      (G s t).satisfies η ↔ R (s.eval η) (t.eval η))
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (x i a d : Term signature_m Γ Δ .num) :
    (iteration_m G x i a d).satisfies η ↔
      iteration_l R (x.eval η) (i.eval η) (a.eval η) (d.eval η) := by
  simp only [iteration_m, Formula.satisfies, Pairing.graph_sat_m, hG, Term.eval_weakenBound]
  rfl

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
          (iteration_l (relation_l d))
          hc (iteration_sat_m (graph_m d) (relation_l d) hd), Term.eval_weakenBound]
      rfl

end YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
