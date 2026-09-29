import YesMetaZFC.Model.Forcing.Valuation
import YesMetaZFC.Model.Forcing.BooleanGeneric

/-! # 名称求值的原子真值定理

四类见证稠密集分别处理双向成员匹配及双向包含的无限合取。
假设只列出实际图节点产生的稠密集，不把真值引理或求值同余当成输入。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean Boolean.BV_graph SmallGraph
universe u v
variable {B : Type v} (𝔹 : CB_alg B)

def mem_dense_l (G H : BV_graph.{u, v} B) : Pos_l 𝔹.toBA_alg → Prop :=
  sup_dense_l 𝔹 (fun c : H.Child H.root => 𝔹.meet (H.val c H.root) (bv_eq 𝔹 G (H.at_node c)))

def eq_dense_l (G H : BV_graph.{u, v} B) : Pos_l 𝔹.toBA_alg → Prop :=
  sup_dense_l 𝔹 (fun c : G.Child G.root =>
    𝔹.neg (𝔹.imp (G.val c G.root) (bv_mem 𝔹 (G.at_node c) H)))

/-- 只要求遇到给定两幅图所有节点的四类明确稠密集。 -/
def Name_generic_l (U : Filter_l 𝔹.toBA_alg) (G H : BV_graph.{u, v} B) : Prop :=
  ∀ a b,
    BF_meets_l U (mem_dense_l 𝔹 (G.at_node a) (H.at_node b)) ∧
    BF_meets_l U (mem_dense_l 𝔹 (H.at_node b) (G.at_node a)) ∧
    BF_meets_l U (eq_dense_l 𝔹 (G.at_node a) (H.at_node b)) ∧
    BF_meets_l U (eq_dense_l 𝔹 (H.at_node b) (G.at_node a))

def name_dense_l (G H : BV_graph.{u, v} B) (a : G.Domain) (b : H.Domain)
    (p : Pos_l 𝔹.toBA_alg) : Prop :=
  mem_dense_l 𝔹 (G.at_node a) (H.at_node b) p ∧
  mem_dense_l 𝔹 (H.at_node b) (G.at_node a) p ∧
  eq_dense_l 𝔹 (G.at_node a) (H.at_node b) p ∧
  eq_dense_l 𝔹 (H.at_node b) (G.at_node a) p

theorem name_dense_dense_l (G H : BV_graph.{u, v} B) (a : G.Domain) (b : H.Domain) :
    (positive_order_l 𝔹.toBA_alg).toPO_pre.Dense_l (name_dense_l 𝔹 G H a b) := by
  let R := (positive_order_l 𝔹.toBA_alg).toPO_pre
  exact R.dense_inter_l (sup_dense_dense_l 𝔹 _)
    (R.dense_inter_l (sup_dense_dense_l 𝔹 _)
      (R.dense_inter_l (sup_dense_dense_l 𝔹 _) (sup_dense_dense_l 𝔹 _)
        (sup_dense_lower_l 𝔹 _)) (sup_dense_lower_l 𝔹 _)) (sup_dense_lower_l 𝔹 _)

theorem name_dense_lower_l (G H : BV_graph.{u, v} B) (a : G.Domain) (b : H.Domain) :
    (positive_order_l 𝔹.toBA_alg).toPO_pre.Lower_l (name_dense_l 𝔹 G H a b) :=
  fun h k => ⟨sup_dense_lower_l 𝔹 _ h k.1, sup_dense_lower_l 𝔹 _ h k.2.1,
    sup_dense_lower_l 𝔹 _ h k.2.2.1, sup_dense_lower_l 𝔹 _ h k.2.2.2⟩

theorem name_generic_of_meets_l (U : Filter_l 𝔹.toBA_alg) (G H : BV_graph.{u, v} B)
    (h : ∀ a b, BF_meets_l U (name_dense_l 𝔹 G H a b)) : Name_generic_l 𝔹 U G H := by
  intro a b
  obtain ⟨p, hp, h₁, h₂, h₃, h₄⟩ := h a b
  exact ⟨⟨p, hp, h₁⟩, ⟨p, hp, h₂⟩, ⟨p, hp, h₃⟩, ⟨p, hp, h₄⟩⟩

/-- 节点已有可数枚举时，从任意非零条件得到所需的真实泛型滤子。 -/
theorem name_generic_countable_l (G H : BV_graph.{u, v} B)
    (g : Nat → G.Domain) (hg : ∀ a, ∃ n, g n = a)
    (f : Nat → H.Domain) (hf : ∀ b, ∃ n, f n = b) (p : Pos_l 𝔹.toBA_alg) :
    ∃ U : Filter_l 𝔹.toBA_alg, U.Maximal_l ∧ U.mem p.1 ∧ Name_generic_l 𝔹 U G H := by
  obtain ⟨U, hU, hp, hu⟩ := generic_ultrafilter_grid_l 𝔹.toBA_alg
    (fun i j => name_dense_l 𝔹 G H (g i) (f j))
    (fun i j => name_dense_dense_l 𝔹 G H (g i) (f j))
    (fun i j => name_dense_lower_l 𝔹 G H (g i) (f j)) p
  refine ⟨U, hU, hp, name_generic_of_meets_l 𝔹 U G H (fun a b => ?_)⟩
  obtain ⟨i, rfl⟩ := hg a
  obtain ⟨j, rfl⟩ := hf b
  exact hu i j

private theorem mem_truth_step_l (U : Filter_l 𝔹.toBA_alg) (hU : U.Proper_l)
    (G H : BV_graph.{u, v} B) (h : BF_meets_l U (mem_dense_l 𝔹 G H))
    (ih : ∀ c : H.Child H.root,
      U.mem (bv_eq 𝔹 G (H.at_node c)) ↔ val_l U.mem G = val_l U.mem (H.at_node c)) :
    U.mem (bv_mem 𝔹 G H) ↔ val_l U.mem G ∈ val_l U.mem H := by
  rw [bv_mem, sup_mem_iff_l 𝔹 U hU _ h, val_mem_l]
  exact exists_congr fun c => (meet_mem_iff_l U _ _).trans (and_congr_right fun _ => ih c)

/-- 对左图作良基归纳，双向成员匹配同时下降到左右子节点。 -/
theorem val_eq_iff_l (U : Filter_l 𝔹.toBA_alg) (hU : U.Maximal_l)
    (G H : BV_graph.{u, v} B) (h : Name_generic_l 𝔹 U G H) :
    U.mem (bv_eq 𝔹 G H) ↔ val_l U.mem G = val_l U.mem H := by
  have he (a : G.Domain) : ∀ b : H.Domain,
      U.mem (bv_eq 𝔹 (G.at_node a) (H.at_node b)) ↔
        val_l U.mem (G.at_node a) = val_l U.mem (H.at_node b) := by
    induction a using G.wf.induction with
    | h a ih =>
      intro b
      -- 两个方向均使用左图子节点的同一个归纳假设，反向匹配先交换等号两侧。
      have hl (c : G.Child a) := mem_truth_step_l 𝔹 U hU.1
        (G.at_node c) (H.at_node b) (h c b).1 (fun d => ih c c.2 d)
      have hr (d : H.Child b) := mem_truth_step_l 𝔹 U hU.1
        (H.at_node d) (G.at_node a) (h a d).2.1 (fun c => by
          rw [eq_symm, ih c c.2 d, eq_comm])
      -- 否定包含项的稠密集把无限合取还原为逐项包含，再由外延性收尾。
      rw [eq_unfold, meet_mem_iff_l,
        inf_mem_iff_l 𝔹 U hU.1 _ (h a b).2.2.1,
        inf_mem_iff_l 𝔹 U hU.1 _ (h a b).2.2.2]
      constructor
      · rintro ⟨l, r⟩
        apply SG_set.ext
        intro x
        constructor
        · intro hx
          obtain ⟨c, hc, rfl⟩ := (val_mem_l _ _ _).mp hx
          exact (hl c).mp ((imp_mem_iff_l U hU _ _).mp (l c) hc)
        · intro hx
          obtain ⟨d, hd, rfl⟩ := (val_mem_l _ _ _).mp hx
          exact (hr d).mp ((imp_mem_iff_l U hU _ _).mp (r d) hd)
      · intro e
        constructor
        · intro c
          apply (imp_mem_iff_l U hU _ _).mpr
          intro hc
          apply (hl c).mpr
          rw [← e]
          exact (val_mem_l _ _ _).mpr ⟨c, hc, rfl⟩
        · intro d
          apply (imp_mem_iff_l U hU _ _).mpr
          intro hd
          apply (hr d).mpr
          rw [e]
          exact (val_mem_l _ _ _).mpr ⟨d, hd, rfl⟩
  exact he G.root H.root

theorem val_mem_iff_l (U : Filter_l 𝔹.toBA_alg) (hU : U.Maximal_l)
    (G H : BV_graph.{u, v} B) (h : Name_generic_l 𝔹 U G H) :
    U.mem (bv_mem 𝔹 G H) ↔ val_l U.mem G ∈ val_l U.mem H :=
  mem_truth_step_l 𝔹 U hU.1 G H (h G.root H.root).1
    (fun c => val_eq_iff_l 𝔹 U hU G (H.at_node c) h)

end YesMetaZFC.Model.Forcing
