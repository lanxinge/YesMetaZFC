import YesMetaZFC.Model.Boolean.Algebra
import YesMetaZFC.Model.SmallGraph.RootSum

/-! # 布尔名称的良基小图呈现

小节点域、真值域分别保持原 universe；等号按两侧子节点的匹配递归定义。
递归只沿左图良基关系进行，每次实际匹配同时下降到两侧子节点。
-/

namespace YesMetaZFC.Model.Boolean

/-- 以布尔值标记成员边的良基有根图；非成员边上的标签不参与解释。 -/
structure BV_graph.{u, v} (B : Type v) extends SmallGraph.WF_graph.{u} where
  val : Domain → Domain → B

/-- 标准名称宇宙：节点与布尔值同层，名称载体预先固定在上一层。 -/
abbrev BV_name.{u} (B : Type u) : Type (u+1) := BV_graph.{u, u} B

universe u v w
namespace BV_graph
variable {B : Type v}

def empty (R : PO_bot B) : BV_graph.{u, v} B where
  toWF_graph := SmallGraph.WF_graph.empty
  val _ _ := R.bot

abbrev Child (G : BV_graph.{u, v} B) (a : G.Domain) := {b : G.Domain // G.mem b a}

abbrev at_node (G : BV_graph.{u, v} B) (a : G.Domain) : BV_graph.{u, v} B where
  toWF_graph := G.toWF_graph.at_node a
  val := G.val

variable (𝔹 : CB_alg B)

def eq_aux (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) : G.Domain → H.Domain → B :=
  G.wf.fix fun a ih b => 𝔹.meet
    (𝔹.iInf fun c : G.Child a => 𝔹.imp (G.val c a)
      (𝔹.iSup fun d : H.Child b => 𝔹.meet (H.val d b) (ih c c.2 d)))
    (𝔹.iInf fun d : H.Child b => 𝔹.imp (H.val d b)
      (𝔹.iSup fun c : G.Child a => 𝔹.meet (G.val c a) (ih c c.2 d)))

theorem eq_aux_unfold (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B)
    (a : G.Domain) (b : H.Domain) : eq_aux 𝔹 G H a b = 𝔹.meet
      (𝔹.iInf fun c : G.Child a => 𝔹.imp (G.val c a)
        (𝔹.iSup fun d : H.Child b => 𝔹.meet (H.val d b) (eq_aux 𝔹 G H c d)))
      (𝔹.iInf fun d : H.Child b => 𝔹.imp (H.val d b)
        (𝔹.iSup fun c : G.Child a => 𝔹.meet (G.val c a) (eq_aux 𝔹 G H c d))) := by
  rw [eq_aux, WellFounded.fix_eq]

theorem eq_aux_symm (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B)
    (a : G.Domain) (b : H.Domain) : eq_aux 𝔹 G H a b = eq_aux 𝔹 H G b a := by
  induction a using G.wf.induction generalizing b with
  | h a ih =>
      rw [eq_aux_unfold 𝔹 G H a b, eq_aux_unfold 𝔹 H G b a, 𝔹.meet_comm]
      congr 1
      · apply congrArg 𝔹.iInf
        funext d
        apply congrArg (𝔹.imp (H.val d b))
        apply congrArg 𝔹.iSup
        funext c
        rw [ih c c.2 d]
      · apply congrArg 𝔹.iInf
        funext c
        apply congrArg (𝔹.imp (G.val c a))
        apply congrArg 𝔹.iSup
        funext d
        rw [ih c c.2 d]

def bv_eq (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) : B :=
  eq_aux 𝔹 G H G.root H.root

def bv_mem (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) : B :=
  𝔹.iSup fun b : H.Child H.root => 𝔹.meet (H.val b H.root) (bv_eq 𝔹 G (H.at_node b))

theorem empty_mem (G : BV_graph.{u, v} B) : bv_mem 𝔹 G (empty.{w, v} 𝔹.toPO_bot) = 𝔹.bot :=
  𝔹.le_antisymm ((𝔹.iSup_le_iff _ _).mpr (fun a => False.elim a.2)) (𝔹.bot_le _)

theorem eq_symm (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) :
    bv_eq 𝔹 G H = bv_eq 𝔹 H G := eq_aux_symm 𝔹 G H G.root H.root

/-- 名称等同逐项比较两侧带权成员，不把顶值等同定义为 Lean 相等。 -/
theorem eq_unfold (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) :
    bv_eq 𝔹 G H = 𝔹.meet
      (𝔹.iInf fun a : G.Child G.root => 𝔹.imp (G.val a G.root) (bv_mem 𝔹 (G.at_node a) H))
      (𝔹.iInf fun b : H.Child H.root => 𝔹.imp (H.val b H.root) (bv_mem 𝔹 (H.at_node b) G)) := by
  rw [bv_eq, eq_aux_unfold]
  congr 1
  apply congrArg 𝔹.iInf
  funext b
  apply congrArg (𝔹.imp (H.val b H.root))
  unfold bv_mem
  apply congrArg 𝔹.iSup
  funext a
  exact congrArg (𝔹.meet (G.val a G.root)) (eq_aux_symm 𝔹 G H a b)

theorem le_eq_iff (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) (c : B) :
    𝔹.le c (bv_eq 𝔹 G H) ↔
      (∀ a : G.Child G.root, 𝔹.le (𝔹.meet c (G.val a G.root)) (bv_mem 𝔹 (G.at_node a) H)) ∧
      (∀ b : H.Child H.root, 𝔹.le (𝔹.meet c (H.val b H.root)) (bv_mem 𝔹 (H.at_node b) G)) := by
  rw [eq_unfold, 𝔹.le_meet_iff]
  apply and_congr
  · exact (𝔹.le_iInf_iff _ c).trans (forall_congr' fun a => 𝔹.le_imp_iff _ _ _)
  · exact (𝔹.le_iInf_iff _ c).trans (forall_congr' fun b => 𝔹.le_imp_iff _ _ _)

/-- 任意根成员项给出对应的加权隶属下界。 -/
theorem mem_intro (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) (b : H.Child H.root) :
    𝔹.le (𝔹.meet (H.val b H.root) (bv_eq 𝔹 G (H.at_node b))) (bv_mem 𝔹 G H) :=
  𝔹.le_iSup (fun c : H.Child H.root => 𝔹.meet (H.val c H.root) (bv_eq 𝔹 G (H.at_node c))) b

theorem eq_refl (G : BV_graph.{u, v} B) : bv_eq 𝔹 G G = 𝔹.top := by
  apply (𝔹.top_le_iff _).mp
  have h (a : G.Domain) : 𝔹.le 𝔹.top (bv_eq 𝔹 (G.at_node a) (G.at_node a)) := by
    induction a using G.wf.induction with
    | h a ih =>
        have hm (b : G.Child a) :
            𝔹.le (𝔹.meet 𝔹.top (G.val b a)) (bv_mem 𝔹 (G.at_node b) (G.at_node a)) := by
          rw [𝔹.top_meet]
          exact 𝔹.le_trans
            (𝔹.le_meet (𝔹.le_refl _) (𝔹.le_trans (𝔹.le_top _) (ih b b.2)))
            (mem_intro 𝔹 (G.at_node b) (G.at_node a) b)
        exact (le_eq_iff 𝔹 (G.at_node a) (G.at_node a) 𝔹.top).mpr ⟨hm, hm⟩
  exact h G.root

theorem mem_root (G : BV_graph.{u, v} B) (a : G.Child G.root) :
    𝔹.le (G.val a G.root) (bv_mem 𝔹 (G.at_node a) G) := by
  have h := mem_intro 𝔹 (G.at_node a) G a
  simpa only [eq_refl, BA_alg.meet_top] using h

end BV_graph
end YesMetaZFC.Model.Boolean
