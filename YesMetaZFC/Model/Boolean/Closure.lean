import YesMetaZFC.Model.Boolean.NameModel

/-! # 标准布尔宇宙的集合运算

有界量词沿根成员展开；分离通过重加权，幂集通过所有小权函数构造。
所有名称的节点保持原层，谓词可以来自带任意参数的完整公式。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B)

def Stable (p : BV_graph.{u, u} B → B) : Prop :=
  ∀ G H, 𝔹.le (𝔹.meet (bv_eq 𝔹 G H) (p G)) (p H)

theorem stable_agree {p : BV_graph.{u, u} B → B} (hp : Stable 𝔹 p) (G H) :
    𝔹.Agree (bv_eq 𝔹 G H) (p G) (p H) := by
  refine ⟨hp G H, ?_⟩
  rw [eq_symm]; exact hp H G

theorem stable_const (b : B) : Stable 𝔹 (fun _ => b) := fun _ _ => 𝔹.meet_le_right _ _
theorem stable_elem (K : BV_graph.{u, u} B) : Stable 𝔹 (fun G => bv_mem 𝔹 G K) :=
  fun G H => mem_left 𝔹 G H K
theorem stable_set (K : BV_graph.{u, u} B) : Stable 𝔹 (fun G => bv_mem 𝔹 K G) :=
  fun G H => mem_right 𝔹 K G H
theorem stable_eq (K : BV_graph.{u, u} B) : Stable 𝔹 (fun G => bv_eq 𝔹 K G) := by
  intro G H; rw [𝔹.meet_comm]; exact eq_trans 𝔹 K G H

section
variable {p q : BV_graph.{u, u} B → B}
theorem stable_neg (h : Stable 𝔹 p) : Stable 𝔹 (fun G => 𝔹.neg (p G)) :=
  fun G H => (𝔹.agree_neg (stable_agree 𝔹 h G H)).1
theorem stable_meet (h : Stable 𝔹 p) (k : Stable 𝔹 q) : Stable 𝔹 (fun G => 𝔹.meet (p G) (q G)) :=
  fun G H => (𝔹.agree_meet (stable_agree 𝔹 h G H) (stable_agree 𝔹 k G H)).1
theorem stable_join (h : Stable 𝔹 p) (k : Stable 𝔹 q) : Stable 𝔹 (fun G => 𝔹.join (p G) (q G)) :=
  fun G H => (𝔹.agree_join (stable_agree 𝔹 h G H) (stable_agree 𝔹 k G H)).1
theorem stable_iff (h : Stable 𝔹 p) (k : Stable 𝔹 q) : Stable 𝔹 (fun G => 𝔹.iff (p G) (q G)) :=
  fun G H => (𝔹.agree_iff (stable_agree 𝔹 h G H) (stable_agree 𝔹 k G H)).1
theorem stable_imp (h : Stable 𝔹 p) (k : Stable 𝔹 q) : Stable 𝔹 (fun G => 𝔹.imp (p G) (q G)) :=
  fun G H => (𝔹.agree_imp (stable_agree 𝔹 h G H) (stable_agree 𝔹 k G H)).1
theorem stable_inf {ι : Sort _} (P : ι → BV_graph.{u, u} B → B) (h : ∀ i, Stable 𝔹 (P i)) :
    Stable 𝔹 (fun G => 𝔹.iInf (fun i => P i G)) :=
  fun G H => (𝔹.agree_iInf (fun i => stable_agree 𝔹 (h i) G H)).1
theorem stable_sup {ι : Sort _} (P : ι → BV_graph.{u, u} B → B) (h : ∀ i, Stable 𝔹 (P i)) :
    Stable 𝔹 (fun G => 𝔹.iSup (fun i => P i G)) :=
  fun G H => (𝔹.agree_iSup (fun i => stable_agree 𝔹 (h i) G H)).1
end

def pair (G H : BV_graph.{u, u} B) : BV_graph.{u, u} B :=
  root_sum 𝔹.toSup_order (fun i : PUnit.{u+1} ⊕ PUnit.{u+1} => i.elim (fun _ => G) (fun _ => H))
    (fun _ => 𝔹.top)

theorem pair_mem (G H K : BV_graph.{u, u} B) :
    bv_mem 𝔹 K (pair 𝔹 G H) = 𝔹.join (bv_eq 𝔹 K G) (bv_eq 𝔹 K H) := by
  rw [pair, sum_mem]
  simp only [BA_alg.top_meet]
  apply 𝔹.le_antisymm
  · apply (𝔹.iSup_le_iff _ _).mpr
    intro i; cases i <;> first | exact 𝔹.le_join_left _ _ | exact 𝔹.le_join_right _ _
  · apply (𝔹.join_le_iff _ _ _).mpr
    let v (i : PUnit.{u+1} ⊕ PUnit.{u+1}) := bv_eq 𝔹 K (i.elim (fun _ => G) (fun _ => H))
    exact ⟨𝔹.le_iSup v (.inl .unit), 𝔹.le_iSup v (.inr .unit)⟩

/-- 有界全称量词只需检查带权根成员。 -/
theorem bounded_all (G : BV_graph.{u, u} B) (p) (hp : Stable 𝔹 p) (c : B) :
    𝔹.le c (𝔹.iInf (fun H => 𝔹.imp (bv_mem 𝔹 H G) (p H))) ↔
      ∀ a : G.Child G.root, 𝔹.le (𝔹.meet c (G.val a G.root)) (p (G.at_node a)) := by
  rw [𝔹.le_iInf_iff]
  constructor
  · intro h a
    exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (mem_root 𝔹 G a))
      ((𝔹.le_imp_iff _ _ _).mp (h (G.at_node a)))
  · intro h H
    apply (𝔹.le_imp_iff _ _ _).mpr
    rw [bv_mem, 𝔹.meet_iSup, 𝔹.iSup_le_iff]
    intro a
    rw [← 𝔹.meet_assoc, 𝔹.meet_comm, eq_symm 𝔹 H (G.at_node a)]
    exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (h a)) (hp (G.at_node a) H)

def sep (G : BV_graph.{u, u} B) (p : BV_graph.{u, u} B → B) : BV_graph.{u, u} B :=
  root_sum 𝔹.toSup_order (fun a : G.Child G.root => G.at_node a)
    (fun a => 𝔹.meet (G.val a G.root) (p (G.at_node a)))

theorem sep_mem (G : BV_graph.{u, u} B) (p) (hp : Stable 𝔹 p) (H) :
    bv_mem 𝔹 H (sep 𝔹 G p) = 𝔹.meet (bv_mem 𝔹 H G) (p H) := by
  rw [sep, sum_mem, 𝔹.meet_comm (bv_mem 𝔹 H G), bv_mem, 𝔹.meet_iSup]
  apply congrArg 𝔹.iSup
  funext a
  rw [𝔹.meet_assoc, 𝔹.meet_comm (p (G.at_node a)), 𝔹.meet_left_comm (p H),
    𝔹.meet_comm (p H), 𝔹.agree_cut (stable_agree 𝔹 hp H (G.at_node a))]

def subset (G H : BV_graph.{u, u} B) : B :=
  𝔹.iInf (fun K : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 K G) (bv_mem 𝔹 K H))

theorem subset_use (G H K : BV_graph.{u, u} B) :
    𝔹.le (𝔹.meet (subset 𝔹 G H) (bv_mem 𝔹 K G)) (bv_mem 𝔹 K H) :=
  𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _)
    (𝔹.iInf_le (fun J : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 J G) (bv_mem 𝔹 J H)) K))
    (𝔹.meet_le_right _ _)

theorem subset_left (G H K : BV_graph.{u, u} B) :
    𝔹.le (𝔹.meet (bv_eq 𝔹 G H) (subset 𝔹 G K)) (subset 𝔹 H K) := by
  apply (𝔹.le_iInf_iff _ _).mpr
  intro J
  apply (𝔹.le_imp_iff _ _ _).mpr
  have he : 𝔹.le (𝔹.meet (𝔹.meet (bv_eq 𝔹 G H) (subset 𝔹 G K)) (bv_mem 𝔹 J H))
      (bv_mem 𝔹 J G) := by
    have h := mem_right 𝔹 J H G
    rw [eq_symm 𝔹 H G] at h
    exact 𝔹.le_trans (𝔹.meet_mono (𝔹.meet_le_left _ _) (𝔹.le_refl _)) h
  exact 𝔹.le_trans (𝔹.le_meet (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)) he)
    (subset_use 𝔹 G K J)

def subname (G : BV_graph.{u, u} B) (w : G.Child G.root → B) : BV_graph.{u, u} B :=
  root_sum 𝔹.toSup_order (fun a : G.Child G.root => G.at_node a)
    (fun a => 𝔹.meet (G.val a G.root) (w a))

def power (G : BV_graph.{u, u} B) : BV_graph.{u, u} B :=
  root_sum 𝔹.toSup_order (subname 𝔹 G) (fun _ => 𝔹.top)

theorem subname_subset (G : BV_graph.{u, u} B) (w) : subset 𝔹 (subname 𝔹 G w) G = 𝔹.top := by
  apply (𝔹.top_le_iff _).mp
  apply (𝔹.le_iInf_iff _ _).mpr
  intro H
  rw [𝔹.valid_imp_iff, subname, sum_mem, 𝔹.iSup_le_iff]
  intro a
  exact 𝔹.le_trans (𝔹.meet_mono (𝔹.meet_le_left _ _) (𝔹.le_refl _)) (mem_intro 𝔹 H G a)

theorem power_mem (G H : BV_graph.{u, u} B) : bv_mem 𝔹 H (power 𝔹 G) = subset 𝔹 H G := by
  rw [power, sum_mem]
  simp only [BA_alg.top_meet]
  apply 𝔹.le_antisymm
  · apply (𝔹.iSup_le_iff _ _).mpr
    intro w
    have h := subset_left 𝔹 (subname 𝔹 G w) H G
    simpa only [eq_symm 𝔹 (subname 𝔹 G w) H, subname_subset, BA_alg.meet_top] using h
  · let p (K : BV_graph.{u, u} B) := bv_mem 𝔹 K H
    have hp : Stable 𝔹 p := fun K J => mem_left 𝔹 K J H
    have he : 𝔹.le (subset 𝔹 H G) (bv_eq 𝔹 H (sep 𝔹 G p)) := by
      apply le_eq_of_mem 𝔹 H (sep 𝔹 G p)
      · intro K
        rw [sep_mem 𝔹 G p hp]
        exact 𝔹.le_meet (subset_use 𝔹 H G K) (𝔹.meet_le_right _ _)
      · intro K
        rw [sep_mem 𝔹 G p hp]
        exact 𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_right _ _)
    exact 𝔹.le_trans he (𝔹.le_iSup (fun w => bv_eq 𝔹 H (subname 𝔹 G w))
      (fun a => p (G.at_node a)))

def union (G : BV_graph.{u, u} B) : BV_graph.{u, u} B :=
  mix 𝔹 (fun a : G.Child G.root => G.at_node a) (fun a => G.val a G.root)

theorem bounded_sup (G : BV_graph.{u, u} B) (p) (hp : Stable 𝔹 p) :
    𝔹.iSup (fun H => 𝔹.meet (bv_mem 𝔹 H G) (p H)) =
      𝔹.iSup (fun a : G.Child G.root => 𝔹.meet (G.val a G.root) (p (G.at_node a))) := by
  apply 𝔹.le_antisymm
  · apply (𝔹.iSup_le_iff _ _).mpr
    intro H
    rw [𝔹.meet_comm, bv_mem, 𝔹.meet_iSup, 𝔹.iSup_le_iff]
    intro a
    rw [𝔹.meet_left_comm, 𝔹.meet_comm (p H)]
    exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (hp H (G.at_node a)))
      (𝔹.le_iSup (fun a : G.Child G.root => 𝔹.meet (G.val a G.root) (p (G.at_node a))) a)
  · apply (𝔹.iSup_le_iff _ _).mpr
    intro a
    exact 𝔹.le_trans (𝔹.meet_mono (mem_root 𝔹 G a) (𝔹.le_refl _))
      (𝔹.le_iSup (fun H => 𝔹.meet (bv_mem 𝔹 H G) (p H)) (G.at_node a))

theorem union_mem (G H : BV_graph.{u, u} B) :
    bv_mem 𝔹 H (union 𝔹 G) =
      𝔹.iSup (fun K : BV_graph.{u, u} B => 𝔹.meet (bv_mem 𝔹 K G) (bv_mem 𝔹 H K)) := by
  rw [union, mix_mem, bounded_sup 𝔹 G _ (fun K J => mem_right 𝔹 H K J)]

/-- 最大值见证按原根成员小域收集，不要求二元关系具有函数性。 -/
theorem collection (G : BV_graph.{u, u} B) (R : BV_graph.{u, u} B → BV_graph.{u, u} B → B)
    (hR : ∀ H, Stable 𝔹 (R H)) : ∃ C : BV_graph.{u, u} B,
      ∀ a : G.Child G.root, 𝔹.le (𝔹.iSup (R (G.at_node a)))
        (𝔹.iSup (fun H => 𝔹.meet (bv_mem 𝔹 H C) (R (G.at_node a) H))) := by
  obtain ⟨F, hF⟩ := Classical.axiomOfChoice (fun a : G.Child G.root =>
    maximum 𝔹 (R (G.at_node a)) (hR (G.at_node a)))
  let C := root_sum 𝔹.toSup_order F (fun _ => 𝔹.top)
  refine ⟨C, fun a => ?_⟩
  have hm : 𝔹.le 𝔹.top (bv_mem 𝔹 (F a) C) := by
    rw [sum_mem]
    simpa only [eq_refl, BA_alg.meet_top] using
      𝔹.le_iSup (fun i => 𝔹.meet 𝔹.top (bv_eq 𝔹 (F a) (F i))) a
  apply 𝔹.le_trans _ (𝔹.le_iSup (fun H => 𝔹.meet (bv_mem 𝔹 H C) (R (G.at_node a) H)) (F a))
  rw [← hF a]
  exact 𝔹.le_meet (𝔹.le_trans (𝔹.le_top _) hm) (𝔹.le_refl _)

end YesMetaZFC.Model.Boolean.BV_graph
