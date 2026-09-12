import YesMetaZFC.Model.Boolean.Foundation
import YesMetaZFC.Model.Boolean.Selection

/-! # 布尔值选择集

先给每个呈现成员取最大值见证，再用模等同的选择系数消除重复选择。
两两不交的假设只用于排除来自不同、尚不等同成员的两个选择同时落入一个成员。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B)

def selects (C G : BV_graph.{u, u} B) : B :=
  𝔹.iSup (fun H : BV_graph.{u, u} B => 𝔹.meet (𝔹.meet (bv_mem 𝔹 H C) (bv_mem 𝔹 H G))
    (𝔹.iInf (fun K : BV_graph.{u, u} B =>
      𝔹.imp (𝔹.meet (bv_mem 𝔹 K C) (bv_mem 𝔹 K G)) (bv_eq 𝔹 K H))))

theorem selects_stable (C : BV_graph.{u, u} B) : Stable 𝔹 (selects 𝔹 C) :=
  stable_sup 𝔹 _ (fun H => stable_meet 𝔹
    (stable_meet 𝔹 (stable_const 𝔹 _) (stable_set 𝔹 H))
    (stable_inf 𝔹 _ (fun K => stable_imp 𝔹
      (stable_meet 𝔹 (stable_const 𝔹 _) (stable_set 𝔹 K)) (stable_const 𝔹 _))))

def pairwise_disjoint (G : BV_graph.{u, u} B) : B :=
  𝔹.iInf (fun H : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 H G)
    (𝔹.iInf (fun K : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 K G)
      (𝔹.imp (𝔹.neg (bv_eq 𝔹 H K)) (𝔹.neg (𝔹.iSup (fun J : BV_graph.{u, u} B =>
        𝔹.meet (bv_mem 𝔹 J H) (bv_mem 𝔹 J K))))))))

/-- 非空且两两不交的布尔集合族，在同一布尔条件下有实际选择集。 -/
theorem choice (G : BV_graph.{u, u} B) (c : B)
    (hn : 𝔹.le c (𝔹.iInf (fun H : BV_graph.{u, u} B =>
      𝔹.imp (bv_mem 𝔹 H G) (nonempty_value 𝔹 H))))
    (hd : 𝔹.le c (pairwise_disjoint 𝔹 G)) :
    ∃ C : BV_graph.{u, u} B,
      𝔹.le c (𝔹.iInf (fun H : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 H G) (selects 𝔹 C H))) := by
  classical
  let F (i : G.Child G.root) := G.at_node i
  let w (i : G.Child G.root) := 𝔹.meet c (G.val i G.root)
  obtain ⟨q, hq, hdis, hcov⟩ := selection 𝔹 F w
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun i => maximum 𝔹
    (fun H : BV_graph.{u, u} B => bv_mem 𝔹 H (F i)) (stable_elem 𝔹 (F i)))
  let C := root_sum 𝔹.toSup_order f q
  have hqc (i) : 𝔹.le (q i) c := 𝔹.le_trans (hq i) (𝔹.meet_le_left _ _)
  have hqG (i) : 𝔹.le (q i) (bv_mem 𝔹 (F i) G) :=
    𝔹.le_trans (hq i) (𝔹.le_trans (𝔹.meet_le_right _ _) (mem_root 𝔹 G i))
  have hfi (i) : 𝔹.le (q i) (bv_mem 𝔹 (f i) (F i)) := by
    rw [hf i]
    exact 𝔹.imp_use (𝔹.le_trans (hqc i) (𝔹.le_trans hn (𝔹.iInf_le _ (F i)))) (hqG i)
  have hsel (i) : 𝔹.le (q i) (selects 𝔹 C (F i)) := by
    have huni (K : BV_graph.{u, u} B) :
        𝔹.le (𝔹.meet (𝔹.meet (q i) (bv_mem 𝔹 K (F i))) (bv_mem 𝔹 K C)) (bv_eq 𝔹 K (f i)) := by
      rw [sum_mem, 𝔹.meet_iSup, 𝔹.iSup_le_iff]
      intro j
      by_cases hij : i = j
      · subst j; exact 𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_right _ _)
      · let e := 𝔹.meet (𝔹.meet (q i) (bv_mem 𝔹 K (F i)))
          (𝔹.meet (q j) (bv_eq 𝔹 K (f j)))
        have hei : 𝔹.le e (q i) := 𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_left _ _)
        have hej : 𝔹.le e (q j) := 𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_left _ _)
        have hki : 𝔹.le e (bv_mem 𝔹 K (F i)) :=
          𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)
        have hkj : 𝔹.le e (bv_mem 𝔹 K (F j)) := by
          have heq : 𝔹.le e (bv_eq 𝔹 (f j) K) := by
            rw [eq_symm]; exact 𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_right _ _)
          exact 𝔹.le_trans (𝔹.le_meet heq (𝔹.le_trans hej (hfi j))) (mem_left 𝔹 (f j) K (F j))
        have hab := 𝔹.imp_use (𝔹.le_trans (𝔹.le_trans hei (hqc i))
          (𝔹.le_trans hd (𝔹.iInf_le _ (F i)))) (𝔹.le_trans hei (hqG i))
        have hab' := 𝔹.imp_use (𝔹.le_trans hab (𝔹.iInf_le _ (F j))) (𝔹.le_trans hej (hqG j))
        have hneg := 𝔹.imp_use hab' (𝔹.le_trans (𝔹.le_meet hei hej) (hdis i j hij))
        have hmem := 𝔹.le_trans (𝔹.le_meet hki hkj) (𝔹.le_iSup
          (fun J : BV_graph.{u, u} B => 𝔹.meet (bv_mem 𝔹 J (F i)) (bv_mem 𝔹 J (F j))) K)
        exact 𝔹.le_trans (𝔹.imp_use hneg hmem) (𝔹.bot_le _)
    apply 𝔹.le_trans _ (𝔹.le_iSup (fun H : BV_graph.{u, u} B =>
      𝔹.meet (𝔹.meet (bv_mem 𝔹 H C) (bv_mem 𝔹 H (F i)))
        (𝔹.iInf (fun K : BV_graph.{u, u} B =>
          𝔹.imp (𝔹.meet (bv_mem 𝔹 K C) (bv_mem 𝔹 K (F i))) (bv_eq 𝔹 K H)))) (f i))
    apply 𝔹.le_meet
    · apply 𝔹.le_meet _ (hfi i)
      rw [sum_mem]
      simpa only [eq_refl, BA_alg.meet_top] using
        𝔹.le_iSup (fun j => 𝔹.meet (q j) (bv_eq 𝔹 (f i) (f j))) i
    · apply (𝔹.le_iInf_iff _ _).mpr
      intro K
      apply (𝔹.le_imp_iff _ _ _).mpr
      exact 𝔹.le_trans (𝔹.le_meet
        (𝔹.le_meet (𝔹.meet_le_left _ _) (𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_right _ _)))
        (𝔹.le_trans (𝔹.meet_le_right _ _) (𝔹.meet_le_left _ _))) (huni K)
  refine ⟨C, (bounded_all 𝔹 G _ (selects_stable 𝔹 C) c).mpr (fun i => ?_)⟩
  apply 𝔹.le_trans (hcov i)
  apply (𝔹.iSup_le_iff _ _).mpr
  intro j
  rw [𝔹.meet_comm, eq_symm 𝔹 (F i) (F j)]
  exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (hsel j)) (selects_stable 𝔹 C (F j) (F i))

end YesMetaZFC.Model.Boolean.BV_graph
