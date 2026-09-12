import YesMetaZFC.Model.Boolean.Names

/-! # 布尔名称等号的传递性与隶属同余

传递性沿第一个呈现图归纳。中间图的成员匹配由上确界分配律组合，
反向匹配使用同一个归纳假设与已经证明的对称性。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u v w x y
variable {B : Type v} (𝔹 : CB_alg B)

private theorem mem_step (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B)
    (K : BV_graph.{x, v} B)
    (h : ∀ (b : H.Child H.root) (c : K.Child K.root),
      𝔹.le (𝔹.meet (bv_eq 𝔹 G (H.at_node b)) (bv_eq 𝔹 (H.at_node b) (K.at_node c)))
        (bv_eq 𝔹 G (K.at_node c))) :
    𝔹.le (𝔹.meet (bv_eq 𝔹 H K) (bv_mem 𝔹 G H)) (bv_mem 𝔹 G K) := by
  rw [bv_mem, 𝔹.meet_iSup]
  apply (𝔹.iSup_le_iff _ _).mpr
  intro b
  rw [← 𝔹.meet_assoc]
  have hb := ((le_eq_iff 𝔹 H K (bv_eq 𝔹 H K)).mp (𝔹.le_refl _)).1 b
  apply 𝔹.le_trans (𝔹.meet_mono hb (𝔹.le_refl _))
  rw [𝔹.meet_comm, bv_mem, 𝔹.meet_iSup]
  apply (𝔹.iSup_le_iff _ _).mpr
  intro c
  rw [𝔹.meet_left_comm]
  exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (h b c)) (mem_intro 𝔹 G K c)

/-- 布尔值传递性，不要求等号值只能取底或顶。 -/
theorem eq_trans (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) (K : BV_graph.{x, v} B) :
    𝔹.le (𝔹.meet (bv_eq 𝔹 G H) (bv_eq 𝔹 H K)) (bv_eq 𝔹 G K) := by
  have h (a : G.Domain) : ∀ (b : H.Domain) (c : K.Domain),
      𝔹.le (𝔹.meet (bv_eq 𝔹 (G.at_node a) (H.at_node b))
        (bv_eq 𝔹 (H.at_node b) (K.at_node c))) (bv_eq 𝔹 (G.at_node a) (K.at_node c)) := by
    induction a using G.wf.induction with
    | h a ih =>
        intro b c
        apply (le_eq_iff 𝔹 (G.at_node a) (K.at_node c) _).mpr
        constructor
        · intro d
          have hd := ((le_eq_iff 𝔹 (G.at_node a) (H.at_node b) _).mp (𝔹.le_refl _)).1 d
          apply 𝔹.le_trans (𝔹.le_meet
            (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _))
            (𝔹.le_trans (𝔹.meet_mono (𝔹.meet_le_left _ _) (𝔹.le_refl _)) hd))
          exact mem_step 𝔹 (G.at_node d) (H.at_node b) (K.at_node c)
            (fun e f => ih d d.2 e f)
        · intro d
          have hd := ((le_eq_iff 𝔹 (H.at_node b) (K.at_node c) _).mp (𝔹.le_refl _)).2 d
          have hg : 𝔹.le
              (𝔹.meet (𝔹.meet (bv_eq 𝔹 (G.at_node a) (H.at_node b))
                (bv_eq 𝔹 (H.at_node b) (K.at_node c))) (K.val d c))
              (bv_eq 𝔹 (H.at_node b) (G.at_node a)) := by
            rw [eq_symm 𝔹 (H.at_node b) (G.at_node a)]
            exact 𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_left _ _)
          apply 𝔹.le_trans (𝔹.le_meet hg
            (𝔹.le_trans (𝔹.meet_mono (𝔹.meet_le_right _ _) (𝔹.le_refl _)) hd))
          apply mem_step 𝔹 (K.at_node d) (H.at_node b) (G.at_node a)
          intro e f
          rw [eq_symm 𝔹 (K.at_node d) ((H.at_node b).at_node e),
            eq_symm 𝔹 ((H.at_node b).at_node e) ((G.at_node a).at_node f),
            eq_symm 𝔹 (K.at_node d) ((G.at_node a).at_node f), 𝔹.meet_comm]
          exact ih f f.2 e d
  exact h G.root H.root K.root

theorem mem_right (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) (K : BV_graph.{x, v} B) :
    𝔹.le (𝔹.meet (bv_eq 𝔹 H K) (bv_mem 𝔹 G H)) (bv_mem 𝔹 G K) :=
  mem_step 𝔹 G H K (fun b c => eq_trans 𝔹 G (H.at_node b) (K.at_node c))

theorem mem_left (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) (K : BV_graph.{x, v} B) :
    𝔹.le (𝔹.meet (bv_eq 𝔹 G H) (bv_mem 𝔹 G K)) (bv_mem 𝔹 H K) := by
  rw [bv_mem, 𝔹.meet_iSup]
  apply (𝔹.iSup_le_iff _ _).mpr
  intro c
  rw [𝔹.meet_left_comm, eq_symm 𝔹 G H]
  exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (eq_trans 𝔹 H G (K.at_node c)))
    (mem_intro 𝔹 H K c)

/-- 同时替换元素与集合时，两个等号条件共同控制隶属值。 -/
theorem mem_congr (G : BV_graph.{u, v} B) (G' : BV_graph.{w, v} B)
    (H : BV_graph.{x, v} B) (H' : BV_graph.{y, v} B) :
    𝔹.le (𝔹.meet (𝔹.meet (bv_eq 𝔹 G G') (bv_eq 𝔹 H H')) (bv_mem 𝔹 G H))
      (bv_mem 𝔹 G' H') :=
  𝔹.le_trans (𝔹.le_meet
    (𝔹.le_trans (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _))
    (𝔹.le_trans (𝔹.meet_mono (𝔹.meet_le_left _ _) (𝔹.le_refl _)) (mem_left 𝔹 G G' H)))
    (mem_right 𝔹 G' H H')

theorem eq_congr_right (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B)
    (K : BV_graph.{x, v} B) (h : bv_eq 𝔹 H K = 𝔹.top) : bv_eq 𝔹 G H = bv_eq 𝔹 G K := by
  apply 𝔹.le_antisymm
  · simpa only [h, BA_alg.meet_top] using eq_trans 𝔹 G H K
  · have k := (eq_symm 𝔹 K H).trans h
    simpa only [k, BA_alg.meet_top] using eq_trans 𝔹 G K H

/-- 保留每个成员及其标签的图映射给出顶值等同。 -/
theorem eq_of_map (G : BV_graph.{u, v} B) (H : BV_graph.{w, v} B) (f : G.Domain → H.Domain)
    (hr : f G.root = H.root) (hf : ∀ a b, G.mem a b → H.mem (f a) (f b))
    (hv : ∀ a b, G.mem a b → H.val (f a) (f b) = G.val a b)
    (hb : ∀ b c, H.mem c (f b) → ∃ a, G.mem a b ∧ f a = c) : bv_eq 𝔹 G H = 𝔹.top := by
  have h (a : G.Domain) : bv_eq 𝔹 (G.at_node a) (H.at_node (f a)) = 𝔹.top := by
    induction a using G.wf.induction with
    | h a ih =>
        apply (𝔹.top_le_iff _).mp
        apply (le_eq_iff 𝔹 (G.at_node a) (H.at_node (f a)) _).mpr
        constructor
        · intro b
          have k := mem_intro 𝔹 (G.at_node b) (H.at_node (f a)) ⟨f b, hf b a b.2⟩
          simpa only [hv b a b.2, ih b b.2, BA_alg.meet_top, BA_alg.top_meet] using k
        · intro c
          obtain ⟨b, hba, hbc⟩ := hb a c c.2
          have he : bv_eq 𝔹 (H.at_node c) (G.at_node b) = 𝔹.top := by
            rw [← hbc, eq_symm, ih b hba]
          have hv' : H.val c (f a) = G.val b a := by rw [← hbc]; exact hv b a hba
          have k := mem_intro 𝔹 (H.at_node c) (G.at_node a) ⟨b, hba⟩
          simpa only [he, hv', BA_alg.meet_top, BA_alg.top_meet] using k
  simpa only [hr] using h G.root

/-- 布尔条件下的逐元素双向包含推出名称等同。 -/
theorem le_eq_of_mem (G H : BV_graph.{u, v} B) (c : B)
    (h : ∀ K : BV_graph.{u, v} B, 𝔹.le (𝔹.meet c (bv_mem 𝔹 K G)) (bv_mem 𝔹 K H))
    (k : ∀ K : BV_graph.{u, v} B, 𝔹.le (𝔹.meet c (bv_mem 𝔹 K H)) (bv_mem 𝔹 K G)) :
    𝔹.le c (bv_eq 𝔹 G H) :=
  (le_eq_iff 𝔹 G H c).mpr ⟨
    fun a => 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (mem_root 𝔹 G a)) (h (G.at_node a)),
    fun b => 𝔹.le_trans (𝔹.meet_mono (𝔹.le_refl _) (mem_root 𝔹 H b)) (k (H.at_node b))⟩

end YesMetaZFC.Model.Boolean.BV_graph
