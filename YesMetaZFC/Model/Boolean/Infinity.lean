import YesMetaZFC.Model.Boolean.Closure
import YesMetaZFC.Model.SmallGraph.Infinity

/-! # 布尔宇宙中的无穷集合

复用单位元列表构成的原 ω 小图，所有成员边赋顶值。
有限节点的后继方程直接按列表长度核验。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B)

def omega : BV_graph.{u, u} B where
  toWF_graph := SmallGraph.omega_graph
  val _ _ := 𝔹.top

abbrev omega_piece (a : List PUnit.{u+1}) := (omega 𝔹).at_node (some a)

theorem omega_piece_mem (a : List PUnit.{u+1}) (G : BV_graph.{u, u} B) :
    bv_mem 𝔹 G (omega_piece 𝔹 a) =
      𝔹.iSup (fun b : {b : List PUnit.{u+1} // b.length < a.length} => bv_eq 𝔹 G (omega_piece 𝔹 b.1)) := by
  apply 𝔹.le_antisymm
  · apply (𝔹.iSup_le_iff _ _).mpr
    rintro ⟨b, hb⟩
    cases b with
    | none => exact False.elim hb
    | some b =>
        exact 𝔹.le_trans (𝔹.meet_le_right _ _)
          (𝔹.le_iSup (fun b : {b : List PUnit.{u+1} // b.length < a.length} =>
            bv_eq 𝔹 G (omega_piece 𝔹 b.1)) ⟨b, hb⟩)
  · apply (𝔹.iSup_le_iff _ _).mpr
    intro b
    exact 𝔹.le_trans (𝔹.le_meet (𝔹.le_top _) (𝔹.le_refl _))
      (mem_intro 𝔹 G (omega_piece 𝔹 a) ⟨some b.1, b.2⟩)

theorem omega_piece_step (a : List PUnit.{u+1}) (G : BV_graph.{u, u} B) :
    bv_mem 𝔹 G (omega_piece 𝔹 (.unit :: a)) =
      𝔹.join (bv_mem 𝔹 G (omega_piece 𝔹 a)) (bv_eq 𝔹 G (omega_piece 𝔹 a)) := by
  let v (n : Nat) (b : {b : List PUnit.{u+1} // b.length < n}) := bv_eq 𝔹 G (omega_piece 𝔹 b.1)
  rw [omega_piece_mem]
  apply 𝔹.le_antisymm
  · apply (𝔹.iSup_le_iff _ _).mpr
    intro b
    by_cases h : b.1.length < a.length
    · apply 𝔹.le_trans _ (𝔹.le_join_left _ _)
      rw [omega_piece_mem]
      exact 𝔹.le_iSup (v a.length) ⟨b.1, h⟩
    · have he : b.1 = a := List.ext_getElem (by have := b.2; simp only [List.length_cons] at this; omega)
        (fun _ _ _ => Subsingleton.elim _ _)
      rw [he]; exact 𝔹.le_join_right _ _
  · apply (𝔹.join_le_iff _ _ _).mpr
    constructor
    · rw [omega_piece_mem, 𝔹.iSup_le_iff]
      intro b
      exact 𝔹.le_iSup (v (a.length + 1)) ⟨b.1, by have := b.2; omega⟩
    · exact 𝔹.le_iSup (v (a.length + 1)) ⟨a, by simp⟩

theorem omega_piece_root (a : List PUnit.{u+1}) : bv_mem 𝔹 (omega_piece 𝔹 a) (omega 𝔹) = 𝔹.top :=
  (𝔹.top_le_iff _).mp (mem_root 𝔹 (omega 𝔹) ⟨some a, trivial⟩)

def successor_value (G S : BV_graph.{u, u} B) : B := 𝔹.iInf (fun H : BV_graph.{u, u} B =>
  𝔹.iff (bv_mem 𝔹 H S) (𝔹.join (bv_mem 𝔹 H G) (bv_eq 𝔹 H G)))

theorem successor_stable (S : BV_graph.{u, u} B) : Stable 𝔹 (fun G => successor_value 𝔹 G S) :=
  stable_inf 𝔹 _ (fun H => stable_iff 𝔹 (stable_const 𝔹 _)
    (stable_join 𝔹 (stable_set 𝔹 H) (stable_eq 𝔹 H)))

/-- ω 包含空集并在完整布尔语义下对后继封闭。 -/
theorem infinity :
    (∃ E : BV_graph.{u, u} B, (∀ H : BV_graph.{u, u} B, bv_mem 𝔹 H E = 𝔹.bot) ∧
      bv_mem 𝔹 E (omega 𝔹) = 𝔹.top) ∧
    𝔹.le 𝔹.top (𝔹.iInf (fun G : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 G (omega 𝔹))
      (𝔹.iSup (fun S : BV_graph.{u, u} B => 𝔹.meet (successor_value 𝔹 G S) (bv_mem 𝔹 S (omega 𝔹)))))) := by
  constructor
  · refine ⟨omega_piece 𝔹 [], fun H => ?_, omega_piece_root 𝔹 []⟩
    rw [omega_piece_mem]
    exact 𝔹.le_antisymm ((𝔹.iSup_le_iff _ _).mpr (fun b => False.elim (Nat.not_lt_zero _ b.2))) (𝔹.bot_le _)
  · apply (bounded_all 𝔹 (omega 𝔹) _ (stable_sup 𝔹 _ (fun S =>
      stable_meet 𝔹 (successor_stable 𝔹 S) (stable_const 𝔹 _))) 𝔹.top).mpr
    rintro ⟨a, ha⟩
    cases a with
    | none => exact False.elim ha
    | some a =>
      apply 𝔹.le_trans _ (𝔹.le_iSup (fun S : BV_graph.{u, u} B =>
        𝔹.meet (successor_value 𝔹 (omega_piece 𝔹 a) S) (bv_mem 𝔹 S (omega 𝔹))) (omega_piece 𝔹 (.unit :: a)))
      rw [𝔹.top_meet, omega_piece_root]
      apply 𝔹.le_meet _ (𝔹.le_refl _)
      exact (𝔹.le_iInf_iff _ _).mpr (fun H => (𝔹.valid_iff_iff _ _).mpr (omega_piece_step 𝔹 a H))

end YesMetaZFC.Model.Boolean.BV_graph
