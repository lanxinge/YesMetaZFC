import YesMetaZFC.Model.SmallGraph.Sets

/-! # 无穷集合的实际小图

节点使用单位元列表，长度给出有限序数；另加一个以全部有限节点为成员的根。
列表与图节点都保持 `Type u`，不借助升层的自然数副本或树名称宇宙。
-/

namespace YesMetaZFC.Model.SmallGraph
universe u

def omega_edge : Option (List PUnit.{u+1}) → Option (List PUnit.{u+1}) → Prop
  | some a, some b => a.length < b.length
  | some _, none => True
  | none, _ => False

/-- ω 的有根小图；良基性直接由列表长度的自然数良基性证明。 -/
def omega_graph : WF_graph.{u} where
  Domain := Option (List PUnit.{u+1})
  nonempty := ⟨none⟩
  mem := omega_edge
  root := none
  wf := by
    have h (a : List PUnit.{u+1}) : Acc omega_edge (some a) := by
      apply (InvImage.wf (fun a : List PUnit.{u+1} => a.length) Nat.lt_wfRel.wf).induction a
      intro a ih
      refine Acc.intro _ ?_
      intro b hb
      cases b with
      | none => exact hb.elim
      | some b => exact ih b hb
    refine ⟨fun a => ?_⟩
    cases a with
    | some a => exact h a
    | none =>
        refine Acc.intro _ ?_
        intro a ha
        cases a with
        | none => exact ha.elim
        | some a => exact h a

namespace SG_set

def omega : SG_set.{u} := mk omega_graph
def omega_piece (a : List PUnit.{u+1}) : SG_set.{u} := mk (omega_graph.at_node (some a))

/-- 有限节点的成员恰好是更短的节点所表示的集合。 -/
theorem omega_piece_mem (a : List PUnit.{u+1}) (z : SG_set.{u}) :
    z ∈ omega_piece a ↔ ∃ b, b.length < a.length ∧ z = omega_piece b := by
  refine (mem_mk (omega_graph.at_node (some a)) z).trans ?_
  constructor
  · rintro ⟨b, hb, hz⟩
    cases b with
    | none => exact hb.elim
    | some b => exact ⟨b, hb, hz⟩
  · rintro ⟨b, hb, hz⟩
    exact ⟨some b, hb, hz⟩

theorem omega_piece_congr {a b : List PUnit.{u+1}} (h : a.length = b.length) :
    omega_piece a = omega_piece b := by
  apply ext
  intro z
  rw [omega_piece_mem, omega_piece_mem, h]

/-- 添一个单位元的列表节点实现集合论后继。 -/
theorem omega_piece_step (a : List PUnit.{u+1}) (z : SG_set.{u}) :
    z ∈ omega_piece (PUnit.unit :: a) ↔ z ∈ omega_piece a ∨ z = omega_piece a := by
  rw [omega_piece_mem]
  constructor
  · rintro ⟨b, hb, hz⟩
    by_cases h : b.length < a.length
    · exact Or.inl ((omega_piece_mem a z).mpr ⟨b, h, hz⟩)
    · exact Or.inr (hz.trans (omega_piece_congr (by simp only [List.length_cons] at hb; omega)))
  · rintro (h | h)
    · obtain ⟨b, hb, hz⟩ := (omega_piece_mem a z).mp h
      exact ⟨b, by simp only [List.length_cons]; omega, hz⟩
    · exact ⟨a, by simp, h⟩

/-- 图根实际满足原无穷公理的空集与后继封闭条件。 -/
theorem infinity :
    (∃ e : SG_set.{u}, (∀ z, ¬ z ∈ e) ∧ e ∈ omega) ∧
      ∀ x : SG_set.{u}, x ∈ omega →
        ∃ s, (∀ z, z ∈ s ↔ z ∈ x ∨ z = x) ∧ s ∈ omega := by
  constructor
  · refine ⟨omega_piece [], ?_, (mem_mk omega_graph _).mpr ⟨some [], trivial, rfl⟩⟩
    intro z hz
    obtain ⟨b, hb, _⟩ := (omega_piece_mem [] z).mp hz
    exact Nat.not_lt_zero _ hb
  · intro x hx
    obtain ⟨a, ha, hx⟩ := (mem_mk omega_graph x).mp hx
    cases a with
    | none => exact ha.elim
    | some a =>
        refine ⟨omega_piece (PUnit.unit :: a), ?_,
          (mem_mk omega_graph _).mpr ⟨some (PUnit.unit :: a), trivial, rfl⟩⟩
        intro z
        simpa only [omega_piece, hx] using omega_piece_step a z

end SG_set
end YesMetaZFC.Model.SmallGraph
