import YesMetaZFC.Model.SmallGraph.Sets

/-! # 小图模型的分离、幂集与收集

幂集的外层指标是小节点域上的谓词，仍属于 `Type u`。
全收集只使用已证明的小指标族收集；原生选择只出现在存在性证明中。
-/

namespace YesMetaZFC.Model.SmallGraph.SG_set
universe u

/-- 任意背景谓词的分离，由根成员节点的子类型直接构造。 -/
theorem separation (x : SG_set.{u}) (p : SG_set.{u} → Prop) :
    ∃ y : SG_set.{u}, ∀ z, z ∈ y ↔ z ∈ x ∧ p z := by
  induction x using Quotient.inductionOn with
  | _ G =>
      let F (i : {a : G.Domain // G.mem a G.root ∧ p (mk (G.at_node a))}) := G.at_node i.1
      refine ⟨mk (WF_graph.root_sum F), fun z => (mem_sum F z).trans ?_⟩
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(mem_mk G _).mpr ⟨i.1, i.2.1, rfl⟩, i.2.2⟩
      · rintro ⟨hz, hp⟩
        obtain ⟨a, ha, rfl⟩ := (mem_mk G z).mp hz
        exact ⟨⟨a, ha, hp⟩, rfl⟩

/-- 全幂集由所有根成员子族的图并合构造，不提高节点或模型载体层级。 -/
theorem power (x : SG_set.{u}) :
    ∃ y : SG_set.{u}, ∀ z, z ∈ y ↔ ∀ w, w ∈ z → w ∈ x := by
  induction x using Quotient.inductionOn with
  | _ G =>
      let F (p : G.Domain → Prop) := WF_graph.root_sum
        (fun a : {a : G.Domain // G.mem a G.root ∧ p a} => G.at_node a.1)
      refine ⟨mk (WF_graph.root_sum F), fun z => (mem_sum F z).trans ?_⟩
      constructor
      · rintro ⟨p, rfl⟩ w hw
        obtain ⟨a, rfl⟩ := (mem_sum _ w).mp hw
        exact (mem_mk G _).mpr ⟨a.1, a.2.1, rfl⟩
      · intro hz
        refine ⟨fun a => mk (G.at_node a) ∈ z, ext (fun w => ?_)⟩
        constructor
        · intro hw
          obtain ⟨a, ha, rfl⟩ := (mem_mk G w).mp (hz w hw)
          exact (mem_sum _ _).mpr ⟨⟨a, ha, hw⟩, rfl⟩
        · intro hw
          obtain ⟨a, rfl⟩ := (mem_sum _ w).mp hw
          exact a.2.2

/-- 任意关系的全收集；不额外要求关系为函数。 -/
theorem collection (x : SG_set.{u}) (r : SG_set.{u} → SG_set.{u} → Prop)
    (h : ∀ a, a ∈ x → ∃ b, r a b) :
    ∃ y : SG_set.{u}, ∀ a, a ∈ x → ∃ b, b ∈ y ∧ r a b := by
  obtain ⟨ι, f, hf⟩ := small_presentation x
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice (fun i => h (f i) ((hf _).mpr ⟨i, rfl⟩))
  obtain ⟨y, hy⟩ := small_collect g
  refine ⟨y, fun a ha => ?_⟩
  obtain ⟨i, rfl⟩ := (hf a).mp ha
  exact ⟨g i, (hy _).mpr ⟨i, rfl⟩, hg i⟩

/-- 两个给定图的二元并合给出无序对。 -/
theorem pair (x y : SG_set.{u}) : ∃ p : SG_set.{u}, ∀ z, z ∈ p ↔ z = x ∨ z = y := by
  induction x using Quotient.inductionOn with
  | _ G =>
      induction y using Quotient.inductionOn with
      | _ H =>
          let F : PUnit.{u+1} ⊕ PUnit.{u+1} → WF_graph.{u}
            | .inl _ => G
            | .inr _ => H
          refine ⟨mk (WF_graph.root_sum F), fun z => (mem_sum F z).trans ?_⟩
          constructor
          · rintro ⟨i, hi⟩
            cases i with
            | inl _ => exact Or.inl hi
            | inr _ => exact Or.inr hi
          · rintro (h | h)
            · exact ⟨.inl PUnit.unit, h⟩
            · exact ⟨.inr PUnit.unit, h⟩

/-- 并集由原图中长度为二的成员路径收集而成。 -/
theorem union (x : SG_set.{u}) :
    ∃ y : SG_set.{u}, ∀ z, z ∈ y ↔ ∃ a, a ∈ x ∧ z ∈ a := by
  induction x using Quotient.inductionOn with
  | _ G =>
      let F (p : {p : G.Domain × G.Domain // G.mem p.1 G.root ∧ G.mem p.2 p.1}) :=
        G.at_node p.1.2
      refine ⟨mk (WF_graph.root_sum F), fun z => (mem_sum F z).trans ?_⟩
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨mk (G.at_node p.1.1), (mem_mk G _).mpr ⟨p.1.1, p.2.1, rfl⟩,
          (mem_mk (G.at_node p.1.1) _).mpr ⟨p.1.2, p.2.2, rfl⟩⟩
      · rintro ⟨a, ha, hz⟩
        obtain ⟨n, hn, rfl⟩ := (mem_mk G a).mp ha
        obtain ⟨m, hm, h⟩ := (mem_mk (G.at_node n) z).mp hz
        exact ⟨⟨(n, m), hn, hm⟩, h⟩

end YesMetaZFC.Model.SmallGraph.SG_set
