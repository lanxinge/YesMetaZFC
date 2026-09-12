import YesMetaZFC.Model.SmallGraph.Sets

/-!
研究用的精确归约，不是新的收集公理证明。
把一族见证缩成小的多值覆盖，与从每项选出一个见证严格区分。
此文件只留在临时研究目录，不进入正式编译层。
-/

namespace YesMetaZFC.Model.CollectionResearch
open SmallGraph
universe u v

/-- 小的多值覆盖：允许同一输入有多个见证，也允许重复呈现。 -/
def cr_cover {I : Type u} {B : Type v} (R : I → B → Prop) : Prop :=
  ∃ (J : Type u) (q : J → I) (f : J → B),
    (∀ i, ∃ j, q j = i) ∧ ∀ j, R (q j) (f j)

/-- 小覆盖与一个小候选族等价；从候选族转为覆盖时保留全部关系边。 -/
theorem cr_cover_iff {I : Type u} {B : Type v} (R : I → B → Prop) :
    cr_cover R ↔ ∃ (J : Type u) (f : J → B), ∀ i, ∃ j, R i (f j) := by
  constructor
  · rintro ⟨J, q, f, h, k⟩
    refine ⟨J, f, fun i => ?_⟩
    obtain ⟨j, rfl⟩ := h i
    exact ⟨j, k j⟩
  · rintro ⟨J, f, h⟩
    let K := {p : I × J // R p.1 (f p.2)}
    refine ⟨K, fun p => p.1.1, fun p => f p.1.2, ?_, fun p => p.2⟩
    intro i
    obtain ⟨j, hj⟩ := h i
    exact ⟨⟨(i, j), hj⟩, rfl⟩

theorem cr_cover_pointwise {I : Type u} {B : Type v} {R : I → B → Prop}
    (h : cr_cover R) : ∀ i, ∃ b, R i b := by
  obtain ⟨J, f, h⟩ := (cr_cover_iff R).mp h
  intro i
  obtain ⟨j, hj⟩ := h i
  exact ⟨f j, hj⟩

/-- 单点阶段没有收集难点；困难在从逐点陈述得到任意小阶段的统一覆盖。 -/
theorem cr_singleton {B : Type v} (P : B → Prop) :
    cr_cover (fun _ : PUnit.{u+1} => P) ↔ ∃ b, P b := by
  constructor
  · intro h
    exact cr_cover_pointwise h PUnit.unit
  · rintro ⟨b, hb⟩
    exact ⟨PUnit, id, fun _ => b, fun i => ⟨i, rfl⟩, fun _ => hb⟩

/-- 覆盖沿任意阶段映射回拉，只取纤维积，不选择覆盖纤维中的点。 -/
theorem cr_pullback {I V : Type u} {B : Type v} {R : I → B → Prop}
    (e : V → I) (h : cr_cover R) : cr_cover (fun v => R (e v)) := by
  obtain ⟨J, q, f, h, k⟩ := h
  let K := {p : V × J // q p.2 = e p.1}
  refine ⟨K, fun p => p.1.1, fun p => f p.1.2, ?_, ?_⟩
  · intro v
    obtain ⟨j, hj⟩ := h (e v)
    exact ⟨⟨(v, j), hj⟩, rfl⟩
  · intro p
    simpa only [← p.2] using k p.1.2

/--
栈语义的有界全称会检查所有小阶段及其广义元素，因而已包含统一覆盖。
只检查单点会变成 `∀ i, ∃ b, R i b`，恰好丢掉此处的关键信息。
-/
theorem cr_generic_iff {I : Type u} {B : Type v} (R : I → B → Prop) :
    (∀ (V : Type u) (e : V → I), cr_cover (fun v => R (e v))) ↔ cr_cover R :=
  ⟨fun h => h I id, fun h _ e => cr_pullback e h⟩

/--
小图载体的收集结论，恰好等价于原始图见证的小多值覆盖。
反向只对一个已给收集集取一次图呈现，随后全部根成员共享该呈现；
因此没有逐点的商代表元选择，也没有逐点的关系见证选择。
-/
theorem cr_sg_iff {I : Type u} (R : I → SG_set.{u} → Prop) :
    (∃ C : SG_set.{u}, ∀ i, ∃ y, y ∈ C ∧ R i y) ↔
      cr_cover (fun i (G : WF_graph.{u}) => R i (SG_set.mk G)) := by
  rw [cr_cover_iff]
  constructor
  · rintro ⟨C, h⟩
    induction C using Quotient.inductionOn with
    | _ G =>
      let J := {a : G.Domain // G.mem a G.root}
      refine ⟨J, fun a => G.at_node a.1, fun i => ?_⟩
      obtain ⟨y, hy, hr⟩ := h i
      obtain ⟨a, ha, rfl⟩ := (SG_set.mem_mk G y).mp hy
      exact ⟨⟨a, ha⟩, hr⟩
  · rintro ⟨J, f, h⟩
    refine ⟨SG_set.mk (WF_graph.root_sum f), fun i => ?_⟩
    obtain ⟨j, hj⟩ := h i
    exact ⟨SG_set.mk (f j), (SG_set.mem_sum f _).mpr ⟨j, rfl⟩, hj⟩

#print axioms cr_cover_iff
#print axioms cr_singleton
#print axioms cr_generic_iff
#print axioms cr_sg_iff

end YesMetaZFC.Model.CollectionResearch
