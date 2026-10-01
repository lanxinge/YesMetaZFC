import YesMetaZFC.Model.Forcing.Internal.Names.Realization
import YesMetaZFC.Model.Forcing.Internal.Check.Valuation

/-! # 规范名称递归的小图地模型实例

使用实际小图集合操作实现递归所需片段，再调用同一通用递归定理。
构造证书的选择只留在 Prop 存在证明中，不导出不可计算的名称选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SmallGraph
universe u
attribute [local implicit_reducible] sg_model Definitional.Project.FirstOrderSemantics.reduct

theorem sg_mem_ind_l : Mem_ind_d sg_structure.{u} := by
  intro n φ ρ h x
  exact SG_set.mem_wf.induction x h

/-- 所有操作直接由小图并合、收集与分离证明，无额外递归假设。 -/
theorem sg_check_ops_l : Check_ops_d sg_structure.{u} where
  pair := SG_set.pair
  union := SG_set.union
  collect b x h := by
    obtain ⟨T, hT⟩ := SG_set.collection x
      (fun y F => Check_graph_d sg_structure b F ∧ ∃ t, Entry_d sg_structure y t F) h
    obtain ⟨C, hC⟩ := SG_set.separation T (Check_graph_d sg_structure b)
    refine ⟨C, fun F hF => ((hC F).mp hF).2, ?_⟩
    intro y hy
    obtain ⟨F, hF, hf, t, ht⟩ := hT y hy
    exact ⟨F, t, (hC F).mpr ⟨hF, hf⟩, ht⟩
  image b F x h hu := by
    let R (y p : SG_set.{u}) := ∃ s, Entry_d sg_structure y s F ∧ KPair_d sg_structure p s b
    obtain ⟨T, hT⟩ := SG_set.collection x R (fun y hy => by
      obtain ⟨s, hs⟩ := h y hy
      obtain ⟨p, hp⟩ := sg_kpair_l.total s b
      exact ⟨p, s, hs, hp⟩)
    obtain ⟨t, ht⟩ := SG_set.separation T (fun p => ∃ y, sg_structure.mem y x ∧ R y p)
    refine ⟨t, fun p => (ht p).trans ?_⟩
    constructor
    · rintro ⟨_, y, hy, s, hs, hp⟩
      exact ⟨y, s, hy, hs, hp⟩
    · rintro ⟨y, s, hy, hs, hp⟩
      obtain ⟨q, hq, a, ha, hqa⟩ := hT y hy
      have he := kpair_unique_l sg_structure sg_extensional ((hu y hy s a hs ha) ▸ hp) hqa
      exact ⟨he.symm ▸ hq, y, hy, s, hs, hp⟩

theorem sg_check_range_l (F : SG_set.{u}) :
    ∃ S, ∀ t, sg_structure.mem t S ↔ ∃ x, Entry_d sg_structure x t F := by
  obtain ⟨A, hA⟩ := SG_set.union F
  obtain ⟨D, hD⟩ := SG_set.union A
  obtain ⟨S, hS⟩ := SG_set.separation D (fun t => ∃ x, Entry_d sg_structure x t F)
  refine ⟨S, fun t => (hS t).trans ?_⟩
  constructor
  · exact And.right
  · rintro ⟨x, p, hp, hpf⟩
    obtain ⟨v, hv, htv⟩ := (kpair_union_l sg_structure hp t).mpr (Or.inr rfl)
    exact ⟨(hD t).mpr ⟨v, (hA v).mpr ⟨p, hpf, hv⟩, htv⟩, x, p, hp, hpf⟩

/-- 小图地模型的无权呈现解释为原对象本身。 -/
theorem sg_ground_l (x : SG_set.{u}) : Ground_d sg_structure x x := by
  induction x using Quotient.inductionOn with
  | _ G =>
    refine ⟨G, ⟨fun a => SG_set.mk (G.at_node a), rfl, ?_, ?_⟩, rfl⟩
    · intro a d h
      exact (SG_set.mem_mk (G.at_node d) _).mpr ⟨a, h, rfl⟩
    · intro d y hy
      obtain ⟨a, ha, he⟩ := (SG_set.mem_mk (G.at_node d) y).mp hy
      exact ⟨a, ha, he.symm⟩

theorem sg_check_val_l {B b x t : SG_set.{u}} (hb : b ∈ B)
    (ht : Check_d sg_structure b x t) (U : SG_set.{u} → Prop) (hU : U b) :
    Val_d sg_structure B U t x :=
  check_val_exists_l sg_structure sg_extensional sg_mem_ind_l SG_set.pair sg_check_range_l
    SG_set.mem_wf sg_setlike_l (B := B) (b := b) hb ht (sg_ground_l x) U hU

/-- 原小图规范名称入口现在也走通用内部递归，并同时返回规范性与唯一性。 -/
theorem sg_check_exists_l {B b : SG_set.{u}} (hb : b ∈ B) (x : SG_set.{u}) :
    ∃ t, Check_d sg_structure b x t ∧ Name_d sg_structure B t ∧
      (∀ s, Check_d sg_structure b x s → s = t) ∧
      ∀ U : SG_set.{u} → Prop, U b → Val_d sg_structure B U t x := by
  obtain ⟨t, ht⟩ := check_exists_l sg_structure sg_extensional sg_mem_ind_l sg_check_ops_l b x
  exact ⟨t, ht, check_name_l sg_structure sg_check_range_l (B := B) (b := b) hb ht,
    fun s hs => check_unique_l sg_structure sg_extensional sg_mem_ind_l b x s t hs ht,
    sg_check_val_l hb ht⟩

/-- 每个旧对象通过其实际内部规范名称进入解释扩张。 -/
theorem sg_check_ext_l {B b : SG_set.{u}} (hb : b ∈ B)
    (U : SG_set.{u} → Prop) (hU : U b) (x : SG_set.{u}) : Ext_l (sg_name_domain_l B) U x := by
  obtain ⟨t, _, _, _, hv⟩ := sg_check_exists_l hb x
  obtain ⟨G, hG, he⟩ := hv U hU
  exact ⟨G, ⟨t, hG⟩, he⟩

end YesMetaZFC.Model.Forcing.Internal
