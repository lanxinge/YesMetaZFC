import YesMetaZFC.Model.Forcing.Internal.Names.Realization
import YesMetaZFC.SetTheory.Boolean.Algebra

/-! # 布尔代数的实际模型内编码

载体和序关系都由集合编码给出。有限运算接回原 Boolean_d；内部上确界只量化
模型中的集合族。构造消费已经给定的单射条件编码，不选择逆函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open Boolean SmallGraph SetTheory
universe u
variable {B : Type u}

def order_set_l (r : B → B → Prop) (c : B → WF_graph.{u}) : SG_set.{u} := SG_set.mk (WF_graph.root_sum
  (fun p : {p : B × B // r p.1 p.2} => kpair_graph_l (c p.1.1) (c p.1.2)))

attribute [local implicit_reducible] sg_model Definitional.Project.FirstOrderSemantics.reduct

theorem order_mem_l (r : B → B → Prop) (c : B → WF_graph.{u})
    (hc : Function.Injective (fun b => SG_set.mk (c b))) (a b : B) :
    sg_structure.PairMember sg_kpair_l (SG_set.mk (c a)) (SG_set.mk (c b)) (order_set_l r c) ↔
      r a b := by
  constructor
  · rintro ⟨p, hp, hpr⟩
    obtain ⟨q, rfl⟩ := (SG_set.mem_sum _ p).mp hpr
    obtain ⟨ha, hb⟩ := kpair_injective_l sg_structure hp (kpair_graph_spec_l _ _)
    exact hc ha ▸ hc hb ▸ q.2
  · intro h
    exact ⟨SG_set.mk (kpair_graph_l (c a) (c b)), kpair_graph_spec_l _ _,
      (SG_set.mem_sum _ _).mpr ⟨⟨(a, b), h⟩, rfl⟩⟩

variable (𝔹 : BA_alg B) (c : B → WF_graph.{u})
  (hc : Function.Injective (fun b => SG_set.mk (c b)))
include hc

theorem meet_spec_l (a b : B) (m : SG_set.{u}) :
    BooleanZF.Meet_d sg_kpair_l (condition_set_l c) (order_set_l 𝔹.le c)
      (SG_set.mk (c a)) (SG_set.mk (c b)) m ↔ m = SG_set.mk (c (𝔹.meet a b)) := by
  constructor
  · rintro ⟨hm, h⟩
    obtain ⟨x, rfl⟩ := (SG_set.mem_sum c m).mp hm
    have hw w : 𝔹.le w x ↔ 𝔹.le w a ∧ 𝔹.le w b := by
      simpa only [order_mem_l 𝔹.le c hc] using h (SG_set.mk (c w)) ((SG_set.mem_sum c _).mpr ⟨w, rfl⟩)
    exact congrArg (fun x => SG_set.mk (c x)) (𝔹.le_antisymm
      ((𝔹.le_meet_iff _ _ _).mpr ((hw x).mp (𝔹.le_refl x)))
      ((hw _).mpr ⟨𝔹.meet_le_left _ _, 𝔹.meet_le_right _ _⟩))
  · rintro rfl
    refine ⟨(SG_set.mem_sum c _).mpr ⟨𝔹.meet a b, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨x, rfl⟩ := (SG_set.mem_sum c z).mp hz
    rw [order_mem_l 𝔹.le c hc, order_mem_l 𝔹.le c hc, order_mem_l 𝔹.le c hc]
    exact 𝔹.le_meet_iff x a b

theorem imp_spec_l (a b : B) (m : SG_set.{u}) :
    BooleanZF.Imp_d sg_kpair_l (condition_set_l c) (order_set_l 𝔹.le c)
      (SG_set.mk (c a)) (SG_set.mk (c b)) m ↔ m = SG_set.mk (c (𝔹.imp a b)) := by
  have hk x :
      (∀ z, BooleanZF.Meet_d sg_kpair_l (condition_set_l c) (order_set_l 𝔹.le c)
        (SG_set.mk (c x)) (SG_set.mk (c a)) z →
          sg_structure.PairMember sg_kpair_l z (SG_set.mk (c b)) (order_set_l 𝔹.le c)) ↔
        𝔹.le x (𝔹.imp a b) := by
    rw [𝔹.le_imp_iff]
    constructor
    · intro h
      exact (order_mem_l 𝔹.le c hc _ _).mp (h _ ((meet_spec_l 𝔹 c hc x a _).mpr rfl))
    · intro h z hz
      rw [(meet_spec_l 𝔹 c hc x a z).mp hz]
      exact (order_mem_l 𝔹.le c hc _ _).mpr h
  constructor
  · rintro ⟨hm, h⟩
    obtain ⟨x, rfl⟩ := (SG_set.mem_sum c m).mp hm
    have hw w : 𝔹.le w x ↔ 𝔹.le w (𝔹.imp a b) :=
      (order_mem_l 𝔹.le c hc w x).symm.trans
        ((h (SG_set.mk (c w)) ((SG_set.mem_sum c _).mpr ⟨w, rfl⟩)).trans (hk w))
    exact congrArg (fun x => SG_set.mk (c x))
      (𝔹.le_antisymm ((hw x).mp (𝔹.le_refl _)) ((hw _).mpr (𝔹.le_refl _)))
  · rintro rfl
    refine ⟨(SG_set.mem_sum c _).mpr ⟨𝔹.imp a b, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨x, rfl⟩ := (SG_set.mem_sum c z).mp hz
    exact (order_mem_l 𝔹.le c hc _ _).trans (hk x).symm

/-- 原内部布尔代数合同由载体、序关系和显式运算见证逐项实现。 -/
theorem boolean_model_l : BooleanZF.Boolean_d sg_kpair_l (condition_set_l c)
    (order_set_l 𝔹.le c) (SG_set.mk (c 𝔹.bot)) where
  order := {
    refl := by
      intro a ha
      obtain ⟨a, rfl⟩ := (SG_set.mem_sum c _).mp ha
      exact (order_mem_l 𝔹.le c hc _ _).mpr (𝔹.le_refl a)
    trans := by
      intro a b d ha hb hd h k
      obtain ⟨a, rfl⟩ := (SG_set.mem_sum c _).mp ha
      obtain ⟨b, rfl⟩ := (SG_set.mem_sum c _).mp hb
      obtain ⟨d, rfl⟩ := (SG_set.mem_sum c _).mp hd
      exact (order_mem_l 𝔹.le c hc _ _).mpr
        (𝔹.le_trans ((order_mem_l 𝔹.le c hc _ _).mp h) ((order_mem_l 𝔹.le c hc _ _).mp k))
    antisymm := by
      intro a b ha hb h k
      obtain ⟨a, rfl⟩ := (SG_set.mem_sum c _).mp ha
      obtain ⟨b, rfl⟩ := (SG_set.mem_sum c _).mp hb
      exact congrArg (fun x => SG_set.mk (c x))
        (𝔹.le_antisymm ((order_mem_l 𝔹.le c hc _ _).mp h) ((order_mem_l 𝔹.le c hc _ _).mp k)) }
  bot_mem := (SG_set.mem_sum c _).mpr ⟨𝔹.bot, rfl⟩
  bot_le := by
    intro a ha
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum c _).mp ha
    exact (order_mem_l 𝔹.le c hc _ _).mpr (𝔹.bot_le a)
  meet := by
    intro a b ha hb
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum c _).mp ha
    obtain ⟨b, rfl⟩ := (SG_set.mem_sum c _).mp hb
    exact ⟨_, (meet_spec_l 𝔹 c hc a b _).mpr rfl⟩
  imp := by
    intro a b ha hb
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum c _).mp ha
    obtain ⟨b, rfl⟩ := (SG_set.mem_sum c _).mp hb
    exact ⟨_, (imp_spec_l 𝔹 c hc a b _).mpr rfl⟩
  double_neg := by
    intro a b d ha hb hd
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum c _).mp ha
    rw [(imp_spec_l 𝔹 c hc a 𝔹.bot b).mp hb] at hd
    simpa only [𝔹.double_neg] using (imp_spec_l 𝔹 c hc (𝔹.neg a) 𝔹.bot d).mp hd

/-- 对模型中的集合族构造内部上确界，不把其元素替换为宿主任意谓词参数。 -/
theorem sup_exists_l (C : Sup_order B) (S : SG_set.{u})
    (hS : ∀ z, z ∈ S → z ∈ condition_set_l c) :
    ∃ a, a ∈ condition_set_l c ∧
      (∀ b, b ∈ S → sg_structure.PairMember sg_kpair_l b a (order_set_l C.le c)) ∧
      ∀ d, d ∈ condition_set_l c →
        (∀ b, b ∈ S → sg_structure.PairMember sg_kpair_l b d (order_set_l C.le c)) →
          sg_structure.PairMember sg_kpair_l a d (order_set_l C.le c) := by
  let a := C.sup (fun b => SG_set.mk (c b) ∈ S)
  refine ⟨SG_set.mk (c a), (SG_set.mem_sum c _).mpr ⟨a, rfl⟩, ?_, ?_⟩
  · intro b hb
    obtain ⟨x, rfl⟩ := (SG_set.mem_sum c b).mp (hS b hb)
    exact (order_mem_l C.le c hc x a).mpr (C.le_sup hb)
  · intro d hd h
    obtain ⟨x, rfl⟩ := (SG_set.mem_sum c d).mp hd
    apply (order_mem_l C.le c hc a x).mpr
    exact (C.sup_le_iff _ _).mpr (fun b hb =>
      (order_mem_l C.le c hc b x).mp (h (SG_set.mk (c b)) hb))

end YesMetaZFC.Model.Forcing.Internal
