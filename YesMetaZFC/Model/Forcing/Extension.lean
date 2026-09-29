import YesMetaZFC.Model.Forcing.Truth

/-! # 相对名称域的解释扩张

扩张载体是指定名称域的实际求值像，其隶属继承宿主小图集合。子名称封闭保证
传递性，进而得到外延性与良基性；这些性质不冒充整个 ZFC 的保持定理。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean SmallGraph
universe u v
variable {B : Type v}

/-- 名称域只要求非空和子名称封闭，地模型公理不混入这一层。 -/
structure Name_domain_l (B : Type v) where
  mem : BV_graph.{u, v} B → Prop
  inhabited : ∃ G, mem G
  child_closed : ∀ G, mem G → ∀ a : G.Child G.root, mem (G.at_node a)

/-- 给定实际种子族，加入各图的观察根及空名称，显式产生子名称封闭域。 -/
def name_span_l (𝔹 : BA_alg B) (S : BV_graph.{u, v} B → Prop) : Name_domain_l.{u, v} B where
  mem G := G = BV_graph.empty 𝔹.toPO_bot ∨ ∃ H, S H ∧ ∃ a, G = H.at_node a
  inhabited := ⟨BV_graph.empty 𝔹.toPO_bot, Or.inl rfl⟩
  child_closed := by
    rintro G (rfl | ⟨H, hH, b, rfl⟩) a
    · exact False.elim a.2
    · exact Or.inr ⟨H, hH, a.1, rfl⟩

theorem name_span_mem_l (𝔹 : BA_alg B) {S : BV_graph.{u, v} B → Prop}
    {G : BV_graph.{u, v} B} (h : S G) : (name_span_l 𝔹 S).mem G :=
  Or.inr ⟨G, h, G.root, rfl⟩

def Ext_l (N : Name_domain_l.{u, v} B) (U : B → Prop) (x : SG_set.{u}) : Prop :=
  ∃ G, N.mem G ∧ val_l U G = x

theorem ext_val_l (N : Name_domain_l.{u, v} B) (U : B → Prop)
    {G : BV_graph.{u, v} B} (h : N.mem G) : Ext_l N U (val_l U G) := ⟨G, h, rfl⟩

theorem ext_transitive_l (N : Name_domain_l.{u, v} B) (U : B → Prop)
    {x y : SG_set.{u}} (h : Ext_l N U y) (k : x ∈ y) : Ext_l N U x := by
  obtain ⟨G, hG, rfl⟩ := h
  obtain ⟨a, _, rfl⟩ := (val_mem_l U G x).mp k
  exact ext_val_l N U (N.child_closed G hG a)

/-- 直接可供现有集合论语义消费的二值隶属结构。 -/
def ext_structure_l (N : Name_domain_l.{u, v} B) (U : B → Prop) : SetTheory.Structure where
  Domain := {x : SG_set.{u} // Ext_l N U x}
  nonempty := N.inhabited.elim fun G h => ⟨⟨val_l U G, ext_val_l N U h⟩⟩
  mem x y := x.1 ∈ y.1

theorem ext_extensional_l (N : Name_domain_l.{u, v} B) (U : B → Prop) :
    SetTheory.Extensional (ext_structure_l N U) where
  eq_of_same_members := by
    intro x y h
    apply Subtype.ext
    apply SG_set.ext
    intro z
    constructor
    · intro hz
      exact (h ⟨z, ext_transitive_l N U x.2 hz⟩).mp hz
    · intro hz
      exact (h ⟨z, ext_transitive_l N U y.2 hz⟩).mpr hz

theorem ext_wf_l (N : Name_domain_l.{u, v} B) (U : B → Prop) :
    WellFounded (ext_structure_l N U).mem := InvImage.wf Subtype.val SG_set.mem_wf

/-- 一个旧集合的规范名称在名称域中，就保证该集合进入扩张。 -/
theorem ext_check_l (𝔹 : BA_alg B) (N : Name_domain_l.{u, v} B)
    (U : Filter_l 𝔹) (G : WF_graph.{u}) (h : N.mem (check_graph_l 𝔹 G)) :
    Ext_l N U.mem (SG_set.mk G) := ⟨check_graph_l 𝔹 G, h, val_check_l 𝔹 U.mem U.top_mem G⟩

/-- 扩张中两个已解释对象的原子语义，由各自实际名称的局部泛型性给出。 -/
theorem ext_atomic_l (𝔹 : CB_alg B) (N : Name_domain_l.{u, v} B)
    (U : Filter_l 𝔹.toBA_alg) (hU : U.Maximal_l) (G H : BV_graph.{u, v} B)
    (hG : N.mem G) (hH : N.mem H) (h : Name_generic_l 𝔹 U G H) :
    let x : (ext_structure_l N U.mem).Domain := ⟨val_l U.mem G, ext_val_l N U.mem hG⟩
    let y : (ext_structure_l N U.mem).Domain := ⟨val_l U.mem H, ext_val_l N U.mem hH⟩
    (U.mem (BV_graph.bv_eq 𝔹 G H) ↔ x = y) ∧
    (U.mem (BV_graph.bv_mem 𝔹 G H) ↔ (ext_structure_l N U.mem).mem x y) :=
  ⟨(val_eq_iff_l 𝔹 U hU G H h).trans ⟨fun e => Subtype.ext e, congrArg Subtype.val⟩,
    val_mem_iff_l 𝔹 U hU G H h⟩

end YesMetaZFC.Model.Forcing
