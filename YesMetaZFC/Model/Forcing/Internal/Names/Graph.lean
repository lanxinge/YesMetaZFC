import YesMetaZFC.Model.Forcing.Internal.Names.Basic
import YesMetaZFC.Model.Forcing.External.Extension

/-! # 内部名称的小图呈现

节点取支撑集与条件集的小呈现的乘积，再添一个根。标签仍是地模型中的条件对象，
不假设内部布尔代数具有宿主任意上确界。空条件集也允许，根的非成员标签不参与求值。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open Boolean SmallGraph SetTheory
universe u v
variable (M : SetTheory.Structure.{u})

/-- 模型中每个集合有指定层级的小呈现；只要求存在，不选择全局呈现函数。 -/
def Setlike_d : Prop := ∀ x : M.Domain, ∃ (I : Type v) (f : I → M.Domain),
  ∀ z, M.mem z x ↔ ∃ i, z = f i

def node_l {I J : Type v} (t : M.Domain) (s : I → M.Domain) : Option (I × J) → M.Domain
  | none => t
  | some a => s a.1

def decode_graph_l (hM : _root_.WellFounded M.mem) {I J : Type v}
    (t : M.Domain) (s : I → M.Domain) (b : J → M.Domain) : BV_graph.{v, u} M.Domain where
  Domain := Option (I × J)
  nonempty := ⟨none⟩
  root := none
  mem a c := match a with
    | none => False
    | some a => Entry_d M (s a.1) (b a.2) (node_l M t s c)
  val a _ := match a with
    | none => t
    | some a => b a.2
  wf := ⟨fun a => (InvImage.wf (node_l M t s) hM.transGen).induction a fun a ih =>
    Acc.intro a fun c hc => by
      cases c with
      | none => exact hc.elim
      | some c => exact ih _ (entry_descent_l M hc)⟩

/-- 逐节点保留并覆盖全部内部带权成员；重复呈现同一子名称是允许的。 -/
def Rep_d (B t : M.Domain) (G : BV_graph.{v, u} M.Domain) : Prop :=
  Name_d M B t ∧ ∃ c : G.Domain → M.Domain, c G.root = t ∧
    (∀ a d, G.mem a d → Entry_d M (c a) (G.val a d) (c d)) ∧
    (∀ d s b, Entry_d M s b (c d) → ∃ a, G.mem a d ∧ c a = s ∧ G.val a d = b)

theorem decode_rep_l (hM : _root_.WellFounded M.mem) {I J : Type v}
    {B S t : M.Domain} (s : I → M.Domain) (b : J → M.Domain)
    (hs : ∀ z, M.mem z S ↔ ∃ i, z = s i) (hb : ∀ z, M.mem z B ↔ ∃ j, z = b j)
    (ht : M.mem t S) (hS : Supp_d M B S) : Rep_d M B t (decode_graph_l M hM t s b) := by
  have hn (a : Option (I × J)) : M.mem (node_l M t s a) S := by
    cases a with
    | none => exact ht
    | some a => exact (hs _).mpr ⟨a.1, rfl⟩
  refine ⟨⟨S, ht, hS⟩, node_l M t s, rfl, ?_, ?_⟩
  · intro a d h
    cases a with
    | none => exact h.elim
    | some a => exact h
  · intro d x c h
    obtain ⟨hx, hc⟩ := supp_entry_l M hS (hn d) h
    obtain ⟨i, rfl⟩ := (hs x).mp hx
    obtain ⟨j, rfl⟩ := (hb c).mp hc
    exact ⟨some (i, j), h, rfl, rfl⟩

/-- 直接从内部名称取得原节点层级的小图；所有存在见证均留在 Prop 中。 -/
theorem decode_exists_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    {B t : M.Domain} (h : Name_d M B t) : ∃ G : BV_graph.{v, u} M.Domain, Rep_d M B t G := by
  obtain ⟨S, ht, hS⟩ := h
  obtain ⟨I, s, hs⟩ := hL S
  obtain ⟨J, b, hb⟩ := hL B
  exact ⟨decode_graph_l M hM t s b, decode_rep_l M hM s b hs hb ht hS⟩

theorem rep_child_l {B t : M.Domain} {G : BV_graph.{v, u} M.Domain}
    (h : Rep_d M B t G) (a : G.Child G.root) :
    ∃ s, Entry_d M s (G.val a G.root) t ∧ Rep_d M B s (G.at_node a) := by
  obtain ⟨ht, c, hr, hf, hb⟩ := h
  have ha : Entry_d M (c a) (G.val a G.root) t := hr ▸ hf a G.root a.2
  exact ⟨c a, ha, (name_entry_l M ht ha).1, c, rfl, hf, hb⟩

/-- 同一内部名称的不同图呈现给出同一个实际求值，不需要泛型性假设。 -/
theorem rep_val_eq_l (U : M.Domain → Prop) {B t : M.Domain}
    {G H : BV_graph.{v, u} M.Domain} (h : Rep_d M B t G) (k : Rep_d M B t H) :
    val_l U G = val_l U H := by
  obtain ⟨_, c, hc, hf, hb⟩ := h
  obtain ⟨_, d, hd, kf, kb⟩ := k
  apply SG_set.mk_eq.mpr
  refine ⟨fun a b => c a = d b, ?_, hc.trans hd.symm⟩
  intro a b hab
  constructor
  · rintro a' ⟨ha, hu⟩
    have he := hf a' a ha
    rw [hab] at he
    obtain ⟨b', hb', hc', hv⟩ := kb b _ _ he
    exact ⟨b', ⟨hb', hv.symm ▸ hu⟩, hc'.symm⟩
  · rintro b' ⟨hb', hu⟩
    have he := kf b' b hb'
    rw [← hab] at he
    obtain ⟨a', ha', hd', hv⟩ := hb a _ _ he
    exact ⟨a', ⟨ha', hv.symm ▸ hu⟩, hd'⟩

def Val_d (B : M.Domain) (U : M.Domain → Prop) (t : M.Domain) (x : SG_set.{v}) : Prop :=
  ∃ G : BV_graph.{v, u} M.Domain, Rep_d M B t G ∧ val_l U G = x

theorem val_exists_unique_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    (B : M.Domain) (U : M.Domain → Prop) {t : M.Domain} (h : Name_d M B t) :
    ∃ x : SG_set.{v}, Val_d M B U t x ∧ ∀ y, Val_d M B U t y → y = x := by
  obtain ⟨G, hG⟩ := decode_exists_l M hM hL h
  refine ⟨val_l U G, ⟨G, hG, rfl⟩, ?_⟩
  rintro y ⟨H, hH, rfl⟩
  exact rep_val_eq_l M U hH hG

/-- 求值递归式直接使用地模型内的有序对成员和条件对象。 -/
theorem val_mem_l {B t : M.Domain} {U : M.Domain → Prop} {x y : SG_set.{v}}
    (h : Val_d M B U t x) : y ∈ x ↔
      ∃ s b, Entry_d M s b t ∧ U b ∧ Val_d M B U s y := by
  obtain ⟨G, hG, rfl⟩ := h
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := (Forcing.val_mem_l U G y).mp hy
    obtain ⟨s, hs, hg⟩ := rep_child_l M hG a
    exact ⟨s, G.val a G.root, hs, ha, G.at_node a, hg, rfl⟩
  · rintro ⟨s, b, hs, hu, H, hH, rfl⟩
    obtain ⟨ht, c, hr, hf, hb⟩ := hG
    obtain ⟨a, ha, hc, hv⟩ := hb G.root s b (hr ▸ hs)
    have hg : Rep_d M B s (G.at_node a) :=
      ⟨(name_entry_l M ht hs).1, c, hc, hf, hb⟩
    exact (Forcing.val_mem_l U G _).mpr
      ⟨⟨a, ha⟩, hv.symm ▸ hu, rep_val_eq_l M U hH hg⟩

/-- 内部名称的全部小图呈现接入现有相对名称域；非空性只要求存在一个内部名称。 -/
def name_domain_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    (B : M.Domain) (hN : ∃ t, Name_d M B t) : Name_domain_l.{v, u} M.Domain where
  mem G := ∃ t, Rep_d M B t G
  inhabited := by
    obtain ⟨t, ht⟩ := hN
    obtain ⟨G, hG⟩ := decode_exists_l M hM hL ht
    exact ⟨G, t, hG⟩
  child_closed := by
    rintro G ⟨t, ht⟩ a
    obtain ⟨s, _, hs⟩ := rep_child_l M ht a
    exact ⟨s, hs⟩

theorem ext_iff_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    (B : M.Domain) (hN : ∃ t, Name_d M B t) (U : M.Domain → Prop) (x : SG_set.{v}) :
    Ext_l (name_domain_l M hM hL B hN) U x ↔ ∃ t, Val_d M B U t x :=
  ⟨fun ⟨G, ⟨t, hG⟩, e⟩ => ⟨t, G, hG, e⟩,
    fun ⟨t, G, hG, e⟩ => ⟨G, ⟨t, hG⟩, e⟩⟩

end YesMetaZFC.Model.Forcing.Internal
