import YesMetaZFC.Model.Forcing.Internal.Names.Graph
import YesMetaZFC.Model.Forcing.Internal.Names.Closure
import YesMetaZFC.Model.SmallGraph.ZFC

/-! # 小图地模型中的实际内部名称

把原布尔名称逐节点编码成模型内的有序对集合，条件集和全体子名称支撑也直接由
小图并合构造。编码、解码与求值保持原小节点层级；不存在代表元选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open Boolean SmallGraph SetTheory
universe u

def sg_kpair_l : kpair_convention_l.Interpretation sg_structure.{u} :=
  kpair_interpretation_l sg_structure sg_extensional SG_set.pair

def pair_graph_l (G H : WF_graph.{u}) : WF_graph.{u} :=
  WF_graph.root_sum (fun i : PUnit.{u+1} ⊕ PUnit.{u+1} => i.elim (fun _ => G) (fun _ => H))

theorem pair_graph_spec_l (G H : WF_graph.{u}) :
    Pair_d sg_structure (SG_set.mk (pair_graph_l G H)) (SG_set.mk G) (SG_set.mk H) := by
  intro z
  refine (SG_set.mem_sum _ z).trans ?_
  constructor
  · rintro ⟨i, h⟩
    cases i with
    | inl _ => exact Or.inl h
    | inr _ => exact Or.inr h
  · exact fun h => h.elim (fun h => ⟨.inl PUnit.unit, h⟩) (fun h => ⟨.inr PUnit.unit, h⟩)

def kpair_graph_l (G H : WF_graph.{u}) : WF_graph.{u} :=
  pair_graph_l (pair_graph_l G G) (pair_graph_l G H)

theorem kpair_graph_spec_l (G H : WF_graph.{u}) :
    KPair_d sg_structure (SG_set.mk (kpair_graph_l G H)) (SG_set.mk G) (SG_set.mk H) :=
  ⟨SG_set.mk (pair_graph_l G G), SG_set.mk (pair_graph_l G H),
    fun z => (pair_graph_spec_l G G z).trans ⟨fun h => h.elim id id, Or.inl⟩,
    pair_graph_spec_l G H, pair_graph_spec_l _ _⟩

variable {B : Type u}

def encode_graph_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) : G.Domain → WF_graph.{u} :=
  G.wf.fix fun a ih => WF_graph.root_sum
    (fun i : G.Child a => kpair_graph_l (ih i i.2) (c (G.val i a)))

def encode_set_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) : SG_set.{u} :=
  SG_set.mk (encode_graph_l c G a)

def condition_set_l (c : B → WF_graph.{u}) : SG_set.{u} := SG_set.mk (WF_graph.root_sum c)

def coded_graph_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) : BV_graph.{u, u+1} SG_set.{u} where
  toWF_graph := G.toWF_graph
  val a b := SG_set.mk (c (G.val a b))

theorem encode_graph_eq_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) :
    encode_graph_l c G a = WF_graph.root_sum
      (fun i : G.Child a => kpair_graph_l (encode_graph_l c G i) (c (G.val i a))) := by
  rw [encode_graph_l, WellFounded.fix_eq]

theorem encode_mem_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B)
    (a : G.Domain) (p : SG_set.{u}) : p ∈ encode_set_l c G a ↔
      ∃ i : G.Child a, KPair_d sg_structure p (encode_set_l c G i) (SG_set.mk (c (G.val i a))) := by
  change p ∈ SG_set.mk (encode_graph_l c G a) ↔ _
  rw [encode_graph_eq_l, SG_set.mem_sum]
  apply exists_congr
  intro i
  exact ⟨fun h => h ▸ kpair_graph_spec_l _ _,
    fun h => kpair_unique_l sg_structure sg_extensional h (kpair_graph_spec_l _ _)⟩

/-- 整幅图的编码子名称共同组成一个实际模型集合，允许无限节点域。 -/
theorem encode_name_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) :
    Name_d sg_structure (condition_set_l c) (encode_set_l c G a) := by
  let S := SG_set.mk (WF_graph.root_sum (encode_graph_l c G))
  have hs (a : G.Domain) : encode_set_l c G a ∈ S := (SG_set.mem_sum _ _).mpr ⟨a, rfl⟩
  refine ⟨S, hs a, ?_⟩
  intro t ht p hp
  obtain ⟨d, rfl⟩ := (SG_set.mem_sum _ t).mp ht
  obtain ⟨i, hi⟩ := (encode_mem_l c G d p).mp hp
  exact ⟨encode_set_l c G i, SG_set.mk (c (G.val i d)), hi, hs i,
    (SG_set.mem_sum c _).mpr ⟨G.val i d, rfl⟩⟩

theorem encode_rep_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) :
    Rep_d sg_structure (condition_set_l c) (encode_set_l c G a) (coded_graph_l c (G.at_node a)) := by
  refine ⟨encode_name_l c G a, encode_set_l c G, rfl, ?_, ?_⟩
  · intro x y hxy
    let P := SG_set.mk (kpair_graph_l (encode_graph_l c G x) (c (G.val x y)))
    have hP : KPair_d sg_structure P (encode_set_l c G x) (SG_set.mk (c (G.val x y))) :=
      kpair_graph_spec_l _ _
    exact ⟨P, hP, (encode_mem_l c G y P).mpr ⟨⟨x, hxy⟩, hP⟩⟩
  · rintro y s b ⟨p, hp, hpy⟩
    obtain ⟨i, hi⟩ := (encode_mem_l c G y p).mp hpy
    obtain ⟨hs, hb⟩ := kpair_injective_l sg_structure hi hp
    exact ⟨i.1, i.2, hs, hb⟩

/-- 标签按给定模型对象编码时，内部解释与原名称求值完全一致。 -/
theorem encode_val_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (U : SG_set.{u} → Prop) :
    Val_d sg_structure (condition_set_l c) U (encode_set_l c G G.root)
      (Forcing.val_l (fun b => U (SG_set.mk (c b))) G) :=
  ⟨coded_graph_l c G, encode_rep_l c G G.root, rfl⟩

/-- 外部条件谓词沿实际编码送到模型对象，不要求该谓词本身是地模型的集合。 -/
def code_pred_l (c : B → WF_graph.{u}) (U : B → Prop) (z : SG_set.{u}) : Prop :=
  ∃ b, z = SG_set.mk (c b) ∧ U b

theorem code_pred_iff_l (c : B → WF_graph.{u})
    (hc : Function.Injective (fun b => SG_set.mk (c b))) (U : B → Prop) (b : B) :
    code_pred_l c U (SG_set.mk (c b)) ↔ U b :=
  ⟨fun ⟨_, h, hd⟩ => hc h ▸ hd, fun hb => ⟨b, rfl, hb⟩⟩

theorem encode_pred_val_l (c : B → WF_graph.{u})
    (hc : Function.Injective (fun b => SG_set.mk (c b))) (G : BV_graph.{u, u} B) (U : B → Prop) :
    Val_d sg_structure (condition_set_l c) (code_pred_l c U) (encode_set_l c G G.root)
      (Forcing.val_l U G) := by
  have h := encode_val_l c G (code_pred_l c U)
  have he : (fun b => code_pred_l c U (SG_set.mk (c b))) = U :=
    funext fun b => propext (code_pred_iff_l c hc U b)
  rwa [he] at h

/-- 小图模型的实际集合构造直接提供内部名称所需的两个模式实例。 -/
theorem sg_name_ops_l : Name_ops_d sg_structure.{u} where
  pair := SG_set.pair
  union := SG_set.union
  separation B T := SG_set.separation T (Supp_d sg_structure B)
  collection B t h := SG_set.collection t (Entry_supp_d sg_structure B) h

theorem sg_setlike_l : Setlike_d.{u+1, u} sg_structure.{u} := SG_set.small_presentation

/-- 可直接调用的内部名称域实例，使用原 SG_set 层级作为扩张的求值载体。 -/
def sg_name_domain_l (B : SG_set.{u}) : Name_domain_l.{u, u+1} SG_set.{u} :=
  name_domain_l sg_structure SG_set.mem_wf sg_setlike_l B
    ⟨SG_set.empty, name_empty_l sg_structure SG_set.pair B SG_set.empty SG_set.not_mem_empty⟩

theorem sg_decode_l {B t : SG_set.{u}} (h : Name_d sg_structure B t) :
    ∃ G : BV_graph.{u, u+1} SG_set.{u}, Rep_d sg_structure B t G :=
  decode_exists_l sg_structure SG_set.mem_wf sg_setlike_l h

end YesMetaZFC.Model.Forcing.Internal
