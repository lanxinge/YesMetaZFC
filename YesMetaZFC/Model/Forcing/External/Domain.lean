import YesMetaZFC.Model.Forcing.External.Extension
import YesMetaZFC.Model.Boolean.Semantics
import YesMetaZFC.Model.FirstOrder.Morphism
import YesMetaZFC.SetTheory.Language

/-! # 相对名称域与原一阶语义

布尔量词明确遍历指定名称域。求值映到同一名称域的实际解释像；它只作为满射
函数解释映射使用，名称的字面相等不代替布尔等号。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean Logic Logic.FirstOrder SetTheory
universe u v
variable {B : Type v}

def domain_str_l (𝔹 : CB_alg B) (N : Name_domain_l.{u, v} B) : BV_str ℒ B where
  Carrier _ := {G : BV_graph.{u, v} B // N.mem G}
  nonempty _ := N.inhabited.elim fun G h => ⟨⟨G, h⟩⟩
  funcInterp f := nomatch f
  eqv G H := BV_graph.bv_eq 𝔹 G.1 H.1
  relv | .membership, .cons G (.cons H .nil) => BV_graph.bv_mem 𝔹 G.1 H.1

/-- 已有集合论扩张的同一个纯一阶载体，不另造名称商。 -/
def ext_model_l (N : Name_domain_l.{u, v} B) (U : B → Prop) : FirstOrder.Structure ℒ where
  Carrier _ := (ext_structure_l N U).Domain
  nonempty _ := (ext_structure_l N U).nonempty
  funcInterp f := nomatch f
  relInterp | .membership, .cons x (.cons y .nil) => (ext_structure_l N U).mem x y

def val_map_l (𝔹 : CB_alg B) (N : Name_domain_l.{u, v} B) (U : B → Prop) :
    Fn_map ((domain_str_l 𝔹 N).top_structure 𝔹.toBA_alg) (ext_model_l N U) where
  map _ G := ⟨val_l U G.1, ext_val_l N U G.2⟩
  function_eq f := nomatch f

theorem val_map_surjective_l (𝔹 : CB_alg B) (N : Name_domain_l.{u, v} B) (U : B → Prop)
    (s : SetSort) : Function.Surjective ((val_map_l 𝔹 N U).map s) := by
  intro x
  obtain ⟨G, hG, e⟩ := x.2
  exact ⟨⟨G, hG⟩, Subtype.ext e⟩

end YesMetaZFC.Model.Forcing
