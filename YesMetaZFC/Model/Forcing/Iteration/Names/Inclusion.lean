import YesMetaZFC.Model.Forcing.Iteration.Stage.Embedding
import YesMetaZFC.Model.Forcing.Stage.Atomic.Basic

/-! # 实际阶段包含下不改写名称

坐标阶段的嵌入是全部旧条件上的恒等图，故其递归名称搬运逐对象等于原名称。
前段名称可直接作为后段名称；等号和成员力迫在旧条件上保持并反射。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}}

/-- 阶段包含只扩大可用标签，已有闭名称无需选择新的表示。 -/
theorem row_name_l {I : kpair_convention_l.Interpretation M} {α B R D V t}
    (h : Row_link_d I α B R D V) (ht : Name_d M B t) : Name_d M D t := by
  obtain ⟨S, ht, hS⟩ := ht
  exact ⟨S, ht, fun x hx v hv => (hS x hx v hv).elim fun a hh =>
    hh.elim fun b hh => ⟨a, b, hh.1, hh.2.1, h.mem b hh.2.2⟩⟩

theorem row_eq_force_l (hZF : M.Models ZF) {α B R D V p s t}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (h : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hp : M.mem p B)
    (hs : Name_d M B s) (ht : Name_d M B t) :
    Eq_force_d M B R B p s t ↔ Eq_force_d M D V D p s t := by
  obtain ⟨F, hF, he⟩ := row_link_embed_l hZF h
  exact nmap_eq_l O L hZF he hs ht (nmap_identity_l hZF hF hs) (nmap_identity_l hZF hF ht)
    ((hF p p).mpr ⟨hp, rfl⟩)

theorem row_mem_force_l (hZF : M.Models ZF) {α B R D V p s t}
    (O : Cond_order_d M B R B) (L : Cond_order_d M D V D)
    (h : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hp : M.mem p B)
    (hs : Name_d M B s) (ht : Name_d M B t) :
    Mem_force_d M B R B p s t ↔ Mem_force_d M D V D p s t := by
  obtain ⟨F, hF, he⟩ := row_link_embed_l hZF h
  exact nmap_mem_force_l O L hZF he hs ht (nmap_identity_l hZF hF hs) (nmap_identity_l hZF hF ht)
    ((hF p p).mpr ⟨hp, rfl⟩)

end YesMetaZFC.Model.Forcing.Internal
