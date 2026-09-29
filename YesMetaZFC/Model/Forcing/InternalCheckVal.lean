import YesMetaZFC.Model.Forcing.InternalGround
import YesMetaZFC.Model.Forcing.InternalCheck

/-! # 规范名称解释还原地模型对象

将规范名称递归图直接作为名称图与地模型成员图之间的双模拟。只需标签 b
被接受，不需要超滤子、完备性或泛型性；取布尔顶值即得到通常的 check 定理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SmallGraph Boolean
universe u v
variable (M : SetTheory.Structure.{u})

theorem check_val_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) {B b x t : M.Domain}
    {G : WF_graph.{v}} {H : BV_graph.{v, u} M.Domain}
    (hx : Ground_rep_d M x G) (ht : Check_d M b x t) (hH : Rep_d M B t H)
    {U : M.Domain → Prop} (hb : U b) : Forcing.val_l U H = SG_set.mk G := by
  obtain ⟨c, hc, hf, hk⟩ := hx
  obtain ⟨_, d, hd, hh, hj⟩ := hH
  apply SG_set.mk_eq.mpr
  refine ⟨fun a z => Check_d M b (c z) (d a), ?_, by
    change Check_d M b (c G.root) (d H.root)
    rw [hc, hd]; exact ht⟩
  intro a z haz
  constructor
  · rintro a' ⟨ha, _⟩
    obtain ⟨_, y, hy, hs⟩ := (check_entry_l M hE hI hP haz _ _).mp (hh a' a ha)
    obtain ⟨z', hz, he⟩ := hk z y hy
    exact ⟨z', hz, show Check_d M b (c z') (d a') from he.symm ▸ hs⟩
  · intro z' hz
    obtain ⟨s, hs⟩ := check_child_l M haz (hf z' z hz)
    have he := (check_entry_l M hE hI hP haz s b).mpr ⟨rfl, c z', hf z' z hz, hs⟩
    obtain ⟨a', ha, had, hav⟩ := hj a s b he
    exact ⟨a', ⟨ha, hav.symm ▸ hb⟩, show Check_d M b (c z') (d a') from had.symm ▸ hs⟩

/-- 同一内部规范名称对所有接受 b 的条件谓词都还原同一个地模型对象。 -/
theorem check_val_exists_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hR : ∀ F, ∃ S, ∀ t, M.mem t S ↔ ∃ x, Entry_d M x t F)
    (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    {B b x t : M.Domain} (hb : M.mem b B) (ht : Check_d M b x t)
    {y : SG_set.{v}} (hy : Ground_d M x y) :
    ∀ U : M.Domain → Prop, U b → Val_d M B U t y := by
  obtain ⟨G, hG, rfl⟩ := hy
  obtain ⟨H, hH⟩ := decode_exists_l M hM hL (check_name_l M hR hb ht)
  exact fun U hU => ⟨H, hH, check_val_l M hE hI hP hG ht hH hU⟩

end YesMetaZFC.Model.Forcing.Internal
