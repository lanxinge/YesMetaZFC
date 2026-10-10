import YesMetaZFC.Model.SetTheory.Internal.TransitiveRecursion
import YesMetaZFC.SetTheory.Ord.OrderType

/-! # 传递子源中良序坍缩方程的绝对性

坍缩图已经在源内时，其前驱集与每个值的全部成员均可回收。
因此这里不需要源的替代公理，也不以外部良基性代替内部方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hE : Extensional M)
  (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
include hZ
local notation "N" => rt_model_l Z nz
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hZ nz hE pair

theorem rt_predecessor_l (P R A p : (N).Domain) :
    (N).IsPredecessorSet J P R A p ↔ M.IsPredecessorSet I P.val R.val A.val p.val := by
  have entry := rt_entry_l hZ nz hE
  constructor
  · intro h x
    constructor
    · intro hx
      obtain ⟨ha, hr⟩ := (h ⟨x, hZ P.val P.property x hx⟩).mp hx
      exact ⟨ha, (entry ..).mp hr⟩
    · rintro ⟨ha, hr⟩
      exact (h ⟨x, hZ A.val A.property x ha⟩).mpr ⟨ha, (entry ..).mpr hr⟩
  · intro h x
    exact (h x.val).trans (and_congr_right fun _ => (entry x p R).symm)

theorem rt_initial_segment_l (P R A : (N).Domain) :
    (N).IsRelationInitialSegment J P R A ↔ M.IsRelationInitialSegment I P.val R.val A.val := by
  refine and_congr (rt_member_subset_l hZ nz P A) ?_
  constructor
  · intro h x hx y hy hyx
    exact h ⟨x, hZ P.val P.property x hx⟩ hx ⟨y, hZ A.val A.property y hy⟩ hy
      ((rt_entry_l hZ nz hE ..).mpr hyx)
  · intro h x hx y hy hyx
    exact h x.val hx y.val hy ((rt_entry_l hZ nz hE ..).mp hyx)

theorem rt_order_collapse_l (F R A P : (N).Domain) :
    (N).IsWellOrderCollapseFunction J F R A P ↔
      M.IsWellOrderCollapseFunction I F.val R.val A.val P.val := by
  have entry := rt_entry_l hZ nz hE
  refine and_congr (rt_function_l hZ nz hE hP pair F)
    (and_congr (rt_domain_l hE hP hZ nz pair P F)
      (and_congr (rt_initial_segment_l hE hP hZ nz pair P R A) ?_))
  constructor
  · intro h x hx y hxy z
    have xy := rd_entry_transitive_l hZ F.property hxy
    have values := h ⟨x, hZ P.val P.property x hx⟩ hx ⟨y, xy.2⟩ ((entry ..).mpr hxy)
    constructor
    · intro hz
      obtain ⟨a, ha, hax, haz⟩ := (values ⟨z, hZ y xy.2 z hz⟩).mp hz
      exact ⟨a.val, ha, (entry ..).mp hax, (entry ..).mp haz⟩
    · rintro ⟨a, ha, hax, haz⟩
      exact (values ⟨z, (rd_entry_transitive_l hZ F.property haz).2⟩).mpr
        ⟨⟨a, hZ P.val P.property a ha⟩, ha, (entry ..).mpr hax, (entry ..).mpr haz⟩
  · intro h x hx y hxy z
    constructor
    · intro hz
      obtain ⟨a, ha, hax, haz⟩ := (h x.val hx y.val ((entry ..).mp hxy) z.val).mp hz
      exact ⟨⟨a, hZ P.val P.property a ha⟩, ha, (entry ..).mpr hax, (entry ..).mpr haz⟩
    · rintro ⟨a, ha, hax, haz⟩
      exact (h x.val hx y.val ((entry ..).mp hxy) z.val).mpr
        ⟨a.val, ha, (entry ..).mp hax, (entry ..).mp haz⟩

end YesMetaZFC.SetTheory.Internal
