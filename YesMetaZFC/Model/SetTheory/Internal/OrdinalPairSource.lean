import YesMetaZFC.Model.SetTheory.Internal.OrdinalPairOrderSource
import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 典范序数配对在极限秩层中的绝对性

向下解释时，把方块截到源内足够大的序数。方块、次序、前驱集和坍缩图
依次由实际秩闭包回收；不要求该秩层满足 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem rt_oc_at_up_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z})
    (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
    (a p c : (rt_model_l Z nz).Domain)
    (h : Oc_at_d (rt_pair_l hZ nz hKP.1 pair) a p c) :
    Oc_at_d (kp_pair_l hKP) a.val p.val c.val := by
  obtain ⟨ha, X, R, hr, hp, P, F, pred, collapse, range⟩ := h
  exact ⟨(rt_ordinal_iff_l hZ nz hKP a).mp ha, X.val, R.val,
    (rt_oc_order_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mp hr, hp,
    P.val, F.val, (rt_predecessor_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mp pred,
    (rt_order_collapse_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mp collapse,
    (rt_range_l hZ nz hKP.1 (KP.exists_pair hKP) pair ..).mp range⟩

variable (hZF : M.Models ZF) {δ Z : M.Domain} (hδ : M.IsLimitOrdinal δ)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (nz : Nonempty {x // M.mem x Z})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => ZF.v_transitive_l I hZF hV
local notation "P" => sc_v_pair_l hZF hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P

theorem rt_oc_at_down_l (a p c : (N).Domain) (h : Oc_at_d I a.val p.val c.val) :
    Oc_at_d J a p c := by
  obtain ⟨ha, X, R, hr, hp, D, F, pred, collapse, range⟩ := h
  have hx := ZF.v_product_mem_l I hZF hV hδ a.property a.property hr.1
  have hR := ZF.v_relation_mem_l I hZF hV hδ hx (fun q hq => by
    obtain ⟨x, y, code⟩ := hr.2.1.1 q hq
    have xy := hr.2.1.2 x y ⟨q, code, hq⟩
    exact ⟨x, xy.1, y, xy.2, code⟩)
  have hD := ZF.v_subset_mem_l I hZF hV hx (fun x hx => ((pred x).mp hx).1)
  obtain ⟨B, hB, hdB, hcB⟩ := ZF.v_joint_bound_l I hZF hV hD c.property
  have hF := ZF.v_relation_mem_l I hZF hV hδ hB (fun q hq => by
    obtain ⟨x, y, code⟩ := collapse.1.1 q hq
    have entry : M.PairMember I x y F := ⟨q, code, hq⟩
    exact ⟨x, hdB x ((collapse.2.1 x).mpr ⟨y, entry⟩),
      y, hcB y ((range y).mpr ⟨x, entry⟩), code⟩)
  let X' : (N).Domain := ⟨X, hx⟩
  let R' : (N).Domain := ⟨R, hR⟩
  let D' : (N).Domain := ⟨D, hD⟩
  let F' : (N).Domain := ⟨F, hF⟩
  exact ⟨rt_ordinal_l T nz a ha, X', R',
    (rt_oc_order_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P R' X' a).mpr hr, hp,
    D', F', (rt_predecessor_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P D' R' X' p).mpr pred,
    (rt_order_collapse_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P F' R' X' D').mpr collapse,
    (rt_range_l T nz hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) P c F').mpr range⟩

/-- 输入与输出已在极限秩层中时，典范序数配对的内外计算完全相同。 -/
theorem rt_oc_pair_l (a b c : (N).Domain) : Oc_pair_d J a b c ↔ Oc_pair_d I a.val b.val c.val := by
  constructor
  · rintro ⟨t, p, code, hc⟩
    exact ⟨t.val, p.val, (rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P ..).mp code,
      rt_oc_at_up_l (ZF.modelsKP hZF) T nz P t p c hc⟩
  · intro h
    have types := oc_pair_types_l I hZF h
    have ha := ZF.v_ordinal_height_l hZF hV types.1 a.property
    have hb := ZF.v_ordinal_height_l hZF hV types.2.1 b.property
    have bound : ∃ t, M.mem t δ ∧ M.mem a.val t ∧ M.mem b.val t := by
      have upper {x y} (hy : M.mem y δ) (hxy : x = y ∨ M.mem x y) :
          ∃ t, M.mem t δ ∧ M.mem x t ∧ M.mem y t := by
        obtain ⟨t, ht, hyt⟩ := hδ.2.2 y hy
        exact ⟨t, ht, hxy.elim (fun e => e.symm ▸ hyt)
          (fun h => (hδ.1.mem ht).transitive y hyt x h), hyt⟩
      rcases hδ.1.wellOrder.linear.compare a.val ha b.val hb with eq | lt | gt
      · exact upper hb (Or.inl (hZF.1.eq_of_same_members _ _ eq))
      · exact upper hb (Or.inr lt)
      · obtain ⟨t, ht, hb, ha⟩ := upper ha (Or.inr gt)
        exact ⟨t, ht, ha, hb⟩
    obtain ⟨t, ht, hat, hbt⟩ := bound
    obtain ⟨s, p, code, hc⟩ := h
    obtain ⟨X, hx⟩ := ZF.exists_cartesianProduct hZF I t t
    obtain ⟨R, hr, _⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I (hδ.1.mem ht) hx
    have hp := (hx p).mpr ⟨a.val, hat, b.val, hbt, code⟩
    have htZ := ZF.v_ordinal_mem_l I hZF hV ht
    have hpZ := T X (ZF.v_product_mem_l I hZF hV hδ htZ htZ hx) p hp
    let t' : (N).Domain := ⟨t, htZ⟩
    let p' : (N).Domain := ⟨p, hpZ⟩
    exact ⟨t', p', (rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P p' a b).mpr code,
      rt_oc_at_down_l hZF hδ hV nz t' p' c
        ⟨hδ.1.mem ht, X, R, hr, hp, oc_at_value_l I hZF (hδ.1.mem ht) hr hp hc⟩⟩

end YesMetaZFC.SetTheory.Internal
