import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.Ord.Code.Pair
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.SetTheory.Ord.Code.Prefix
import YesMetaZFC.SetTheory.Ord.Code.Sequence

/-! # 典范序数对次序在传递子源中的解释

最大坐标必为原来的某个坐标，故无需额外的最大值闭包。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hE : Extensional M)
  (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
local notation "N" => rt_model_l Z nz
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hZ nz hE pair

theorem rt_ordinal_max_l (a b m : (N).Domain) :
    (N).IsOrdinalMaximum a b m ↔ M.IsOrdinalMaximum a.val b.val m.val := by
  have eq (x y : (N).Domain) : x = y ↔ x.val = y.val := ⟨congrArg Subtype.val, Subtype.ext⟩
  exact or_congr (and_congr (eq m a) (or_congr (eq b a) Iff.rfl)) (and_congr (eq m b) Iff.rfl)

theorem rt_oc_less_l (p q : (N).Domain) :
    (N).CanonicalOrdinalPairLess J p q ↔ M.CanonicalOrdinalPairLess I p.val q.val := by
  have code := rt_kpair_l hE hP hZ nz pair
  have mx := rt_ordinal_max_l nz
  have cmp (a b c d m n : (N).Domain) :
      ((N).mem m n ∨ (m = n ∧ ((N).mem a c ∨ (a = c ∧ (N).mem b d)))) ↔
        (M.mem m.val n.val ∨ (m.val = n.val ∧
          (M.mem a.val c.val ∨ (a.val = c.val ∧ M.mem b.val d.val)))) := by
    have eq (x y : (N).Domain) : x = y ↔ x.val = y.val := ⟨congrArg Subtype.val, Subtype.ext⟩
    exact or_congr Iff.rfl (and_congr (eq m n) (or_congr Iff.rfl (and_congr (eq a c) Iff.rfl)))
  constructor
  · rintro ⟨a, b, c, d, m, n, hp, hq, hm, hn, h⟩
    exact ⟨a.val, b.val, c.val, d.val, m.val, n.val,
      (code ..).mp hp, (code ..).mp hq, (mx ..).mp hm, (mx ..).mp hn, (cmp ..).mp h⟩
  · rintro ⟨a, b, c, d, m, n, hp, hq, hm, hn, h⟩
    have ab := hp.mem_l M hZ p.property
    have cd := hq.mem_l M hZ q.property
    have hmZ := hm.elim (fun e => e.1.symm ▸ ab.1) (fun e => e.1.symm ▸ ab.2)
    have hnZ := hn.elim (fun e => e.1.symm ▸ cd.1) (fun e => e.1.symm ▸ cd.2)
    exact ⟨⟨a, ab.1⟩, ⟨b, ab.2⟩, ⟨c, cd.1⟩, ⟨d, cd.2⟩, ⟨m, hmZ⟩, ⟨n, hnZ⟩,
      (code ..).mpr hp, (code ..).mpr hq, (mx ..).mpr hm, (mx ..).mpr hn, (cmp ..).mpr h⟩

theorem rt_oc_order_l (R A a : (N).Domain) :
    (N).IsCanonicalOrdinalPairOrder J R A a ↔
      M.IsCanonicalOrdinalPairOrder I R.val A.val a.val := by
  have entry := rt_entry_l hZ nz hE
  refine and_congr (rt_cartesian_l hE hP hZ nz pair A a a)
    (and_congr (rt_relation_on_l hE hP hZ nz pair R A) ?_)
  constructor
  · intro h p q
    constructor
    · intro hpq
      have pq := rd_entry_transitive_l hZ R.property hpq
      obtain ⟨hp, hq, lt⟩ := (h ⟨p, pq.1⟩ ⟨q, pq.2⟩).mp ((entry ..).mpr hpq)
      exact ⟨hp, hq, (rt_oc_less_l hE hP hZ nz pair ..).mp lt⟩
    · rintro ⟨hp, hq, lt⟩
      exact (entry ..).mp ((h ⟨p, hZ A.val A.property p hp⟩ ⟨q, hZ A.val A.property q hq⟩).mpr
        ⟨hp, hq, (rt_oc_less_l hE hP hZ nz pair ..).mpr lt⟩)
  · intro h p q
    exact (entry p q R).trans ((h p.val q.val).trans
      (and_congr_right fun _ => and_congr_right fun _ => (rt_oc_less_l hE hP hZ nz pair p q).symm))

end YesMetaZFC.SetTheory.Internal

/-! ## 典范序数配对在极限秩层中的绝对性

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
local notation "T" => v_transitive_l I hV
local notation "P" => sc_v_pair_l (ZF.modelsKP hZF) hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P

theorem rt_oc_at_down_l (a p c : (N).Domain) (h : Oc_at_d I a.val p.val c.val) :
    Oc_at_d J a p c := by
  obtain ⟨ha, X, R, hr, hp, D, F, pred, collapse, range⟩ := h
  have hx := ZF.v_product_mem_l I hZF hV hδ a.property a.property hr.1
  have hR := v_relation_mem_l I hV hδ hx (fun q hq => by
    obtain ⟨x, y, code⟩ := hr.2.1.1 q hq
    have xy := hr.2.1.2 x y ⟨q, code, hq⟩
    exact ⟨x, xy.1, y, xy.2, code⟩)
  have hD := v_subset_mem_l I hV hx (fun x hx => ((pred x).mp hx).1)
  obtain ⟨B, hB, hdB, hcB⟩ := v_joint_bound_l I hV hD c.property
  have hF := v_relation_mem_l I hV hδ hB (fun q hq => by
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

/-! ## 序数折叠的读取与递归步在极限秩层中绝对

读取见证的长度就是已有历史图的定义域，故可在同一秩层内恢复。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {δ Z : M.Domain}
  (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z)
  (nz : Nonempty {x // M.mem x Z})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => v_transitive_l I hV
local notation "P" => sc_v_pair_l (ZF.modelsKP hZF) hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P

theorem rt_oc_read_l (F H b a : (N).Domain) :
    Oc_read_d J F H b a ↔ Oc_read_d I F.val H.val b.val a.val := by
  have ent := rt_entry_l T nz hZF.1
  have dom := rt_domain_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  have ord := rt_ordinal_iff_l T nz (ZF.modelsKP hZF)
  constructor
  · rintro ⟨n, i, hn, hs, hi, hb, ha, ob, oa⟩
    exact ⟨n.val, i.val, (dom ..).mp hn, (rt_successor_l T nz hZF.1 ..).mp hs,
      (ord ..).mp hi, (ent ..).mp hb, (ent ..).mp ha, (ord ..).mp ob, (ord ..).mp oa⟩
  · rintro ⟨n, i, hn, hs, hi, hb, ha, ob, oa⟩
    let n' : (N).Domain := ⟨n, ZF.v_domain_mem_l I hZF hV H.property hn⟩
    let i' : (N).Domain := ⟨i, T n n'.property i hs.predecessor_mem⟩
    exact ⟨n', i', (dom ..).mpr hn, (rt_successor_l T nz hZF.1 ..).mpr hs,
      (ord ..).mpr hi, (ent ..).mpr hb, (ent ..).mpr ha, (ord ..).mpr ob, (ord ..).mpr oa⟩

theorem rt_oc_step_l (F H c : (N).Domain) :
    Oc_step_d J F H c ↔ Oc_step_d I F.val H.val c.val := by
  have read := rt_oc_read_l hZF hδ hV nz
  have own {b a} (h : Oc_read_d I F.val H.val b a) : M.mem b Z ∧ M.mem a Z := by
    obtain ⟨n, i, _, _, _, hb, ha, _⟩ := h
    exact ⟨(rd_entry_transitive_l T H.property hb).2, (rd_entry_transitive_l T F.property ha).2⟩
  have ex : (∃ b a, Oc_read_d J F H b a) ↔ ∃ b a, Oc_read_d I F.val H.val b a := by
    constructor
    · rintro ⟨b, a, h⟩
      exact ⟨b.val, a.val, (read ..).mp h⟩
    · rintro ⟨b, a, h⟩
      exact ⟨⟨b, (own h).1⟩, ⟨a, (own h).2⟩, (read ..).mpr h⟩
  refine or_congr ?_ (and_congr (not_congr ex)
    ⟨fun h x hx => h ⟨x, T c.val c.property x hx⟩ hx, fun h x => h x.val⟩)
  constructor
  · rintro ⟨b, a, hr, hp⟩
    exact ⟨b.val, a.val, (read ..).mp hr, (rt_oc_pair_l hZF hδ hV nz ..).mp hp⟩
  · rintro ⟨b, a, hr, hp⟩
    exact ⟨⟨b, (own hr).1⟩, ⟨a, (own hr).2⟩,
      (read ..).mpr hr, (rt_oc_pair_l hZF hδ hV nz ..).mpr hp⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部有限序列编码在极限秩层中的绝对性

递归历史的每个值都是较短前缀的实际编码。自然数前缀的整张历史因此是
ω 上的关系，而不是外部逐项选择出的列；非标准有限长度同样适用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {δ Z : M.Domain}
  (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z)
  (nz : Nonempty {x // M.mem x Z})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => v_transitive_l I hV
local notation "P" => sc_v_pair_l (ZF.modelsKP hZF) hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P

theorem rt_oc_recursion_l (F H n : (N).Domain) :
    (N).IsRecursiveSequence J (Oc_step_d J F) H n ↔
      M.IsRecursiveSequence I (Oc_step_d I F.val) H.val n.val := by
  have ent := rt_entry_l T nz hZF.1
  have cut := rt_restriction_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  refine and_congr (rt_sequence_l (ZF.modelsKP hZF) T nz P H n) ?_
  constructor
  · intro h i hi y hiy
    have iy := rd_entry_transitive_l T H.property hiy
    obtain ⟨K, hk, hs⟩ := h ⟨i, iy.1⟩ hi ⟨y, iy.2⟩ ((ent ..).mpr hiy)
    exact ⟨K.val, (cut ..).mp hk, (rt_oc_step_l hZF hδ hV nz ..).mp hs⟩
  · intro h i hi y hiy
    obtain ⟨K, hk, hs⟩ := h i.val hi y.val ((ent ..).mp hiy)
    let K' : (N).Domain := ⟨K, ZF.v_restriction_mem_l I hZF hV H.property hk⟩
    exact ⟨K', (cut ..).mpr hk, (rt_oc_step_l hZF hδ hV nz ..).mpr hs⟩

theorem rt_oc_fold_up_l (F n c : (N).Domain) (h : Oc_fold_d J F n c) :
    Oc_fold_d I F.val n.val c.val := by
  obtain ⟨H, hh, hc⟩ := h
  exact ⟨H.val, (rt_oc_recursion_l hZF hδ hV nz ..).mp hh,
    (rt_oc_step_l hZF hδ hV nz ..).mp hc⟩

theorem rt_oc_fold_down_l (ω F n c : (N).Domain) (hω : M.IsOmega ω.val)
    (hn : M.mem n.val ω.val) (hf : Oc_prefix_d I n.val F.val)
    (hv : ∀ i, M.mem i n.val → ∀ a, M.PairMember I i a F.val → M.mem a ω.val)
    (h : Oc_fold_d I F.val n.val c.val) : Oc_fold_d J F n c := by
  obtain ⟨H, hh, hc⟩ := h
  have hHZ := v_relation_mem_l I hV hδ ω.property (fun p hp => by
    obtain ⟨i, a, code⟩ := hh.1.2.1.1 p hp
    have hia : M.PairMember I i a H := ⟨p, code, hp⟩
    have hi := (hh.1.2.2 i).mpr ⟨a, hia⟩
    have sub := hh.1.1.transitive i hi
    exact ⟨i, hω.transitive (ZF.modelsKP hZF) n.val hn i hi, a,
      oc_fold_natural_l I hZF hω i (hω.transitive (ZF.modelsKP hZF) n.val hn i hi) F.val a
        (hf.mono_l I sub) (fun j hj => hv j (sub j hj)) (hh.recursionValue_of_pairMember hi hia), code⟩)
  let H' : (N).Domain := ⟨H, hHZ⟩
  exact ⟨H', (rt_oc_recursion_l hZF hδ hV nz F H' n).mpr hh,
    (rt_oc_step_l hZF hδ hV nz F H' c).mpr hc⟩

/-- 自然数值图的规范序列码可以在源中原样解码。 -/
theorem rt_oc_seq_l (ω F c : (N).Domain) (hω : M.IsOmega ω.val)
    (hv : ∀ i a, M.PairMember I i a F.val → M.mem a ω.val) :
    Oc_seq_d J ω F c ↔ Oc_seq_d I ω.val F.val c.val := by
  constructor
  · rintro ⟨n, b, hn, hf, hb, hc⟩
    exact ⟨n.val, b.val, hn, (rt_ordinal_sequence_l (ZF.modelsKP hZF) T nz P ..).mp hf,
      rt_oc_fold_up_l hZF hδ hV nz F n b hb, (rt_oc_pair_l hZF hδ hV nz ..).mp hc⟩
  · rintro ⟨n, b, hn, hf, hb, hc⟩
    have pre := oc_seq_prefix_l I hf
    have nb := oc_fold_natural_l I hZF hω n hn F.val b pre (fun i _ => hv i) hb
    let n' : (N).Domain := ⟨n, T ω.val ω.property n hn⟩
    let b' : (N).Domain := ⟨b, T ω.val ω.property b nb⟩
    exact ⟨n', b', hn, (rt_ordinal_sequence_l (ZF.modelsKP hZF) T nz P F n').mpr hf,
      rt_oc_fold_down_l hZF hδ hV nz ω F n' b' hω hn pre (fun i _ => hv i) hb,
      (rt_oc_pair_l hZF hδ hV nz n' b' c).mpr hc⟩

end YesMetaZFC.SetTheory.Internal
