import YesMetaZFC.Model.SetTheory.Internal.TransitiveOrderCollapse
import YesMetaZFC.SetTheory.Ord.Code.Pair

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
