import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure

/-! # 传递子源中的笛卡尔积与递归图

只用外延性和实际配对闭包；所有量词的见证由已有集合的传递性回收。
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

theorem rt_member_subset_l (A B : (N).Domain) :
    (N).MemberSubset A B ↔ M.MemberSubset A.val B.val :=
  ⟨fun h x hx => h ⟨x, hZ A.val A.property x hx⟩ hx, fun h x hx => h x.val hx⟩

theorem rt_domain_l (A F : (N).Domain) :
    (N).IsDomainOf J A F ↔ M.IsDomainOf I A.val F.val := by
  have entry := rt_entry_l hZ nz hE
  constructor
  · intro h x
    constructor
    · intro hx
      obtain ⟨y, hxy⟩ := (h ⟨x, hZ A.val A.property x hx⟩).mp hx
      exact ⟨y.val, (entry ..).mp hxy⟩
    · rintro ⟨y, hxy⟩
      have xy := rd_entry_transitive_l hZ F.property hxy
      exact (h ⟨x, xy.1⟩).mpr ⟨⟨y, xy.2⟩, (entry ..).mpr hxy⟩
  · intro h x
    exact (h x.val).trans ⟨fun ⟨y, hxy⟩ =>
      ⟨⟨y, (rd_entry_transitive_l hZ F.property hxy).2⟩, (entry ..).mpr hxy⟩,
      fun ⟨y, hxy⟩ => ⟨y.val, (entry ..).mp hxy⟩⟩

theorem rt_restriction_l (P F A : (N).Domain) :
    (N).IsRestrictionOf J P F A ↔ M.IsRestrictionOf I P.val F.val A.val := by
  have entry := rt_entry_l hZ nz hE
  constructor
  · rintro ⟨rel, cut⟩
    refine ⟨(rt_relation_l hE hP hZ nz pair P).mp rel, fun x y => ⟨?_, ?_⟩⟩
    · intro hxy
      have xy := rd_entry_transitive_l hZ P.property hxy
      obtain ⟨hx, he⟩ := (cut ⟨x, xy.1⟩ ⟨y, xy.2⟩).mp ((entry ..).mpr hxy)
      exact ⟨hx, (entry ..).mp he⟩
    · rintro ⟨hx, hxy⟩
      have xy := rd_entry_transitive_l hZ F.property hxy
      exact (entry ..).mp ((cut ⟨x, xy.1⟩ ⟨y, xy.2⟩).mpr ⟨hx, (entry ..).mpr hxy⟩)
  · rintro ⟨rel, cut⟩
    exact ⟨(rt_relation_l hE hP hZ nz pair P).mpr rel, fun x y =>
      (entry x y P).trans ((cut x.val y.val).trans (and_congr_right fun _ => (entry x y F).symm))⟩

theorem rt_cartesian_l (P A B : (N).Domain) :
    (N).IsCartesianProduct J P A B ↔ M.IsCartesianProduct I P.val A.val B.val := by
  have code := rt_kpair_l hE hP hZ nz pair
  constructor
  · intro h p
    constructor
    · intro hp
      obtain ⟨a, ha, b, hb, hp⟩ := (h ⟨p, hZ P.val P.property p hp⟩).mp hp
      exact ⟨a.val, ha, b.val, hb, (code ..).mp hp⟩
    · rintro ⟨a, ha, b, hb, hp⟩
      let a' : (N).Domain := ⟨a, hZ A.val A.property a ha⟩
      let b' : (N).Domain := ⟨b, hZ B.val B.property b hb⟩
      obtain ⟨q, hq⟩ := (J).total a' b'
      have eq := (I).unique hp ((code ..).mp hq)
      exact eq ▸ (h q).mpr ⟨a', ha, b', hb, hq⟩
  · intro h p
    constructor
    · intro hp
      obtain ⟨a, ha, b, hb, hp⟩ := (h p.val).mp hp
      exact ⟨⟨a, hZ A.val A.property a ha⟩, ha, ⟨b, hZ B.val B.property b hb⟩, hb, (code ..).mpr hp⟩
    · rintro ⟨a, ha, b, hb, hp⟩
      exact (h p.val).mpr ⟨a.val, ha, b.val, hb, (code ..).mp hp⟩

theorem rt_relation_on_l (R A : (N).Domain) :
    (N).IsSetRelationOn J R A ↔ M.IsSetRelationOn I R.val A.val := by
  refine and_congr (rt_relation_l hE hP hZ nz pair R) ?_
  constructor
  · intro h x y hxy
    have xy := rd_entry_transitive_l hZ R.property hxy
    exact h ⟨x, xy.1⟩ ⟨y, xy.2⟩ ((rt_entry_l hZ nz hE ..).mpr hxy)
  · intro h x y hxy
    exact h x.val y.val ((rt_entry_l hZ nz hE ..).mp hxy)

end YesMetaZFC.SetTheory.Internal
