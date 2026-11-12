import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # 反向包含条件序在成员满扩张中的精确解释 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem image_subset_order_l (hM : M.Models KP) (hN : Extensional N)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {B R : M.Domain}
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) :
    ∀ p q, Entry_d N p q (e R) ↔ N.mem p (e B) ∧ N.mem q (e B) ∧ N.MemberSubset q p := by
  intro p q
  constructor
  · rintro ⟨v,pair,hv⟩
    obtain ⟨v₀,hv₀,rfl⟩ := (full R v).mp hv
    obtain ⟨a,b,code,rfl,rfl⟩ := image_kpair_pull_l hM hN e inj full pair
    obtain ⟨ha,hb,sub⟩ := (order a b).mp ⟨v₀,code,hv₀⟩
    exact ⟨(image_member_l e inj full).mpr ha,(image_member_l e inj full).mpr hb,
      (image_subset_iff_l e inj full).mpr sub⟩
  · rintro ⟨hp,hq,sub⟩
    obtain ⟨a,ha,rfl⟩ := (full B p).mp hp
    obtain ⟨b,hb,rfl⟩ := (full B q).mp hq
    exact (image_entry_iff_l e inj full (KP.exists_pair hM) hN a b R).mp
      ((order a b).mpr ⟨ha,hb,(image_subset_iff_l e inj full).mp sub⟩)

end YesMetaZFC.Model.Forcing.Internal
