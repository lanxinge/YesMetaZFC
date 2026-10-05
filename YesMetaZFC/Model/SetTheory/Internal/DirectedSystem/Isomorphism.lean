import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Limit

/-! # 直接极限沿实际同构传递

同构后的规范投影仍有完全相同的核与代表关系，故保持同一个定向系统
的直接极限证书。这里只消费实际函数图、双射和关系等价，不用选择公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem di_limit_iso_l {A p T R q C S Y V e r : M.Domain} (limit : Di_limit_d A p T R q C S)
    (he : M.IsSetBijectionFromTo I e C Y) (hr : Fn0_d A Y r)
    (rs : ∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ x, Rd_entry_d a x q ∧ Rd_entry_d x y e)
    (rel : M.IsSetRelationOn I V Y)
    (atom : ∀ x y u v, Rd_entry_d x u e → Rd_entry_d y v e → (Rd_entry_d x y S ↔ Rd_entry_d u v V)) :
    Di_limit_d A p T R r Y V := by
  refine ⟨hr, fun y => ⟨?_, fun ⟨a, ha⟩ => (hr.bound_l ha).2⟩, ?_, ?_, rel.2, rel.1⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := he.2 y hy
    obtain ⟨a, hax⟩ := (limit.range x).mp hx
    exact ⟨a, (rs a y).mpr ⟨(limit.projection.bound_l hax).1, x, hax, hxy⟩⟩
  · intro a b u v hau hbv
    obtain ⟨_, x, hax, hxu⟩ := (rs a u).mp hau
    obtain ⟨_, y, hby, hyv⟩ := (rs b v).mp hbv
    exact (⟨fun eq => he.1.2 x y v (eq ▸ hxu) hyv,
      fun eq => he.1.1.1.2 y u v (eq ▸ hxu) hyv⟩ : u = v ↔ x = y).trans (limit.kernel a b x y hax hby)
  · intro a b u v hau hbv
    obtain ⟨_, x, hax, hxu⟩ := (rs a u).mp hau
    obtain ⟨_, y, hby, hyv⟩ := (rs b v).mp hbv
    exact (atom x y u v hxu hyv).symm.trans (limit.relation a b x y hax hby)

end YesMetaZFC.SetTheory.Internal
