import YesMetaZFC.Model.SetTheory.Internal.Structure

/-! # 内部隶属结构的解码与外延性

传递集合的成员都仍在载体中，因此其实际隶属结构保持外延性。这是一般内部
模型性质，不依赖力迫或名称定义。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {c X R : M.Domain} (hM : Smdl_d I c X R)
  (hR : ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
local notation "L" => smdl_structure_l I (R := R) (And.left (And.right hM))
include hR

theorem smem_member_l (a b : (L).Domain) : (L).mem a b ↔ M.mem a.val b.val :=
  (hR a.val b.val).trans ⟨And.right ∘ And.right, fun h => ⟨a.property, b.property, h⟩⟩

theorem smem_ext_l (hX : M.TransitiveSet X) (hE : Extensional M) : Extensional L := by
  refine ⟨fun a b h => Subtype.ext (hE.eq_of_same_members a.val b.val (fun x => ?_))⟩
  constructor
  · intro hx
    let y : (L).Domain := ⟨x, hX a.val a.property x hx⟩
    exact (smem_member_l I hM hR y b).mp ((h y).mp ((smem_member_l I hM hR y a).mpr hx))
  · intro hx
    let y : (L).Domain := ⟨x, hX b.val b.property x hx⟩
    exact (smem_member_l I hM hR y a).mp ((h y).mpr ((smem_member_l I hM hR y b).mpr hx))

end YesMetaZFC.SetTheory.Internal
