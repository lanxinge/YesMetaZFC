import YesMetaZFC.Model.SetTheory.Internal.RelationSubset

/-! # 原关系共同低层的相对幂集识别

回收目标中的任意新子集，再用所属源的真实相对幂集判断成员关系。
这同时控制低层幂集递归的两个方向，不局限于旧对象的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smap_d.power_raw_l (hZF : M.Models ZF) {ω c X R c' Y S q B H Γ k N D P : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q) (hBH : M.PairMember I B H q)
    (closed : ∀ a b, M.mem a B → M.mem b X → M.MemberSubset b a → M.mem b B)
    (hΓ : M.TransitiveSet Γ) (inside : M.MemberSubset Γ N) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ a, M.PairMember I a H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x a k)
    (pred : ∀ x a, M.PairMember I x a k → ∀ b,
      M.PairMember I b a S ↔ ∃ y, M.mem y x ∧ M.PairMember I y b k)
    (d p : (smdl_structure_l I (R := S) model.2.1).Domain)
    (hDd : M.PairMember I D d.val k) (hPp : M.PairMember I P p.val k) (power : Source_d N D P) :
    (smdl_structure_l I (R := S) model.2.1).IsPowerSetOf p d := by
  intro z
  constructor
  · intro hz x hx
    obtain ⟨A, hA, hAz⟩ := (pred P p.val hPp z.val).mp hz
    obtain ⟨s, hs, hsx⟩ := (pred A z.val hAz x.val).mp hx
    exact (pred D d.val hDd x.val).mpr ⟨s, ((power A).mp hA).2 s hs, hsx⟩
  · intro sub
    obtain ⟨A, hA, hAz, subA⟩ := hq.capture_raw_l I hZF hω hX hm model hBH closed hΓ fk image pred hDd z.property
      (fun x hx => sub ⟨x, hx⟩)
    exact (pred P p.val hPp z.val).mpr ⟨A, (power A).mpr ⟨inside A hA, subA⟩, hAz⟩

end YesMetaZFC.SetTheory.Internal
