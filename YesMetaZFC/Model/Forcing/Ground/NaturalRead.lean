import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.SetTheory.Images.NaturalBasisImage

/-! # 规范自然数图的完整读取恢复背景中的同一基底

常零输出来自地模型的实际空集，后继关系由成员满嵌入双向保持。
两张读取图的全函数性把自然数坐标上的值方程恢复为完整规范基底。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v w
variable {N : Structure.{u}} {M : Structure.{v}} {E : Structure.{w}}

theorem natural_basis_read_l (hN : N.Models KP) (hM : Extensional M) (hE : Extensional E)
    (k : N.Domain → M.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    (j : N.Domain → E.Domain) (ji : Function.Injective j)
    (jf : ∀ a y, E.mem y (j a) ↔ ∃ b, N.mem b a ∧ j b = y)
    {ω : N.Domain} (hw : N.IsOmega ω) (hΩ : M.IsOmega (k ω))
    {z c s : E.Domain} {c₀ s₀ : M.Domain} (basis : Mc_nat_d (j ω) z c s)
    (fc : Fn0_d (k ω) (k ω) c₀) (fs : Fn0_d (k ω) (k ω) s₀)
    (rc : Fn_read_d k j c c₀) (rs : Fn_read_d k j s s₀) : ∃ z₀, Mc_nat_d (k ω) z₀ c₀ s₀ := by
  obtain ⟨z₁,empty,_⟩ := hw.1.1
  have emptyM y (hy : M.mem y (k z₁)) : False := ((kf z₁ y).mp hy).elim fun a ha => empty a ha.1
  have emptyE y (hy : E.mem y (j z₁)) : False := ((jf z₁ y).mp hy).elim fun a ha => empty a ha.1
  have ez : j z₁ = z := hE.eq_of_same_members _ _ (fun y => iff_of_false (emptyE y) (basis.empty y))
  refine ⟨k z₁,(mc_basis_iff_l hM hΩ).mp ⟨emptyM,fc,fs,?_,?_⟩⟩
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := (kf ω i).mp hi
    exact (rc.entry_l ki a z₁).mpr ((basis.constant_entry (j a) (j z₁)).mpr
      ⟨(image_member_l j ji jf).mpr ha,ez⟩)
  · intro i y hi hy succ
    obtain ⟨a,_,rfl⟩ := (kf ω i).mp hi
    obtain ⟨b,_,rfl⟩ := (kf ω y).mp hy
    have old := (image_successor_iff_l hN hM k ki kf).mpr succ
    exact (rs.entry_l ki a b).mpr ((basis.successor_entry (j a) (j b)).mpr
      ⟨(image_member_l j ji jf).mpr ((image_member_l k ki kf).mp hi),
        (image_successor_iff_l hN hE j ji jf).mp old⟩)

end YesMetaZFC.Model.Forcing.Internal
