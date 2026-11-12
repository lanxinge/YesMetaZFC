import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 原坐标块及逐坐标加强的成员满绝对性

从原图中出现的有序对回拉两个坐标，再逐个比较原函数行。
证明只使用两侧 KP，不假设整个包含初等，也不假设内部有限长度标准。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models KP) (hN : N.Models KP)
  (e : M.Domain → N.Domain) (inj : Function.Injective e)
  (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include hM hN inj full

private theorem fp_function_image_l {a b f : M.Domain} :
    M.IsSetFunctionFromTo (kp_pair_l hM) f a b ↔
      N.IsSetFunctionFromTo (kp_pair_l hN) (e f) (e a) (e b) := by
  let ρ : Env M 3 := ⟨fun i => [a,b,f].get i,fun _ => f⟩
  have same := (fn0_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
    ((delta0_image_l e inj full (fn0_delta_l ..) ρ).trans (fn0_sat_l hN.1 _ _ _ _))
  exact ⟨fun h => fn0_function_l hN (same.mp (fn0_of_function_l hM h)),
    fun h => fn0_function_l hM (same.mpr (fn0_of_function_l hN h))⟩

theorem image_fp_at_l {ω A n p : M.Domain} :
    Fp_at_d (kp_pair_l hM) ω A n p ↔ Fp_at_d (kp_pair_l hN) (e ω) (e A) (e n) (e p) := by
  have edge := image_entry_iff_l e inj full (KP.exists_pair hM) hN.1
  constructor
  · intro block
    refine ⟨⟨?_,?_⟩,fun i => ⟨?_,?_⟩,?_⟩
    · intro v hv
      obtain ⟨q,hq,rfl⟩ := (full p v).mp hv
      obtain ⟨i,s,pair⟩ := block.function.1 q hq
      exact ⟨e i,e s,image_kpair_l e full pair⟩
    · intro i s t is it
      obtain ⟨i₀,s₀,is₀,rfl,rfl⟩ := image_entry_pull_l hM hN.1 e inj full is
      obtain ⟨i₁,t₀,it₀,eq,rfl⟩ := image_entry_pull_l hM hN.1 e inj full it
      have eqi := inj eq
      subst i₁
      exact congrArg e (block.function.2 i₀ s₀ t₀ is₀ it₀)
    · intro hi
      obtain ⟨i₀,hi₀,rfl⟩ := (full n i).mp hi
      obtain ⟨s,is⟩ := (block.domain i₀).mp hi₀
      exact ⟨e s,(edge i₀ s p).mp is⟩
    · rintro ⟨s,is⟩
      obtain ⟨i₀,s₀,is₀,rfl,rfl⟩ := image_entry_pull_l hM hN.1 e inj full is
      exact (image_member_l e inj full).mpr ((block.domain i₀).mpr ⟨s₀,is₀⟩)
    · intro i s is
      obtain ⟨i₀,s₀,is₀,rfl,rfl⟩ := image_entry_pull_l hM hN.1 e inj full is
      obtain ⟨κ,m,ia,hm,fs⟩ := block.coordinates i₀ s₀ is₀
      exact ⟨e κ,e m,(edge i₀ κ A).mp ia,(image_member_l e inj full).mpr hm,
        (fp_function_image_l hM hN e inj full).mp fs⟩
  · intro block
    refine ⟨⟨?_,?_⟩,fun i => ⟨?_,?_⟩,?_⟩
    · intro v hv
      obtain ⟨i,s,pair⟩ := block.function.1 (e v) ((image_member_l e inj full).mpr hv)
      obtain ⟨i₀,s₀,pair₀,_,_⟩ := image_kpair_pull_l hM hN.1 e inj full pair
      exact ⟨i₀,s₀,pair₀⟩
    · intro i s t is it
      exact inj (block.function.2 (e i) (e s) (e t) ((edge i s p).mp is) ((edge i t p).mp it))
    · intro hi
      obtain ⟨s,is⟩ := (block.domain (e i)).mp ((image_member_l e inj full).mpr hi)
      obtain ⟨i₀,s₀,is₀,eq,_⟩ := image_entry_pull_l hM hN.1 e inj full is
      exact ⟨s₀,inj eq ▸ is₀⟩
    · rintro ⟨s,is⟩
      exact (image_member_l e inj full).mp ((block.domain (e i)).mpr ⟨e s,(edge i s p).mp is⟩)
    · intro i s is
      obtain ⟨κ,m,ia,hm,fs⟩ := block.coordinates (e i) (e s) ((edge i s p).mp is)
      obtain ⟨i₀,κ₀,ia₀,eq,rfl⟩ := image_entry_pull_l hM hN.1 e inj full ia
      obtain ⟨m₀,hm₀,rfl⟩ := (full ω m).mp hm
      exact ⟨κ₀,m₀,inj eq ▸ ia₀,hm₀,(fp_function_image_l hM hN e inj full).mpr fs⟩

theorem image_fp_le_l {p q : M.Domain} :
    Fp_le_d (kp_pair_l hM) p q ↔ Fp_le_d (kp_pair_l hN) (e p) (e q) := by
  have edge := image_entry_iff_l e inj full (KP.exists_pair hM) hN.1
  constructor
  · intro le i s is
    obtain ⟨i₀,s₀,is₀,rfl,rfl⟩ := image_entry_pull_l hM hN.1 e inj full is
    obtain ⟨t,it,sub⟩ := le i₀ s₀ is₀
    refine ⟨e t,(edge i₀ t p).mp it,fun y hy => ?_⟩
    obtain ⟨x,hx,rfl⟩ := (full s₀ y).mp hy
    exact (image_member_l e inj full).mpr (sub x hx)
  · intro le i s is
    obtain ⟨t,it,sub⟩ := le (e i) (e s) ((edge i s q).mp is)
    obtain ⟨i₀,t₀,it₀,eq,rfl⟩ := image_entry_pull_l hM hN.1 e inj full it
    exact ⟨t₀,inj eq ▸ it₀,fun x hx =>
      (image_member_l e inj full).mp (sub (e x) ((image_member_l e inj full).mpr hx))⟩

end YesMetaZFC.Model.Forcing.Internal
