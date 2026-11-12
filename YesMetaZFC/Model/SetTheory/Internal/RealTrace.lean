import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.Descriptive.Topology.Space
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 传递隶属模型的包含映射覆盖全部成员 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smem_full_l {c X R : M.Domain} (model : Smem_d I c X R) (trans : M.TransitiveSet X)
    (a : (smdl_structure_l I (R := R) model.1.2.1).Domain) (y : M.Domain) :
    M.mem y a.val ↔ ∃ x : (smdl_structure_l I (R := R) model.1.2.1).Domain,
      (smdl_structure_l I (R := R) model.1.2.1).mem x a ∧ x.val = y := by
  constructor
  · intro hy
    exact ⟨⟨y,trans a.val a.property y hy⟩,(smem_member_l I model.1 model.2 _ a).mpr hy,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact (smem_member_l I model.1 model.2 x a).mp hx

end YesMetaZFC.SetTheory.Internal

/-! ## 测试壳的实际背景实数集

实数集由背景在原载体中分离得到，不要求测试壳满足集合论模式。
已有内部 Baire 空间的成员方程与这一定义一致。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

theorem smem_fn0_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
    (A B f : (smdl_structure_l I (R := R) model.1.2.1).Domain) :
    Fn0_d A B f ↔ Fn0_d A.val B.val f.val := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let ρ : Env N 3 := ⟨fun k => [A,B,f].get k,fun _ => f⟩
  exact (fn0_sat_l (smem_ext_l I model.1 model.2 trans hE) ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
    ((smem_delta_image_l I model trans (fn0_delta_l ..) ρ).trans
      (fn0_sat_l hE (image_env_l (M := N) (N := M) Subtype.val ρ) (.bound 0) (.bound 1) (.bound 2)))

def Rb_reals_d (P ω B : M.Domain) : Prop :=
  ∀ x, M.mem x B ↔ M.mem x P ∧ Fn0_d ω ω x

theorem rb_reals_l (hZF : M.Models ZF) (P ω : M.Domain) : ∃ B, Rb_reals_d P ω B := by
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  let φ : UnarySchema 1 := { body := fn0_m (.bound 1) (.bound 1) .newest }
  obtain ⟨B,sep⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨B,fun x => (sep x).trans (and_congr_right fun _ => ?_)⟩
  exact fn0_sat_l hZF.1 (ρ.push x) (.bound 1) (.bound 1) .newest

theorem Smem_d.real_trace_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
    (native : (smdl_structure_l I (R := R) model.1.2.1).Models KP)
    {ω B : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    (space : Baire_d (kp_pair_l native) ω B) : Rb_reals_d P ω.val B.val := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  have real := smem_fn0_l I hE model trans ω ω
  intro x
  constructor
  · intro hx
    let x₀ : N.Domain := ⟨x,trans B.val B.property x hx⟩
    exact ⟨x₀.property,(real x₀).mp (fn0_of_function_l native ((space.2 x₀).mp
      ((smem_member_l I model.1 model.2 x₀ B).mpr hx)))⟩
  · rintro ⟨hx,fx⟩
    let x₀ : N.Domain := ⟨x,hx⟩
    exact (smem_member_l I model.1 model.2 x₀ B).mp
      ((space.2 x₀).mpr (fn0_function_l native ((real x₀).mpr fx)))

end YesMetaZFC.SetTheory.Internal
