import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.SetTheory.Internal.RealTrace

/-! # 完整函数图读取与成员满像的识别 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u v w
variable {N : Structure.{u}} {M : Structure.{v}} {E : Structure.{w}}

/-- 固定同一地参数的成员满映射，把完整函数图读取变为实际对象相等。 -/
theorem Fn_read_d.image_eq_l (hM : M.Models KP) (hE : E.Models KP)
    (e : E.Domain → M.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, M.mem y (e a) ↔ ∃ b, E.mem b a ∧ e b = y)
    {k : N.Domain → M.Domain} {j : N.Domain → E.Domain}
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    (commute : ∀ a, e (j a) = k a)
    {D A : N.Domain} {F : E.Domain} {x : M.Domain}
    (f : Fn0_d (j D) (j A) F) (fx : M.IsSetRelation (kp_pair_l hM) x)
    (read : Fn_read_d k j F x) : e F = x := by
  have ff := fn0_function_l hE f
  have image := image_function_l (hEN := hM.1) (hPN := KP.exists_pair hM) e ei ef ff
  have covered {a : N.Domain} {y : E.Domain} (hy : E.mem y (j a)) : ∃ b, j b = y := by
    have hy' := (image_member_l e ei ef).mpr hy
    rw [commute] at hy'
    obtain ⟨b,_,hb⟩ := (kf a (e y)).mp hy'
    exact ⟨b,ei ((commute b).trans hb)⟩
  apply image.1.1.eq_of_pairMember_iff hM.1 fx
  intro a b
  constructor
  · intro edge
    obtain ⟨u,v,uv,rfl,rfl⟩ := (image_entries_l e ef ff.1.1 a b).mp edge
    obtain ⟨c,rfl⟩ := covered (f.bound_l uv).1
    obtain ⟨d,rfl⟩ := covered (f.bound_l uv).2
    exact (read _ _).mpr ⟨c,d,(commute c).symm,(commute d).symm,uv⟩
  · intro edge
    obtain ⟨c,d,rfl,rfl,cd⟩ := (read a b).mp edge
    exact (image_entries_l e ef ff.1.1 _ _).mpr ⟨j c,j d,cd,commute c,commute d⟩

theorem function_read_ground_l (hN : N.Models KP) (hM : Extensional M) (hE : Extensional E)
    (k : N.Domain → M.Domain) (ki : Function.Injective k)
    (kf : ∀ a y, M.mem y (k a) ↔ ∃ b, N.mem b a ∧ k b = y)
    (j : N.Domain → E.Domain) (ji : Function.Injective j)
    (jf : ∀ a y, E.mem y (j a) ↔ ∃ b, N.mem b a ∧ j b = y)
    {f : N.Domain} (rel : N.IsSetRelation (SetTheory.InnerModel.kp_pair_l hN) f) : Fn_read_d k j (j f) (k f) := by
  have left := image_entry_iff_l k ki kf (KP.exists_pair hN) hM
  have right := image_entry_iff_l j ji jf (KP.exists_pair hN) hE
  intro a b
  constructor
  · intro edge
    obtain ⟨a₀,b₀,old,rfl,rfl⟩ := (image_entries_l k kf rel a b).mp edge
    exact ⟨a₀,b₀,rfl,rfl,(right a₀ b₀ f).mp old⟩
  · rintro ⟨a₀,b₀,rfl,rfl,edge⟩
    exact (left a₀ b₀ f).mp ((right a₀ b₀ f).mpr edge)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原地模型实数在指定泛型中的完整名字证书

检查名字的地嵌入保持原函数图，逐边读取仍为同一个背景实数。
该证书为保持原泛型的初始帧提供统一实数，无须先进行一次吸收。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hM : Extensional M)
  {c X R : M.Domain} (source : Smem_d I c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
include hM trans native

theorem fn_bg_ground_l (B T z D A f : (smdl_structure_l I (R := R) source.1.2.1).Domain) (H : M.Domain)
    (order : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) B T z)
    (generic : Generic_d (smdl_structure_l I (R := R) source.1.2.1) B T z (fun p => M.mem p.val H))
    (fn : Fn0_d D A f) : Fn_bg_d X B.val T.val z.val D.val A.val H f.val := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨j,checks,jfull,ji⟩ := check_map_l order native generic hb
  have hE := preserves_zf_l order native generic
  let ρ : Env N 3 := ⟨fun i => [D,A,f].get i,fun _ => f⟩
  have fn' : Fn0_d (j D) (j A) (j f) :=
    (fn0_sat_l hE.1 (image_env_l j ρ) (.bound 0) (.bound 1) (.bound 2)).mp
      ((delta0_image_l j ji jfull (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ρ).mp
        ((fn0_sat_l native.1 ρ (.bound 0) (.bound 1) (.bound 2)).mpr fn))
  have read := function_read_ground_l (ZF.modelsKP native) hM hE.1 Subtype.val inj full j ji jfull
    (fn0_function_l (ZF.modelsKP native) fn).1.1
  exact (fn_bg_read_l I hM source trans native.1 B T z D A H f.val).mpr
    (fn_code_of_value_l native order generic Subtype.val j
      (fun a => (gval_check_map_l order native generic hb j checks a (j a)).mpr rfl) fn' read)

end YesMetaZFC.Model.Forcing.Internal
