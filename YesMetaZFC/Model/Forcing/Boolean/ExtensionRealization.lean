import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Iteration.Names.Generic

/-! # 在给定模型中实现吸收扩张

保持地模型参数的同构把规范泛型名称的值搬回原模型，得到真正的泛型集合。
同一次搬运同时保留中间模型的成员满覆盖嵌入和每个原对象的名称代表。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v k

theorem Miso_over_d.realize_l {A : Sort k} {M : Structure.{u}} (hZF : M.Models ZF)
    {B R z : M.Domain} (O : Cond_order_d M B R z) {U : M.Domain → Prop}
    (generic : Generic_d M B R z U) {N : Structure.{v}} (hN : Extensional N)
    {l : A → N.Domain → Prop} {j : A → M.Domain}
    (iso : Miso_over_d N (extension_l M hZF B R z U) l (fun x => Gval_d M B R z U (j x))) :
    ∃ e : M.Domain → N.Domain, Function.Injective e ∧
      (∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y) ∧
      (∀ x y, l x y ↔ e (j x) = y) ∧
      ∃ 𝒟, M.IsPowerSetOf 𝒟 B ∧ ∃ g : N.Domain,
        (∀ y, N.mem y g ↔ ∃ p, U p ∧ e p = y) ∧ Gset_d (e B) (e R) (e z) (e 𝒟) g ∧
        ∃ f : (extension_l M hZF B R z U).Domain → N.Domain,
          (∀ a b, a ∈ b ↔ N.mem (f a) (f b)) ∧ Function.Injective f ∧ Function.Surjective f ∧
          (∀ x a, Gval_d M B R z U x a ↔ e x = f a) ∧
          ∀ y, ∃ t a, Name_d M B t ∧ Qval_d M B R z U t a ∧ f a = y := by
  obtain ⟨f,mem,inj,onto,over⟩ := iso.symm_l
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨i,checks,full,ii⟩ := check_map_l O hZF generic hb
  let e := f ∘ i
  have covers a y : N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y := by
    obtain ⟨v,rfl⟩ := onto y
    apply (mem v (i a)).symm.trans
    apply (full a v).trans
    exact exists_congr fun c => and_congr_right fun _ => inj.eq_iff.symm
  have ground x a : Gval_d M B R z U x a ↔ e x = f a :=
    (gval_check_map_l O hZF generic hb i checks x a).trans inj.eq_iff.symm
  have fixed x y : l x y ↔ e (j x) = y := by
    obtain ⟨a,rfl⟩ := onto y
    exact (over x a).symm.trans (ground (j x) a)
  obtain ⟨𝒟,power⟩ := ZF.exists_powerSet hZF B
  obtain ⟨γ,name⟩ := gname_exists_l hZF (generic.proper b hb).1
  obtain ⟨G,value⟩ := name_value_l (R := R) (z := z) (U := U) name.1
  have filter y : N.mem y (f G) ↔ ∃ p, U p ∧ e p = y := by
    obtain ⟨a,rfl⟩ := onto y
    apply (mem a G).symm.trans
    apply (gname_value_l hZF O generic name value i checks a).trans
    exact exists_congr fun p => and_congr_right fun _ => inj.eq_iff.symm
  exact ⟨e,inj.comp ii,covers,fixed,𝒟,power,f G,filter,
    image_gset_l hZF hN e (inj.comp ii) covers generic filter,f,mem,inj,onto,ground,
    fun y => by
      obtain ⟨a,eq⟩ := onto y
      obtain ⟨t,nt,ta⟩ := value_name_l a
      exact ⟨t,a,nt,ta,eq⟩⟩

end YesMetaZFC.Model.Forcing.Internal
