import YesMetaZFC.Model.Forcing.Functions.Generic
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Boolean.GroundGeneric

/-! # 商扩张中原泛型的实际集合

名字由每个条件 p 所加权的检查名字 p̌ 组成。精确求值方程识别其全部成员，
故同一集合对任意旧稠密参数域给出背景泛型证书。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

theorem generic_name_l (hZF : M.Models ZF) {B b : M.Domain} (hb : M.mem b B) :
    ∃ τ, Name_d M B τ ∧ ∀ s p, Entry_d M s p τ ↔ M.mem p B ∧ Check_d M b p s := by
  obtain ⟨S,members,names⟩ := check_image_l hZF hb B
  let ρ : Env M 1 := ⟨fun _ => b,fun _ => b⟩
  let φ : BinarySchema 1 := { body := check_m (.bound 2) .newest (.bound 1) }
  have read s p : φ.denote ρ s p ↔ Check_d M b p s := check_sat_l M hZF.1 ..
  obtain ⟨τ,name,_,entries⟩ := name_comp_l M hZF φ ρ B S names
  refine ⟨τ,name,fun s p => (entries s p).trans ?_⟩
  exact ⟨fun h => ⟨h.2.1,(read s p).mp h.2.2⟩,
    fun ⟨hp,check⟩ => ⟨(members s).mpr ⟨p,hp,check⟩,hp,(read s p).mpr check⟩⟩

theorem Generic_d.value_set_l (hZF : M.Models ZF) {B R z : M.Domain}
    (O : Cond_order_d M B R z) {G : M.Domain → Prop} (generic : Generic_d M B R z G)
    (j : M.Domain → (extension_l M hZF B R z G).Domain)
    (ground : ∀ a, Gval_d M B R z G a (j a)) :
    ∃ H : (extension_l M hZF B R z G).Domain,
      (∀ x, x ∈ H ↔ ∃ p, G p ∧ j p = x) ∧
      ∀ D, Gset_d (j B) (j R) (j z) (j D) H := by
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨j₀,checks,full,inj⟩ := check_map_l O hZF generic hb
  have eq : j₀ = j := funext fun a => (gval_check_map_l O hZF generic hb j₀ checks a (j a)).mp (ground a)
  subst j₀
  obtain ⟨τ,name,entries⟩ := generic_name_l hZF (generic.proper b hb).1
  obtain ⟨H,value⟩ := name_value_l (R := R) (z := z) (U := G) name
  have members x : x ∈ H ↔ ∃ p, G p ∧ j p = x := by
    constructor
    · intro hx
      obtain ⟨s,p,sp,hp,sx⟩ := (qval_mem_l O hZF generic value).mp hx
      exact ⟨p,hp,qval_unique_l (checks p s ((entries s p).mp sp).2) sx⟩
    · rintro ⟨p,hp,rfl⟩
      obtain ⟨s,check,_,_⟩ := zf_check_l M hZF (generic.proper b hb).1 p
      exact (qval_mem_l O hZF generic value).mpr
        ⟨s,p,(entries s p).mpr ⟨(generic.proper p hp).1,check⟩,hp,checks p s check⟩
  exact ⟨H,members,fun _ => image_gset_l hZF (extension_ext_l O hZF generic) j inj full generic members⟩

end YesMetaZFC.Model.Forcing.Internal
