import YesMetaZFC.Model.SetTheory.Internal.RelationLayer
import YesMetaZFC.Model.SetTheory.Internal.RelativizationCorrect

/-! # 完整低层实现上的全内部程序解释

实现图的实际值域与原低层同构；限制编译器的守卫取高模型中的层对象。
同构和限制两步都量化全部内部程序，故非标准程序不需解码成宿主语法树。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rr_layer_d.program_l {ω Γ Y S H k c R E D F n r b m G T u f g : M.Domain}
    (h : Rr_layer_d I Γ Y S H k) (hω : M.IsOmega ω) (model : Smem_d I c Γ R)
    (hE : M.IsFunctionSpace I E ω Γ) (hD : M.IsFunctionSpace I D ω Y)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) (bound : Sbound_d I F b)
    (state : Sr_state_d I ω b F n m G T) (root : Rd_entry_d r u T)
    (hf : M.mem f E) (hg : M.mem g D) (guard : Rd_entry_d b H g)
    (params : ∀ i x y, M.mem i b → Rd_entry_d i x f → Rd_entry_d x y k → Rd_entry_d i y g) :
    Ssat_d I Γ R E F n r f ↔ Ssat_d I Y S D G m u g := by
  obtain ⟨A, range⟩ := ZF.exists_range_of_setFunction hZF I h.injection.1.1 h.injection.1.2.1
  have fn : M.IsSetFunctionFromTo I k Γ A :=
    ⟨h.injection.1.1, h.injection.1.2.1, fun x hx =>
      (h.injection.1.2.2 x hx).imp fun y hy => ⟨(range y).mpr ⟨x, hy.2⟩, hy.2⟩⟩
  have bij : M.IsSetBijectionFromTo I k Γ A :=
    ⟨⟨fn, h.injection.2⟩, fun y hy => ((range y).mp hy).elim fun x hx =>
      ⟨x, fn.input_mem_of_pairMember hx, hx⟩⟩
  have atoms a b x y (ha : Rd_entry_d a x k) (hb : Rd_entry_d b y k) :
      Rd_entry_d a b R ↔ Rd_entry_d x y S := by
    apply (model.2 a b).trans
    exact ⟨fun hh => (h.predecessors b y hb x).mpr ⟨a, hh.2.2, ha⟩, fun hh => by
      obtain ⟨z, hz, hzx⟩ := (h.predecessors b y hb x).mp hh
      exact ⟨fn.input_mem_of_pairMember ha, fn.input_mem_of_pairMember hb,
        h.injection.2 z a x hzx ha ▸ hz⟩⟩
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω A
  obtain ⟨v, fv, map⟩ := smap_assign_exists_l I hZF fn ((hE f).mp hf)
  have context : Sr_context_d I ω A S Y S H K D := by
    refine ⟨fun x hx => ((range x).mp hx).elim fun a ha => h.injection.1.output_mem_of_pairMember ha,
      fun _ _ _ _ => Iff.rfl, ?_, hK, hD⟩
    intro x _
    exact (h.image x).trans ⟨fun ⟨a, _, ha⟩ => (range x).mpr ⟨a, ha⟩,
      fun hx => ((range x).mp hx).elim fun a ha => ⟨a, fn.input_mem_of_pairMember ha, ha⟩⟩
  have agree : Senv_agree_d I b v g := by
    intro i y hi
    have hiω := hω.transitive hZF b hb i hi
    obtain ⟨x, hx, hix⟩ := ((hE f).mp hf).2.2 i hiω
    obtain ⟨z, _, hxz⟩ := fn.2.2 x hx
    have hiv := map i hiω x z hix hxz
    have hig := params i x z hi hix hxz
    exact ⟨fun hy => fv.1.2 i y z hy hiv ▸ hig,
      fun hy => ((hD g).mp hg).1.2 i y z hy hig ▸ hiv⟩
  exact (smap_row_l I hZF bij atoms hE hK hF hr f v hf ((hK v).mpr fv) map).trans
    (state.correct_l I hZF hF bound context hr root v g ((hK v).mpr fv) hg guard agree)

end YesMetaZFC.SetTheory.Internal
