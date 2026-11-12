import YesMetaZFC.Model.SetTheory.ReducedPower.RelationFormulaImage
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.Model.SetTheory.Relations.Constant

/-! # 同一原关系商中的函数应用

坐标代表、函数代表及常值代表均由同一个商投影读取。
对三者应用完整公式 Łoś，得到原关系目标中的 j(f)([id])=[f]。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 坐标图由当前源中的恒等函数实现，故确实属于原代表族。 -/
theorem rc_coordinate_l {ω c' Y S D t G : M.Domain}
    (hω : M.IsOmega ω) (source : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (family : Rc_family_d I Y S D d.val t G) : M.mem t G := by
  have en := ext.native_l I source.2.1
  obtain ⟨f, ff, diagonal⟩ := sc_identity_raw_l hZF hω source theory en d
  apply (family t).mpr
  refine ⟨ft, f.val, (rf_fun_native_l I source.2.1 en d f).mpr ⟨d, ff⟩, ?_⟩
  intro s x y hsx
  have fx := (rf_val_native_l I source.2.1 en ⟨x, (ft.bound_l hsx).2⟩ ⟨x, (ft.bound_l hsx).2⟩ f).mpr
    (diagonal ⟨x, (ft.bound_l hsx).2⟩ (domain s x hsx))
  constructor
  · intro hsy
    have eq := (fn0_function_l (ZF.modelsKP hZF) ft).1.2 s y x hsy hsx
    exact eq.symm ▸ fx
  · intro val
    have eq := ((rf_fun_native_l I source.2.1 en d f).mpr ⟨d, ff⟩).unique_l I ext val fx
    exact eq.symm ▸ hsx

theorem rc_application_l {ω c' Y S D t P U o G p C T b V W j f g k A B K a v F : M.Domain}
    (hω : M.IsOmega ω) (source : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain) (uniform : Sc_uniform_d I ω Y S d.val)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : FilterZF.Rel_ultra_d D P U)
    (family : Rc_family_d I Y S D d.val t G) (model : Rp_model_d I D Y U S o G p C T)
    (target : Smdl_d I b V W) (hj : Smap_d I ω o b C V j)
    (ff : Rf_fun_d I Y S d.val f) (graph : Rc_graph_d I Y S t f g) (constant : Rs_const_d D f k)
    (htA : Rd_entry_d t A p) (hgB : Rd_entry_d g B p) (hkK : Rd_entry_d k K p)
    (hAa : Rd_entry_d A a j) (hBv : Rd_entry_d B v j) (hKF : Rd_entry_d K F j) :
    Rf_val_d I V W a v F := by
  have en := ext.native_l I source.2.1
  have ht := model.map.projection.input_mem_of_pairMember htA
  have hg := model.map.projection.input_mem_of_pairMember hgB
  have hk := model.map.projection.input_mem_of_pairMember hkK
  obtain ⟨_, i, fi, gi⟩ := (family t).mp ht
  obtain ⟨fk, k', fk', gk⟩ := (family k).mp hk
  let ρ : Env (smdl_structure_l I (R := W) target.2.1) 3 :=
    ⟨Fin.cases ⟨a, hj.1.1.output_mem_of_pairMember hAa⟩
      (Fin.cases ⟨v, hj.1.1.output_mem_of_pairMember hBv⟩ (fun _ => ⟨F, hj.1.1.output_mem_of_pairMember hKF⟩)),
      fun _ => ⟨F, hj.1.1.output_mem_of_pairMember hKF⟩⟩
  have los := rc_formula_image_l hZF hω source ext theory d uniform ft domain hP hU family model target hj
    (rd_entry0_m .newest (.bound 1) (.bound 2)) (by simp -implicitDefEqProofs)
    (Fin.cases i (Fin.cases f (fun _ => k'))) (Fin.cases t (Fin.cases g (fun _ => k)))
    (Fin.cases fi (Fin.cases ff (fun _ => fk'))) (Fin.cases ht (Fin.cases hg (fun _ => hk)))
    (Fin.cases gi (Fin.cases graph (fun _ => gk))) ρ
    (Fin.cases ⟨A, htA, hAa⟩ (Fin.cases ⟨B, hgB, hBv⟩ (fun _ => ⟨K, hkK, hKF⟩)))
  refine ⟨(ρ.bound 0).property, (ρ.bound 1).property, (ρ.bound 2).property, los.mpr ⟨D, hU.base.top, ?_⟩⟩
  intro s hs η entries
  have eq := (fn0_function_l (ZF.modelsKP hZF) fk).1.2 s (η.bound 2).val f (entries 2) (constant s hs)
  have fv := (graph s (η.bound 0).val (η.bound 1).val (entries 0)).mp (entries 1)
  have val := (rf_val_native_l I source.2.1 en (η.bound 0) (η.bound 1) ⟨f, ff.mem_l I⟩).mp fv
  have ef : (⟨f, ff.mem_l I⟩ : (smdl_structure_l I (R := S) source.2.1).Domain) = η.bound 2 := Subtype.ext eq.symm
  apply (rd_entry0_sat_l en ..).mpr
  change Rd_entry_d (η.bound 0) (η.bound 1) (η.bound 2)
  exact ef ▸ val

end YesMetaZFC.SetTheory.Internal
