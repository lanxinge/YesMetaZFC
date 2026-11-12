import YesMetaZFC.Model.SetTheory.Relations.SeparationSource
import YesMetaZFC.Model.SetTheory.Relations.Ultrafilter
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.Filter.Projection

/-! # 原关系坐标子集代数的实际逆像

在原模型内分离投影逆像，坐标交换和内部单值性保证它读出背景中同一逆像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rt_source_d.pull_l {ω c X R c' Y S q D E u v t P Q A : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (ext : Rf_ext_d I Y S) (d e p : (smdl_structure_l I (R := S) source.2.1).Domain)
    (fp : Fn0_d e d p) (fu : Fn0_d D Y u) (fv : Fn0_d E Y v) (ft : Fn0_d E D t)
    (dv : ∀ s x, Rd_entry_d s x v → Rd_entry_d x e.val S)
    (comm : ∀ s r x y, Rd_entry_d s r t → Rd_entry_d s x v → Rd_entry_d r y u → Rf_val_d I Y S x y p.val)
    (hP : Rt_source_d I Y S D u P) (hQ : Rt_source_d I Y S E v Q) (hA : M.mem A P) :
    ∃ B, M.mem B Q ∧ Pull_d E t A B := by
  have en := ext.native_l I source.2.1
  obtain ⟨Z, hZ, trA⟩ := (hP A).mp hA
  let z : (smdl_structure_l I (R := S) source.2.1).Domain := ⟨Z, hZ⟩
  let ρ : Env (smdl_structure_l I (R := S) source.2.1) 2 := ⟨Fin.cases p (fun _ => z), fun _ => z⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 3))
    (rd_entry0_m (.bound 1) .newest (.bound 2))) }
  have matrix x : φ.denote ρ x ↔ ∃ y : (smdl_structure_l I (R := S) source.2.1).Domain,
      Rd_entry_d y.val Z S ∧ Rd_entry_d x y p := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, rd_entry0_sat_l en]; rfl
  obtain ⟨H, hH, cut⟩ := sc_separate_raw_l I hZF hω hm theory source hq φ ρ e
  obtain ⟨B, trB⟩ := rt_trace_exists_l I hZF E v S H
  refine ⟨B, (hQ B).mpr ⟨H, hH, trB⟩, fun s => ?_⟩
  by_cases hs : M.mem s E
  · obtain ⟨r, hr, hsr⟩ := ft.2.1 s hs
    obtain ⟨x, hx, hsx⟩ := fv.2.1 s hs
    obtain ⟨y, hy, hry⟩ := fu.2.1 r hr
    let x' : (smdl_structure_l I (R := S) source.2.1).Domain := ⟨x, hx⟩
    let y' : (smdl_structure_l I (R := S) source.2.1).Domain := ⟨y, hy⟩
    have xy := (rf_val_native_l I source.2.1 en x' y' p).mp (comm s r x y hsr hsx hry)
    have read : Rd_entry_d x H S ↔ Rd_entry_d y Z S :=
      (cut x').trans ((and_iff_right (dv s x hsx)).trans ((matrix x').trans
        ⟨fun ⟨w, hw, xw⟩ => (show w.val = y from congrArg Subtype.val
          (fp.2.2 x' (fp.bound_l xy).1 w (fp.bound_l xw).2 y' (fp.bound_l xy).2 xw xy)) ▸ hw,
          fun h => ⟨y', h, xy⟩⟩))
    apply (trB.value_l I (fn0_function_l (ZF.modelsKP hZF) fv) hsx).trans
      (read.trans ((trA.value_l I (fn0_function_l (ZF.modelsKP hZF) fu) hry).symm.trans ?_))
    exact ⟨fun h => ⟨hs, r, h, hsr⟩, fun ⟨_, r', h, hsr'⟩ =>
      (fn0_function_l (ZF.modelsKP hZF) ft).1.2 s r' r hsr' hsr ▸ h⟩
  · exact iff_of_false (fun h => hs ((trB s).mp h).1) (fun h => hs h.1)

end YesMetaZFC.SetTheory.Internal
