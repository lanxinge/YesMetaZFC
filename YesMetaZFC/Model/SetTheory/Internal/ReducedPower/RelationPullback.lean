import YesMetaZFC.Model.SetTheory.Internal.RelationComposition
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationSyntax
import YesMetaZFC.Model.SetTheory.Internal.PointwiseContext

/-! # 原关系函数代表沿实际支撑坐标拉回

原关系内部先复合函数码。坐标交换方程再证明其实际图恰是旧代表的拉回，
由此在既有源内代表族之间构造唯一的函数图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rc_graph_d.pull_l {Y S D E u v t p d f g f' g' : M.Domain}
    (h : Rc_graph_d I Y S u f g) (fu : Fn0_d D Y u) (fv : Fn0_d E Y v) (ft : Fn0_d E D t)
    (comm : ∀ s r x y, Rd_entry_d s r t → Rd_entry_d s x v → Rd_entry_d r y u → Rf_val_d I Y S x y p)
    (fg : Fn0_d D Y g) (pull : Rf_pull_d hZF Y S d p f f') (comp : Cp0_d E D Y t g g') :
    Rc_graph_d I Y S v f' g' := by
  intro s x z hsx
  obtain ⟨r, _, hsr⟩ := ft.2.1 s (fv.bound_l hsx).1
  obtain ⟨y, _, hry⟩ := fu.2.1 r (ft.bound_l hsr).2
  by_cases hz : M.mem z Y
  · exact (comp.value_l ft fg hsr).trans ((h r y z hry).trans (pull.2 x y z hz (comm s r x y hsr hsx hry)).symm)
  · exact iff_of_false (fun h => hz (comp.1.bound_l h).2) (fun h => hz (h.bounds_l I).2.1)

theorem rc_pullback_family_l {ω c X R c' Y S q D E u v t F G : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d e p : (smdl_structure_l I (R := S) model.2.1).Domain) (fp : Fn0_d e d p)
    (fu : Fn0_d D Y u) (fv : Fn0_d E Y v) (ft : Fn0_d E D t)
    (comm : ∀ s r x y, Rd_entry_d s r t → Rd_entry_d s x v → Rd_entry_d r y u → Rf_val_d I Y S x y p.val)
    (hF : ∀ g, M.mem g F ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) model.2.1).Domain), Rd_entry_d s x.val u →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (hG : ∀ g, M.mem g G ↔ Fn0_d E Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d e B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) model.2.1).Domain), Rd_entry_d s x.val v →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) :
    ∃ K, M.IsSetFunctionFromTo I K F G ∧ ∀ f g, Rd_entry_d f g K ↔
      M.mem f F ∧ M.mem g G ∧ Cp0_d E D Y t f g := by
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω hm.1 model (rf_ext_mem_l I hZF.1 hX hm)
  have en := ext.native_l I model.2.1
  let ρ : Env M 5 := ⟨Fin.cases G (Fin.cases t (Fin.cases Y (Fin.cases D (fun _ => E)))), fun _ => E⟩
  let φ : BinarySchema 5 := {
    body := .conj (.mem .newest (.bound 2)) (cp0_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have read f g : φ.denote ρ f g ↔ M.mem g G ∧ Cp0_d E D Y t f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, cp0_sat_l hZF.1]; rfl
  obtain ⟨K, fn, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := G)
    (fun f hf => by
      obtain ⟨ff, B, a, fa, decode⟩ := (hF f).mp hf
      have af := (rf_fun_native_l I model.2.1 en d a).mpr ⟨B, fa⟩
      have ga := (rc_graph_native_l I model.2.1 en fu ff a).mpr decode
      obtain ⟨b, pull⟩ := rf_pull_exists_l hZF hω hX hm theory model hq ext e d p fp af
      obtain ⟨g, comp⟩ := cp0_exists_l (ZF.modelsKP hZF) ft ff
      let b' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨b, pull.1.mem_l I⟩
      obtain ⟨C, fb⟩ := (rf_fun_native_l I model.2.1 en e b').mp pull.1
      have gb := ga.pull_l hZF fu fv ft comm ff pull comp
      exact ⟨g, (read f g).mpr ⟨(hG g).mpr ⟨comp.1, C, b', fb,
        (rc_graph_native_l I model.2.1 en fv comp.1 b').mp gb⟩, comp⟩⟩)
    (fun f hf g k hg hk => cp0_unique_l hZF.1 ft ((hF f).mp hf).1 ((read f g).mp hg).2 ((read f k).mp hk).2)
    (fun f g _ hg => ((read f g).mp hg).1)
  exact ⟨K, fn, fun f g => (spec f g).trans (and_congr_right fun _ => read f g)⟩

end YesMetaZFC.SetTheory.Internal
