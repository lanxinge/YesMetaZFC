import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationSyntax
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Lift
import YesMetaZFC.Model.SetTheory.Internal.RelationComposition

/-! # 原关系函数码的商赋值与支撑拉回赋值

背景选择仅选择已有的源内函数码；坐标图仍须通过精确函数族检验。
每个实际商赋值因此有同一个 ω 长函数码赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_representatives_l {ω c Y S D t U o G p C T v : M.Domain}
    (source : Smdl_d I c Y S) (ext : Rf_ext_d I Y S)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain) (ft : Fn0_d D Y t)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T) (hv : M.IsSetFunctionFromTo I v ω C) :
    ∃ a, M.IsSetFunctionFromTo I a ω Y ∧ Rc_eval_d I ω d.val Y S t p a v := by
  have en := ext.native_l I source.2.1
  let ρ : Env M 7 := ⟨Fin.cases Y (Fin.cases S (Fin.cases d.val (Fin.cases t
    (Fin.cases G (Fin.cases p (fun _ => v)))))), fun _ => Y⟩
  let φ : BinarySchema 7 := {
    body := .conj (rf_fun_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3) (.bound 4) .newest)
      (Formula.existsMem (.bound 6) (.existsE (.conj
        (rc_graph_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 5) (.bound 7) (.bound 2) (.bound 1))
        (.conj (rd_entry0_m (.bound 1) .newest (.bound 9)) (rd_entry0_m (.bound 3) .newest (.bound 10)))))) }
  have read i f : φ.denote ρ i f ↔ Rf_fun_d I Y S d.val f ∧ ∃ g, M.mem g G ∧
      ∃ B, Rc_graph_d I Y S t f g ∧ Rd_entry_d g B p ∧ Rd_entry_d i B v := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, rf_fun_sat_l I,
      Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, rc_graph_sat_l I hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨a, ha, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := ω) (Y := Y) (fun i hi => by
    obtain ⟨B, hB, hiB⟩ := hv.2.2 i hi
    obtain ⟨g, gp⟩ := (model.map.range B).mp hB
    have hg := model.map.projection.input_mem_of_pairMember gp
    obtain ⟨fg, Q, f, ff, decode⟩ := (hG g).mp hg
    exact ⟨f.val, f.property, (read i f.val).mpr ⟨(rf_fun_native_l I source.2.1 en d f).mpr ⟨Q, ff⟩,
      g, hg, B, (rc_graph_native_l I source.2.1 en ft fg f).mpr decode, gp, hiB⟩⟩)
  refine ⟨a, ha, fun i hi => ?_⟩
  obtain ⟨f, _, hif⟩ := ha.2.2 i hi
  obtain ⟨ff, g, _, B, graph, gp, hiB⟩ := (read i f).mp (select i f hif)
  exact ⟨f, g, B, hif, ff, graph, gp, hiB⟩

theorem rc_pull_assignment_l {ω c X R c' Y S q a : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (ext : Rf_ext_d I Y S) (d e p : (smdl_structure_l I (R := S) model.2.1).Domain)
    (fp : Fn0_d e d p) (ha : M.IsSetFunctionFromTo I a ω Y) (repr : Pe_repr_d I ω d.val Y S a) :
    ∃ b, M.IsSetFunctionFromTo I b ω Y ∧ ∀ i f g, M.mem i ω → Rd_entry_d i f a → Rd_entry_d i g b →
      Rf_pull_d hZF Y S e.val p.val f g := by
  let ρ : Env M 5 := ⟨Fin.cases Y (Fin.cases S (Fin.cases e.val (Fin.cases p.val (fun _ => a)))), fun _ => Y⟩
  let φ : BinarySchema 5 := {
    body := Formula.existsMem (.bound 2) (.conj (rd_entry0_m (.bound 2) .newest (.bound 7))
      (rf_pull_m (.bound 3) (.bound 4) (.bound 5) (.bound 6) .newest (.bound 1))) }
  have read i g : φ.denote ρ i g ↔ ∃ f, M.mem f Y ∧ Rd_entry_d i f a ∧ Rf_pull_d hZF Y S e.val p.val f g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, rf_pull_sat_l hZF]; rfl
  obtain ⟨b, hb, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := ω) (Y := Y) (fun i hi => by
    obtain ⟨f, hf, hif⟩ := ha.2.2 i hi
    obtain ⟨g, hg⟩ := rf_pull_exists_l hZF hω hX hm theory model hq ext e d p fp (repr i f hi hif)
    exact ⟨g, hg.1.mem_l I, (read i g).mpr ⟨f, hf, hif, hg⟩⟩)
  refine ⟨b, hb, fun i f g _ hif hig => ?_⟩
  obtain ⟨f', _, hif', pull⟩ := (read i g).mp (select i g hig)
  exact ha.1.2 i f' f hif' hif ▸ pull

end YesMetaZFC.SetTheory.Internal
