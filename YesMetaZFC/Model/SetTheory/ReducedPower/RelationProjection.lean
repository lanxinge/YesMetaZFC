import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.Relations.Composition
import YesMetaZFC.Model.SetTheory.Types.PointwiseWitness
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationRestriction
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationTrace
import YesMetaZFC.Model.SetTheory.ReducedPower.ProjectionLaws

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
    (hω : M.IsOmega ω) (hm : Smdl_d I c X R)
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
    obtain ⟨g, hg⟩ := rf_pull_exists_l hZF hω hm theory model hq ext e d p fp (repr i f hi hif)
    exact ⟨g, hg.1.mem_l I, (read i g).mpr ⟨f, hf, hif, hg⟩⟩)
  refine ⟨b, hb, fun i f g _ hif hig => ?_⟩
  obtain ⟨f', _, hif', pull⟩ := (read i g).mp (select i g hig)
  exact ha.1.2 i f' f hif' hif ▸ pull

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系函数代表沿实际支撑坐标拉回

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
    (hω : M.IsOmega ω) (ex : Rf_ext_d I X R) (hm : Smdl_d I c X R)
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
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω hm model ex
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
      obtain ⟨b, pull⟩ := rf_pull_exists_l hZF hω hm theory model hq ext e d p fp af
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

/-! ## 原关系分量之间的完整内部初等过渡

内部函数码先沿原关系投影复合，再下降为同一实际代表族上的商图。
精确真值集的坐标逆像与真实测度协调给出全部内部公式码的初等性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_projection_embedding_l {ω c X R c' Y S q D E u v t P Q U V o₀ o₁ G₀ G₁ p₀ p₁ C₀ C₁ T₀ T₁ : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d I X R) (hm : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d e p : (smdl_structure_l I (R := S) source.2.1).Domain)
    (uniform₀ : Sc_uniform_d I ω Y S d.val) (uniform₁ : Sc_uniform_d I ω Y S e.val)
    (fp : Fn0_d e d p) (fu : Fn0_d D Y u) (fv : Fn0_d E Y v)
    (du : ∀ s x, Rd_entry_d s x u → Rd_entry_d x d.val S)
    (dv : ∀ s x, Rd_entry_d s x v → Rd_entry_d x e.val S)
    (comm : ∀ s r x y, Rd_entry_d s r t → Rd_entry_d s x v → Rd_entry_d r y u → Rf_val_d I Y S x y p.val)
    (hP : Rt_source_d I Y S D u P) (hQ : Rt_source_d I Y S E v Q)
    (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V) (ht : Push_d D E P Q U V t)
    (hG₀ : ∀ g, M.mem g G₀ ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val u →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (hG₁ : ∀ g, M.mem g G₁ ↔ Fn0_d E Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d e B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val v →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model₀ : Rp_model_d I D Y U S o₀ G₀ p₀ C₀ T₀) (model₁ : Rp_model_d I E Y V S o₁ G₁ p₁ C₁ T₁) :
    ∃ K j, M.IsSetFunctionFromTo I K G₀ G₁ ∧
      (∀ f g, Rd_entry_d f g K ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d E D Y t f g) ∧
      Smap_d I ω o₀ o₁ C₀ C₁ j ∧ Rp_lift_d I K p₀ p₁ j := by
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω hm source ex
  have current := theory.map_l I hZF hω hm source hq
  obtain ⟨K, hK, liftK⟩ := rc_pullback_family_l hZF hω ex hm theory source hq d e p fp fu fv ht.1 comm hG₀ hG₁
  have kernel f g f' g' (hf : Rd_entry_d f f' K) (hg : Rd_entry_d g g' K) :
      Rp_eq_d Y U f g ↔ Rp_eq_d Y V f' g' := by
    obtain ⟨ff, _, F, _, fd⟩ := (hG₀ f).mp (hK.input_mem_of_pairMember hf)
    obtain ⟨fg, _, G, _, gd⟩ := (hG₀ g).mp (hK.input_mem_of_pairMember hg)
    have cf := ((liftK f f').mp hf).2.2
    have cg := ((liftK g g').mp hg).2.2
    obtain ⟨A, hA, atom⟩ := rc_atom_trace_l hZF hω ex hm theory source hq d F G fu du hP fd gd true
    have trace s : M.mem s A ↔ M.mem s D ∧ ∃ x, M.mem x Y ∧ Rd_entry_d s x f ∧ Rd_entry_d s x g :=
      (atom s).trans (and_congr_right fun _ =>
        ⟨fun ⟨x, hx, y, _, hfx, hgy, eq⟩ => ⟨x, hx, hfx, eq.symm ▸ hgy⟩,
          fun ⟨x, hx, hfx, hgx⟩ => ⟨x, hx, x, hx, hfx, hgx, rfl⟩⟩)
    obtain ⟨B, hB, pull, measure⟩ := ht.2 A hA
    have trace' s : M.mem s B ↔ M.mem s E ∧ ∃ x, M.mem x Y ∧ Rd_entry_d s x f' ∧ Rd_entry_d s x g' := by
      apply (pull s).trans
      refine ⟨fun ⟨hs, r, hr, hsr⟩ => ?_, fun ⟨hs, x, hx, hsx, hsy⟩ => ?_⟩
      · obtain ⟨_, x, hx, hrx, hry⟩ := (trace r).mp hr
        exact ⟨hs, x, hx, (cf.value_l ht.1 ff hsr).mpr hrx, (cg.value_l ht.1 fg hsr).mpr hry⟩
      · obtain ⟨r, hr, hsr⟩ := ht.1.2.1 s hs
        exact ⟨hs, r, (trace r).mpr ⟨hr, x, hx, (cf.value_l ht.1 ff hsr).mp hsx, (cg.value_l ht.1 fg hsr).mp hsy⟩, hsr⟩
    exact (rp_eq_member_l hU hA trace).symm.trans (measure.symm.trans (rp_eq_member_l hV hB trace'))
  obtain ⟨j, hj, lift⟩ := rp_lift_exists_l I hZF hU.base hV.base model₀.map model₁.map hK kernel
  obtain ⟨Z, hZ⟩ := scode_exists_l I hZF hω
  obtain ⟨L, hL⟩ := ZF.exists_functionSpace hZF I ω Y
  refine ⟨K, j, hK, liftK, ⟨hj, Z, hZ, fun z w₀ w₁ hz hw₀ hw₁ hw => ?_⟩, lift⟩
  obtain ⟨a, ha, eval₀⟩ := rc_representatives_l hZFC source ext d fu hG₀ model₀ hw₀
  have repr := eval₀.repr_l I ha.1
  obtain ⟨b, hb, pull⟩ := rc_pull_assignment_l hZFC hω hm theory source hq ext d e p fp ha repr
  have eval₁ : Rc_eval_d I ω e.val Y S v p₁ b w₁ := by
    intro i hi
    obtain ⟨F, g, B, hiF, ff, graph, gp, hiB⟩ := eval₀ i hi
    obtain ⟨H, _, hiH⟩ := hb.2.2 i hi
    obtain ⟨g', hg', hgg⟩ := hK.2.2 g (model₀.map.projection.input_mem_of_pairMember gp)
    obtain ⟨C, _, gp'⟩ := model₁.map.projection.2.2 g' hg'
    have code := pull i F H hi hiF hiH
    exact ⟨H, g', C, hiH, code.1,
      graph.pull_l hZF fu fv ht.1 comm (model₀.map.functions g (hK.input_mem_of_pairMember hgg))
        code ((liftK g g').mp hgg).2.2, gp', hw i hi B C hiB (lift g g' B C hgg gp gp')⟩
  have point s r x y (hsr : Rd_entry_d s r t) (hsx : Rd_entry_d s x v) (hry : Rd_entry_d r y u) f :
      Pe_assign_d I ω d.val Y S a f y ↔ Pe_assign_d I ω e.val Y S b f x := by
    have xy := comm s r x y hsr hsx hry
    constructor
    · intro h i hi
      obtain ⟨F, z, hiF, _, val, hiz⟩ := h i hi
      obtain ⟨G, _, hiG⟩ := hb.2.2 i hi
      have code := pull i F G hi hiF hiG
      exact ⟨G, z, hiG, code.1, (code.2 x y z (val.bounds_l I).2.1 xy).mpr val, hiz⟩
    · intro h i hi
      obtain ⟨G, z, hiG, _, val, hiz⟩ := h i hi
      obtain ⟨F, _, hiF⟩ := ha.2.2 i hi
      exact ⟨F, z, hiF, repr i F hi hiF,
        ((pull i F G hi hiF hiG).2 x y z (val.bounds_l I).2.1 xy).mp val, hiz⟩
  obtain ⟨n, F, r, code⟩ := (hZ z).mp hz
  obtain ⟨A, hA, trace⟩ := rc_full_trace_l hZF hω source ext current d.property fu du hP hL code ((hL a).mpr ha) repr
  obtain ⟨B, hB, preimage, measure⟩ := ht.2 A hA
  have trace' s x (hsx : Rd_entry_d s x v) : M.mem s B ↔
      ∃ f, M.mem f L ∧ Pe_assign_d I ω e.val Y S b f x ∧ Satisfies_d I ω c' z f := by
    have hs := (fv.bound_l hsx).1
    obtain ⟨r, hr, hsr⟩ := ht.1.2.1 s hs
    obtain ⟨y, _, hry⟩ := fu.2.1 r hr
    apply (preimage s).trans
    refine ⟨fun ⟨_, r', hr', hsr'⟩ => ?_, fun ⟨f, hf, val, truth⟩ => ?_⟩
    · have eq := (fn0_function_l (ZF.modelsKP hZF) ht.1).1.2 s r' r hsr' hsr
      obtain ⟨f, hf, val, truth⟩ := (trace r y hry).mp (eq ▸ hr')
      exact ⟨f, hf, (point s r x y hsr hsx hry f).mp val, truth⟩
    · exact ⟨hs, r, (trace r y hry).mpr ⟨f, hf, (point s r x y hsr hsx hry f).mpr val, truth⟩, hsr⟩
  have truth {D P U A t : M.Domain} (hU : Rel_ultra_d D P U) (hA : M.mem A P) (ft : Fn0_d D Y t)
      (φ : M.Domain → Prop) (read : ∀ s x, Rd_entry_d s x t → (M.mem s A ↔ φ x)) :
      M.mem A U ↔ ∃ B, M.mem B U ∧ ∀ s x, M.mem s B → Rd_entry_d s x t → φ x := by
    refine ⟨fun h => ⟨A, h, fun s x hs hsx => (read s x hsx).mp hs⟩, fun ⟨B, hB, holds⟩ => ?_⟩
    apply hU.upward B A hB hA
    intro s hs
    obtain ⟨x, _, hsx⟩ := ft.2.1 s (hU.base.bounds B hB s hs)
    exact (read s x hsx).mpr (holds s x hs hsx)
  have los₀ := rc_satisfies_l hZF hω source ext current d uniform₀ fu du hP hU hG₀ model₀ hL hZ ((hL a).mpr ha) hw₀ eval₀ hz
  have los₁ := rc_satisfies_l hZF hω source ext current e uniform₁ fv dv hQ hV hG₁ model₁ hL hZ ((hL b).mpr hb) hw₁ eval₁ hz
  exact los₀.trans ((truth hU hA fu _ trace).symm.trans (measure.symm.trans ((truth hV hB fv _ trace').trans los₁.symm)))

end YesMetaZFC.SetTheory.Internal
