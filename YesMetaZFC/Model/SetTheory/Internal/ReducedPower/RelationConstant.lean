import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationLos
import YesMetaZFC.Model.SetTheory.Internal.RelationFunction
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Constant

/-! # 原关系后继的实际常值初等图

先统一原关系内部的唯一常值函数码，再读出其实际坐标图。完整内部 Łoś
给出常值嵌入，故后继可继续搬运源理论而无须整体传递塌缩。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Rf_const_d (Y S d x f : M.Domain) : Prop := Rf_fun_d I Y S d f ∧
  ∀ v, M.mem v Y → Rd_entry_d v d S → Rf_val_d I Y S v x f

def rf_const_m {n} (Y S d x f : Term n) : Formula 1 n :=
  .conj (rf_fun_m (𝒞 := kpair_convention_l) Y S d f) (Formula.forallMem Y
    (.imp (rd_entry0_m .newest d.weaken S.weaken)
      (rf_val_m (𝒞 := kpair_convention_l) Y.weaken S.weaken .newest x.weaken f.weaken)))
derive_free_closed rf_const_m

theorem rf_const_sat_l {n} (ρ : Env M n) (Y S d x f : Term n) :
    Formula.satisfies ρ (rf_const_m Y S d x f) ↔
      Rf_const_d hZF (Y.eval ρ) (S.eval ρ) (d.eval ρ) (x.eval ρ) (f.eval ρ) := by
  simp only [rf_const_m, Rf_const_d, Formula.satisfies_conj_iff, rf_fun_sat_l I,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hZF.1,
    rf_val_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem rc_code_constants_l {ω c Y S d E : M.Domain} (context : Pe_context_d I ω c Y S d E) :
    ∃ K, M.IsSetFunctionFromTo I K Y Y ∧
      ∀ x f, Rd_entry_d x f K ↔ M.mem x Y ∧ Rf_const_d hZF Y S d x f := by
  have en := context.1.native_l I context.2.1.2.1
  have hd := context.2.2.2.1
  let ρ : Env M 3 := ⟨Fin.cases d (Fin.cases S (fun _ => Y)), fun _ => d⟩
  let φ : BinarySchema 3 := { body := rf_const_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have read x f : φ.denote ρ x f ↔ Rf_const_d hZF Y S d x f := rf_const_sat_l hZF ..
  obtain ⟨K, fn, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := Y)
    (fun x hx => (context.2.2.2.2 x hx).imp fun f hf => (read x f).mpr hf)
    (fun x hx f g hf hg => by
      obtain ⟨ff, fc⟩ := (read x f).mp hf
      obtain ⟨fg, gc⟩ := (read x g).mp hg
      obtain ⟨B, fb⟩ := (rf_fun_native_l I context.2.1.2.1 en ⟨d, hd⟩ ⟨f, ff.mem_l I⟩).mp ff
      obtain ⟨C, gb⟩ := (rf_fun_native_l I context.2.1.2.1 en ⟨d, hd⟩ ⟨g, fg.mem_l I⟩).mp fg
      exact congrArg Subtype.val (fb.ext_l en gb (fun v hv => ⟨⟨x, hx⟩,
        (rf_val_native_l I context.2.1.2.1 en v ⟨x, hx⟩ ⟨f, ff.mem_l I⟩).mp (fc v.val v.property hv),
        (rf_val_native_l I context.2.1.2.1 en v ⟨x, hx⟩ ⟨g, fg.mem_l I⟩).mp (gc v.val v.property hv)⟩)))
    (fun x f _ hf => ((read x f).mp hf).1.mem_l I)
  exact ⟨K, fn, fun x f => (spec x f).trans (and_congr_right fun _ => read x f)⟩

theorem rc_constant_embedding_l {ω c X R c' Y S q D t P U o G p C T : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d μ e : (smdl_structure_l I (R := S) source.2.1).Domain)
    (small : Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ :
      Env (smdl_structure_l I (R := S) source.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)))
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : Rel_ultra_d D P U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T) :
    ∃ j, Smap_d I ω c' o Y C j ∧ ∀ x B, Rd_entry_d x B j ↔
      M.mem x Y ∧ ∃ f, M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B p := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω Y
  have context := hq.pe_context_l hZF hω hX hm theory source d.property hE
  have ext := context.1
  have en := ext.native_l I source.2.1
  obtain ⟨K, hK, codes⟩ := rc_code_constants_l hZF context
  let ρ : Env M 2 := ⟨Fin.cases G (fun _ => D), fun _ => D⟩
  let φ : BinarySchema 2 := { body := .conj (.mem .newest (.bound 2)) (rs_const_m (.bound 3) (.bound 1) .newest) }
  have read x f : φ.denote ρ x f ↔ M.mem f G ∧ Rs_const_d D x f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rs_const_sat_l hZF.1]; rfl
  obtain ⟨L, hL, constants⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := G)
    (fun x hx => by
      obtain ⟨f, hf, hxf⟩ := hK.2.2 x hx
      obtain ⟨ff, fc⟩ := ((codes x f).mp hxf).2
      obtain ⟨B, fb⟩ := (rf_fun_native_l I source.2.1 en d ⟨f, hf⟩).mp ff
      obtain ⟨g, fg, decode⟩ := smdl_function_l hZF source ext d B ⟨f, hf⟩ fb ft domain
      refine ⟨g, (read x g).mpr ⟨(hG g).mpr ⟨fg, B, ⟨f, hf⟩, fb, decode⟩, fun s hs => ?_⟩⟩
      obtain ⟨v, hv, hsv⟩ := ft.2.1 s hs
      exact (decode s ⟨v, hv⟩ ⟨x, hx⟩ hsv).mpr
        ((rf_val_native_l I source.2.1 en ⟨v, hv⟩ ⟨x, hx⟩ ⟨f, hf⟩).mp (fc v hv (domain s v hsv))))
    (fun x _ f g hf hg => rs_const_unique_l hZF.1 (model.map.functions f ((read x f).mp hf).1)
      (model.map.functions g ((read x g).mp hg).1) ((read x f).mp hf).2 ((read x g).mp hg).2)
    (fun x f _ hf => ((read x f).mp hf).1)
  have constant x f (h : Rd_entry_d x f L) := ((read x f).mp ((constants x f).mp h).2).2
  have decode x F g (hf : Rf_const_d hZF Y S d.val x F) (hg : Rd_entry_d x g L) :
      Rc_graph_d I Y S t F g := by
    intro s v y hsv
    have hs := (ft.bound_l hsv).1
    have vc := hf.2 v (ft.bound_l hsv).2 (domain s v hsv)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have eq := (fn0_function_l (ZF.modelsKP hZF) (model.map.functions g (hL.output_mem_of_pairMember hg))).1.2
        s y x h (constant x g hg s hs)
      exact eq.symm ▸ vc
    · exact (hf.1.unique_l I ext h vc).symm ▸ constant x g hg s hs
  obtain ⟨j, hj, composition⟩ := ZF.exists_compositionFunction hZF I hL model.map.projection
  have inj : M.IsSetInjectionFromTo I j Y C := ⟨hj, fun x y B hx hy => by
    obtain ⟨_, f, hxf, hf⟩ := (composition x B).mp hx
    obtain ⟨_, g, hyg, hg⟩ := (composition y B).mp hy
    obtain ⟨A, hA, equal⟩ := (rp_kernel_l I hZF.1 hU.base model.map hf hg).mp rfl
    obtain ⟨s, hs⟩ := hU.proper A hA
    obtain ⟨z, _, hszf, hszg⟩ := equal s hs
    have hsD := hU.base.bounds A hA s hs
    have ex := (fn0_function_l (ZF.modelsKP hZF) (model.map.functions f (hL.output_mem_of_pairMember hxf))).1.2
      s x z (constant x f hxf s hsD) hszf
    have ey := (fn0_function_l (ZF.modelsKP hZF) (model.map.functions g (hL.output_mem_of_pairMember hyg))).1.2
      s y z (constant y g hyg s hsD) hszg
    exact ex.trans ey.symm⟩
  obtain ⟨Z, hZ⟩ := scode_exists_l I hZF hω
  refine ⟨j, ⟨inj, Z, hZ, fun z f v hz hf hv hfv => ?_⟩, fun x B =>
    (composition x B).trans (and_congr_right fun hx => ?_)⟩
  · obtain ⟨a, ha, assign⟩ := ZF.exists_compositionFunction hZF I hf hK
    have eval : Rc_eval_d I ω d.val Y S t p a v := by
      intro i hi
      obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
      obtain ⟨F, _, hxF⟩ := hK.2.2 x hx
      obtain ⟨g, hg, hxg⟩ := hL.2.2 x hx
      obtain ⟨B, _, hgB⟩ := model.map.projection.2.2 g hg
      have code := ((codes x F).mp hxF).2
      exact ⟨F, g, B, (assign i F).mpr ⟨hi, x, hix, hxF⟩, code.1, decode x F g code hxg, hgB,
        hfv i hi x B hix ((composition x B).mpr ⟨hx, g, hxg, hgB⟩)⟩
    have point x (hx : M.mem x Y) (hxd : Rd_entry_d x d.val S) : Pe_assign_d I ω d.val Y S a f x := by
      intro i hi
      obtain ⟨y, hy, hiy⟩ := hf.2.2 i hi
      obtain ⟨F, _, hyF⟩ := hK.2.2 y hy
      have code := ((codes y F).mp hyF).2
      exact ⟨F, y, (assign i F).mpr ⟨hi, y, hiy, hyF⟩, code.1, code.2 x hx hxd, hiy⟩
    have los := rc_satisfies_l hZF hω hX hm theory collection source hq d μ e small ft domain hP hU hG model
      hE hZ ((hE a).mpr ha) hv eval hz
    refine ⟨fun truth => los.mpr ⟨D, hU.base.top, fun s x _ hsx =>
      ⟨f, (hE f).mpr hf, point x (ft.bound_l hsx).2 (domain s x hsx), truth⟩⟩, fun truth => ?_⟩
    obtain ⟨A, hA, truth⟩ := los.mp truth
    obtain ⟨s, hs⟩ := hU.proper A hA
    obtain ⟨x, hx, hsx⟩ := ft.2.1 s (hU.base.bounds A hA s hs)
    obtain ⟨g, hg, val, truth⟩ := truth s x hs hsx
    have agree := val.agree_right_l I (point x hx (domain s x hsx)) ext ha.1 ((hE g).mp hg).1 hf.1
    have eq : g = f := ((hE g).mp hg).1.1.eq_of_pairMember_iff hZF.1 hf.1.1
      (fun i x => ⟨fun h => (agree i x (((hE g).mp hg).input_mem_of_pairMember h)).mp h,
        fun h => (agree i x (hf.input_mem_of_pairMember h)).mpr h⟩)
    exact eq ▸ truth
  · exact ⟨fun ⟨f, hxf, hfp⟩ => ⟨f, hL.output_mem_of_pairMember hxf, constant x f hxf, hfp⟩,
      fun ⟨f, hf, hc, hfp⟩ => ⟨f, (constants x f).mpr ⟨hx, (read x f).mpr ⟨hf, hc⟩⟩, hfp⟩⟩

end YesMetaZFC.SetTheory.Internal
