import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize

/-! # 原关系商及其初等像中的有限公式

有限参数先编成全部内部 Łoś 所用的同一赋值，再由实际坐标图读取。
源、商和目标均使用同一实际原关系，不另设字面根源。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_formula_image_l {ω c' Y S D t P U o G p C T b V W j : M.Domain}
    (hω : M.IsOmega ω) (source : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain) (uniform : Sc_uniform_d I ω Y S d.val)
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (hU : FilterZF.Rel_ultra_d D P U)
    (family : Rc_family_d I Y S D d.val t G) (model : Rp_model_d I D Y U S o G p C T)
    (target : Smdl_d I b V W) (hj : Smap_d I ω o b C V j)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (f g : Fin n → M.Domain)
    (hf : ∀ i, Rf_fun_d I Y S d.val (f i)) (hg : ∀ i, M.mem (g i) G)
    (decode : ∀ i, Rc_graph_d I Y S t (f i) (g i))
    (ρ : Env (smdl_structure_l I (R := W) target.2.1) n)
    (values : ∀ i, ∃ B, Rd_entry_d (g i) B p ∧ Rd_entry_d B (ρ.bound i).val j) :
    Formula.satisfies ρ φ ↔ ∃ A, M.mem A U ∧
      ∀ s, M.mem s A → ∀ η : Env (smdl_structure_l I (R := S) source.2.1) n,
        (∀ i, Rd_entry_d s (η.bound i).val (g i)) → Formula.satisfies η φ := by
  have en := ext.native_l I source.2.1
  have hG := (rc_family_native_l I source.2.1 en d ft).mp family
  obtain ⟨z, l, F, r, w, prog, hw, compile⟩ := source_compile_l I hZF hω φ hφ
  have hωw i := num_mem_l hZF.1 hω (hw i)
  have inj : Function.Injective w := fun i k h => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hw i) (h.symm ▸ hw k))
  let ε : Env M 3 := ⟨Fin.cases Y (Fin.cases S (fun _ => d.val)), fun _ => Y⟩
  let ψ : UnarySchema 3 := { body := rf_fun_m (𝒞 := kpair_convention_l) (.bound 1) (.bound 2) (.bound 3) .newest }
  obtain ⟨H, sep⟩ := ZF.separation_exists_d hZF ψ ε Y
  have codes a : M.mem a H ↔ M.mem a Y ∧ Rf_fun_d I Y S d.val a :=
    (sep a).trans (and_congr Iff.rfl (rf_fun_sat_l I ..))
  obtain ⟨B₀, hB₀⟩ := model.code.2.1
  obtain ⟨g₀, hg₀⟩ := (model.map.range B₀).mp hB₀
  obtain ⟨_, f₀, ff₀, _⟩ := (family g₀).mp (model.map.projection.input_mem_of_pairMember hg₀)
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω H
  obtain ⟨a, ha₀, params⟩ := senv_params_l I hZF hE₀ ⟨f₀, (codes f₀).mpr ⟨ff₀.mem_l I, ff₀⟩⟩
    w f inj hωw (fun i => (codes (f i)).mpr ⟨(hf i).mem_l I, hf i⟩)
  have fa₀ := (hE₀ a).mp ha₀
  have fa : M.IsSetFunctionFromTo I a ω Y := ⟨fa₀.1, fa₀.2.1, fun i hi =>
    (fa₀.2.2 i hi).imp fun f hf => ⟨((codes f).mp hf.1).1, hf.2⟩⟩
  have repr : Pe_repr_d I ω d.val Y S a := fun _ f _ h => ((codes f).mp (fa₀.output_mem_of_pairMember h)).2
  obtain ⟨v, hv, eval⟩ := rc_eval_exists_l hZF source.2.1 en d ft domain family model.map.projection fa repr
  obtain ⟨v', hv', transport⟩ := smap_assign_exists_l I hZF hj.1.1 hv
  obtain ⟨E', hE'⟩ := ZF.exists_functionSpace hZF I ω V
  have out i : Rd_entry_d (w i) (ρ.bound i).val v' := by
    obtain ⟨f', g', B, hif, _, gr, gp, hiB⟩ := eval (w i) (hωw i)
    have ef := fa.1.2 (w i) f' (f i) hif (params i)
    have eg := gr.unique_l I hZF.1 ft (model.map.functions g' (model.map.projection.input_mem_of_pairMember gp))
      (model.map.functions (g i) (hg i)) (ef.symm ▸ decode i)
    obtain ⟨B', hgB, hBj⟩ := values i
    have eB := model.map.projection.1.2 (g i) B B' (eg ▸ gp) hgB
    exact transport (w i) (hωw i) B' (ρ.bound i).val (eB ▸ hiB) hBj
  have decoded := (satisfies_decode_l I hZF.1 target prog hE').trans
    (compile V W target.2.1 E' hE' v' ((hE' v').mpr hv') ρ out)
  obtain ⟨Z, hZ, elementary⟩ := hj.2
  have hz := (hZ z).mpr ⟨l, F, r, prog⟩
  have mapped := elementary z v v' hz hv hv' transport
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω Y
  have ha := (hE a).mpr fa
  have los := rc_satisfies_l hZF hω source ext theory
    d uniform ft domain hP hU hG model hE hZ ha hv eval hz
  have point e (he : M.mem e E) s x (hsx : Rd_entry_d s x t) (assign : Pe_assign_d I ω d.val Y S a e x)
      (η : Env (smdl_structure_l I (R := S) source.2.1) n)
      (hη : ∀ i, Rd_entry_d s (η.bound i).val (g i)) :
      Satisfies_d I ω c' z e ↔ Formula.satisfies η φ :=
    (satisfies_decode_l I hZF.1 source prog hE).trans (compile Y S source.2.1 E hE e he η
      (fun i => (assign.value_l I ext fa.1 ((hE e).mp he).1 (hωw i) (params i)).mpr
        ((decode i s x (η.bound i).val hsx).mp (hη i))))
  refine (mapped.trans decoded).symm.trans (los.trans ⟨?_, ?_⟩)
  · rintro ⟨A, hA, holds⟩
    refine ⟨A, hA, fun s hs η hη => ?_⟩
    obtain ⟨x, _, hsx⟩ := ft.2.1 s (hU.base.bounds A hA s hs)
    obtain ⟨e, he, assign, truth⟩ := holds s x hs hsx
    exact (point e he s x hsx assign η hη).mp truth
  · rintro ⟨A, hA, holds⟩
    refine ⟨A, hA, fun s x hs hsx => ?_⟩
    obtain ⟨e, he, assign⟩ := pe_value_exists_l I hZF ext hE ha (fun _ h => h)
      (ft.bound_l hsx).2 (domain s x hsx) repr
    -- 有限参数逐项提取；无穷赋值始终由背景的唯一值替换构造。
    have pick : ∀ {k} (v : Fin k → M.Domain), (∀ i, ∃ y, Rd_entry_d (v i) y e) →
        ∃ b : Fin k → M.Domain, ∀ i, Rd_entry_d (v i) (b i) e := by
      intro k
      induction k with
      | zero => exact fun _ _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      | succ k ih =>
        intro v total
        obtain ⟨y, hy⟩ := total 0
        obtain ⟨b, hb⟩ := ih (fun i => v i.succ) (fun i => total i.succ)
        exact ⟨Fin.cases y b, Fin.cases hy hb⟩
    obtain ⟨b, hwb⟩ := pick w (fun i => (((hE e).mp he).2.2 (w i) (hωw i)).imp fun _ h => h.2)
    let η : Env (smdl_structure_l I (R := S) source.2.1) n :=
      ⟨fun i => ⟨b i, ((hE e).mp he).output_mem_of_pairMember (hwb i)⟩, fun _ => d⟩
    have hη i : Rd_entry_d s (η.bound i).val (g i) := (decode i s x (η.bound i).val hsx).mpr
      ((assign.value_l I ext fa.1 ((hE e).mp he).1 (hωw i) (params i)).mp (hwb i))
    exact ⟨e, he, assign, (point e he s x hsx assign η hη).mpr (holds s hs η hη)⟩

end YesMetaZFC.SetTheory.Internal
