import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSatisfaction

/-! # 源内部超幂的常值初等嵌入

先收集每个源对象的唯一常值图，再与实际商投影复合。源内部 Łoś 把常值
赋值的逐点真值还原为原真值，得到覆盖全部内部代码的 Smap 证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Rs_const_d (D x f : M.Domain) : Prop := ∀ v, M.mem v D → Rd_entry_d v x f

def rs_const_m {d} (D x f : Term d) : Formula 1 d :=
  Formula.forallMem D (rd_entry0_m .newest x.weaken f.weaken)
derive_free_closed rs_const_m

theorem rs_const_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D x f : Term d) :
    Formula.satisfies ρ (rs_const_m D x f) ↔ Rs_const_d (D.eval ρ) (x.eval ρ) (f.eval ρ) := by
  simp only [rs_const_m, Rs_const_d, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem rs_const_unique_l (hE : Extensional M) {D X Y x f g : M.Domain}
    (hf : Fn0_d D X f) (hg : Fn0_d D Y g) (h : Rs_const_d D x f) (k : Rs_const_d D x g) : f = g :=
  hf.ext_l hE hg (fun v hv => ⟨x, h v hv, k v hv⟩)

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_constants_l {ω χ c d X R H S q D G} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hn : Smem_d I d H S) (hq : Smap_d I ω c d X H q) (hD : M.mem D X)
    (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g) : ∃ K, M.IsSetFunctionFromTo I K X G ∧
      ∀ x f, M.PairMember I x f K ↔ M.mem x X ∧ M.mem f G ∧ Rs_const_d D x f := by
  let ρ : Env M 2 := ⟨Fin.cases G (fun _ => D), fun _ => D⟩
  let φ : BinarySchema 2 := { body := .conj (.mem .newest (.bound 2)) (rs_const_m (.bound 3) (.bound 1) .newest) }
  have sat x f : φ.denote ρ x f ↔ M.mem f G ∧ Rs_const_d D x f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rs_const_sat_l hZF.1]
    rfl
  obtain ⟨K, hK, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := X) (target := G)
    (fun x hx => by
      obtain ⟨f, C, hf, hC, hFC, hc⟩ := smap_constant_l hZFC hω hχ hωχ hH hX hm hn hq hD hx
      exact ⟨f, (sat x f).mpr ⟨(hG f).mpr ⟨hf, hFC.mono_target_l (hX C hC)⟩,
        fun v hv => (hc v x).mpr ⟨hv, rfl⟩⟩⟩)
    (fun x _ f g hf hg => rs_const_unique_l hZF.1 ((hG f).mp ((sat x f).mp hf).1).2
      ((hG g).mp ((sat x g).mp hg).1).2 ((sat x f).mp hf).2 ((sat x g).mp hg).2)
    (fun x f _ hf => ((sat x f).mp hf).1)
  exact ⟨K, hK, fun x f => (spec x f).trans (and_congr_right fun _ => sat x f)⟩

theorem rs_constant_embedding_l {ω χ c d X R H S q D P U o G p C T}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ)
    (hH : H_d I χ H) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S)
    (hq : Smap_d I ω c d X H q) (hD : M.mem D X) (hP : FilterZF.Source_d X D P)
    (hU : FilterZF.Rel_ultra_d D P U) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g)
    (hM : Rp_model_d I D X U R o G p C T) : ∃ j, Smap_d I ω c o X C j ∧
      ∀ x B, M.PairMember I x B j ↔ M.mem x X ∧ ∃ f, M.mem f G ∧ Rs_const_d D x f ∧ M.PairMember I f B p := by
  obtain ⟨K, hK, hc⟩ := rs_constants_l hZFC hω hχ hωχ hH hX hm hn hq hD hG
  obtain ⟨j, hj, spec⟩ := ZF.exists_compositionFunction hZF I hK hM.map.projection
  have value x f (hf : M.PairMember I x f K) := ((hc x f).mp hf).2.2
  have inj : M.IsSetInjectionFromTo I j X C := ⟨hj, fun x y B hx hy => by
    obtain ⟨_, f, hxf, hf⟩ := (spec x B).mp hx
    obtain ⟨_, g, hyg, hg⟩ := (spec y B).mp hy
    obtain ⟨A, hA, he⟩ := (rp_kernel_l I hZF.1 hU.base hM.map hf hg).mp rfl
    obtain ⟨v, hv⟩ := hU.proper A hA
    obtain ⟨z, _, hvf, hvg⟩ := he v hv
    have hvD := hU.base.bounds A hA v hv
    have ex := (fn0_function_l (ZF.modelsKP hZF) (hM.map.functions f (hK.output_mem_of_pairMember hxf))).1.2
      v x z (value x f hxf v hvD) hvf
    have ey := (fn0_function_l (ZF.modelsKP hZF) (hM.map.functions g (hK.output_mem_of_pairMember hyg))).1.2
      v y z (value y g hyg v hvD) hvg
    exact ex.trans ey.symm⟩
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine ⟨j, ⟨inj, A, hA, fun z f e hz hf he hfe => ?_⟩, fun x B => (spec x B).trans (and_congr_right fun hx => ?_)⟩
  · obtain ⟨a, ha, hfa⟩ := ZF.exists_compositionFunction hZF I hf hK
    have haX : M.IsSetFunctionFromTo I a ω X := ⟨ha.1, ha.2.1, fun i hi =>
      (ha.2.2 i hi).imp fun g hg => ⟨((hG g).mp hg.1).1, hg.2⟩⟩
    have sfun g (hg : M.mem g G) := smap_function_domain_l hZFC hω hχ hωχ hH hX hm hn hq hD
      ((hG g).mp hg).1 ((hG g).mp hg).2
    have eval : Rs_eval_d I ω D X p a e := by
      intro i hi
      obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
      obtain ⟨g, hg, hxg⟩ := hK.2.2 x hx
      obtain ⟨B, _, hgp⟩ := hM.map.projection.2.2 g hg
      exact ⟨g, B, (hfa i g).mpr ⟨hi, x, hix, hxg⟩, sfun g hg, hgp,
        hfe i hi x B hix ((spec x B).mpr ⟨hx, g, hxg, hgp⟩)⟩
    have point v (hv : M.mem v D) : Pe_assign_d I ω D X a f v := by
      intro i hi
      obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
      obtain ⟨g, hg, hxg⟩ := hK.2.2 x hx
      exact ⟨g, x, (hfa i g).mpr ⟨hi, x, hix, hxg⟩, sfun g hg, value x g hxg v hv, hix⟩
    have los := rs_satisfies_l hZFC hω hχ hωχ hH hX hm hn hq hD hP hU hG hM hE hA ((hE a).mpr haX) he eval hz
    refine ⟨fun hs => los.mpr ⟨D, hU.base.top, fun v hv => ⟨f, (hE f).mpr hf, point v hv, hs⟩⟩, fun hs => ?_⟩
    obtain ⟨B, hB, hb⟩ := los.mp hs
    obtain ⟨v, hv⟩ := hU.proper B hB
    obtain ⟨g, hg, hval, hs⟩ := hb v hv
    have agree := hval.agree_right_l I (point v (hU.base.bounds B hB v hv)) haX.1 ((hE g).mp hg).1 hf.1
    have eq : g = f := ((hE g).mp hg).1.1.eq_of_pairMember_iff hZF.1 hf.1.1
      (fun i x => ⟨fun h => (agree i x (((hE g).mp hg).input_mem_of_pairMember h)).mp h,
        fun h => (agree i x (hf.input_mem_of_pairMember h)).mpr h⟩)
    exact eq ▸ hs
  · exact ⟨fun ⟨f, hxf, hfp⟩ => ⟨f, ((hc x f).mp hxf).2.1, value x f hxf, hfp⟩,
      fun ⟨f, hf, hconst, hfp⟩ => ⟨f, (hc x f).mpr ⟨hx, hf, hconst⟩, hfp⟩⟩

end YesMetaZFC.SetTheory.Internal
