import YesMetaZFC.SetTheory.LargeCardinal.ExtenderMatrixValue
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetValue
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Restriction

/-! # 拥有集合之像中的完整分量嵌入

对每个内部公式，仅收集其有限个代表。源内转置矩阵的超幂值是目标赋值，
整张有限真值表把 j(A) 中的真值还原为 A 中的逐点真值，再调用原源的 Łoś。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_component_l {ω κ K L X R F J O Z A p T V q c C W d N S μ K' e i j c₀
    a₀ A₀ R₀ a₁ A₁ R₁ K₀ n D a U o G p₀ C₀ T₀ k : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' N S)
    (small : Ep_source_d hZF ω κ K₀ A₀ R₀)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hm : Smem_d I c₀ X R) (hn : Smem_d I d N S)
    (he : Smap_d I ω c d C N e) (hj : Smap_d I ω c₀ d X N j)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (h₀ : Smem_d I a₀ A₀ R₀) (h₁ : Smem_d I a₁ A₁ R₁) (hA : Rd_entry_d A₀ A₁ j)
    (cover : Ea_subset_d ω κ X A₀) (hnω : M.mem n ω) (haJ : M.mem a J)
    (ha : Fn0_d n L a) (space : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    (hG : ∀ f, M.mem f G ↔ M.mem f A₀ ∧ Fn0_d D A₀ f)
    (component : Rp_model_d I D A₀ U R₀ o G p₀ C₀ T₀) (hk : M.IsSetInjectionFromTo I k C₀ A₁)
    (values : ∀ f B x, Rd_entry_d f B p₀ → Rd_entry_d B x k → Ep_value_d q e a f x) :
    Smap_d I ω o a₁ C₀ A₁ k := by
  have inside := source.transitive A₀ (hj.1.1.input_mem_of_pairMember hA)
  have sub := target.transitive A₁ (hj.1.1.output_mem_of_pairMember hA)
  have ultra := (family.at_l hZF.1 haU ha space).transfer_l
    (fun B hB => ⟨cover n D B hnω space hB, inside B⟩)
  obtain ⟨P, U₀, hp, hu, us, cmp⟩ := rs_restrict_model_l hZF small.omega small.transitive h₀ small.theory
    (small.space_mem_l hZF hnω space) ultra hG component
  obtain ⟨Codes, codes⟩ := scode_exists_l I hZF source.omega
  obtain ⟨Eω, hEω⟩ := ZF.exists_functionSpace hZF I ω A₀
  obtain ⟨Qω, hQω⟩ := ZF.exists_functionSpace hZF I ω C₀
  obtain ⟨Tω, hTω⟩ := ZF.exists_functionSpace hZF I ω A₁
  refine ⟨hk, Codes, codes, fun z u v hz fu fv assign => ?_⟩
  obtain ⟨l, F₀, r, code⟩ := (codes z).mp hz
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF source.omega code.2.1
  have bω := source.omega.transitive hZF b hb
  obtain ⟨g, fg, eval⟩ := rp_representatives_l I hZFC component.map fu
  have fg₀ : M.IsSetFunctionFromTo I g ω A₀ := ⟨fg.1, fg.2.1, fun m hm =>
    (fg.2.2 m hm).imp fun f hf => ⟨((hG f).mp hf.1).1, hf.2⟩⟩
  have sf f (hf : M.mem f G) := small.function_l hZF ((hG f).mp hf).1 ((hG f).mp hf).2
  have evaluation : Rs_eval_d I ω D A₀ p₀ g u := by
    intro m hm
    obtain ⟨f, hf, hmf⟩ := fg.2.2 m hm
    obtain ⟨B, _, hfB⟩ := component.map.projection.2.2 f hf
    exact ⟨f, B, hmf, sf f hf, hfB, eval m hm f B hmf hfB⟩
  -- 只转置程序实际读取的有限代表；量词的全部赋值仍由原真值表解释。
  obtain ⟨g₀, gr⟩ := ZF.exists_restriction hZF I g b
  obtain ⟨v₀, vr⟩ := ZF.exists_restriction hZF I v b
  have fg₁ := fn0_of_function_l (ZF.modelsKP hZF) (gr.isSetFunctionFromTo fg₀ bω)
  have fv₁ := fn0_of_function_l (ZF.modelsKP hZF) (vr.isSetFunctionFromTo fv bω)
  obtain ⟨B, E₀, H, hB, hE₀, hH, hE, fH, matrix⟩ := small.matrix_l hZF hb (small.space_mem_l hZF hnω space)
    fg₁ (fun m f hmf => ((hG f).mp (fg.output_mem_of_pairMember ((gr.2 m f).mp hmf).2)).2)
  have mv := ep_matrix_value_l hZFC source family coherent system limit model target.transitive hn he haJ ha space
    hb (inside B hB) (inside E₀ hE₀) (inside H hH) hE fH (fg₁.mono_target_l inside) (fv₁.mono_target_l sub) matrix (by
      intro m f x hmf hmx
      have hmf' := ((gr.2 m f).mp hmf).2
      obtain ⟨B, hBC, hfB⟩ := component.map.projection.2.2 f (fg.output_mem_of_pairMember hmf')
      obtain ⟨y, _, hBy⟩ := hk.1.2.2 B hBC
      have eq := fv.1.2 m y x (assign m (bω m (fg₁.bound_l hmf).1) B y
        (eval m (bω m (fg₁.bound_l hmf).1) f B hmf' hfB) hBy) ((vr.2 m x).mp hmx).2
      exact eq ▸ values f B y hfB hBy)
  obtain ⟨E, E', hs, ht, truth⟩ := ep_set_value_l hZFC source target family coherent system limit model hm hn he hj
    constants comp h₀ h₁ hA hnω haJ ha space haU code.2.1 hb bound code.2.2 mv
  have point s t (hsD : M.mem s D) (hst : Rd_entry_d s t H) :
      Pe_sat_d I b D A₀ R₀ Eω F₀ l r g s ↔ Ssat_d I A₀ R₀ E F₀ l r t := by
    obtain ⟨w, hw, pw⟩ := pe_value_exists_l I hZF small.transitive hEω ((hEω g).mpr fg₀) bω hsD h₀.1.2.1
      (fun m f hm => evaluation.repr_l I fg.1 m f (bω m hm))
    have ft := (fn0_of_function_l (ZF.modelsKP hZF) ((hE t).mp (fH.bound_l hst).2)).mono_target_l (small.transitive B hB)
    have same : Senv_agree_d I b w t := by
      intro m x hm
      obtain ⟨f, _, hmf⟩ := fg₁.2.1 m hm
      exact (pw.value_l I fg.1 ((hEω w).mp hw).1 hm ((gr.2 m f).mp hmf).2).trans (matrix s t m f x hst hmf).symm
    exact (pe_sat_value_l I hZF code.2.1 bound code.2.2 hEω ((hEω g).mpr fg₀) hw pw).trans
      (ssat_spaces_l I hZF code.2.1 bound hEω hs bω (fun _ h => h) code.2.2 hw
        ((hs t).mpr (fn0_function_l (ZF.modelsKP hZF) ft)) same)
  have measure : Pe_holds_d I b D A₀ R₀ Eω F₀ l r U₀ g ↔ Ssat_d I A₁ R₁ E' F₀ l r v₀ := by
    -- 大源中的测度一见证由有限 κ 幂子集包含回到小源，再读取同一个限制测度。
    rw [truth]
    constructor
    · rintro ⟨B, hBU, all⟩
      have hBP := ((us B).mp hBU).1
      exact ⟨B, inside B ((hp B).mp hBP).1, ((us B).mp hBU).2, ((hp B).mp hBP).2,
        fun s hs t hst => (point s t (((hp B).mp hBP).2 s hs) hst).mp (all s hs)⟩
    · rintro ⟨B, hBX, hBU, hBD, all⟩
      refine ⟨B, (us B).mpr ⟨(hp B).mpr ⟨cover n D B hnω space hBD hBX, hBD⟩, hBU⟩, fun s hs => ?_⟩
      obtain ⟨t, _, hst⟩ := fH.2.1 s (hBD s hs)
      exact (point s t (hBD s hs) hst).mpr (all s hs t hst)
  have old := rs_los_l hZF small.omega small.transitive h₀ small.theory (small.uniform_l hZF hnω space)
    (small.space_mem_l hZF hnω space) hp hu hG cmp hEω hQω code.2.1 hb bound code.2.2 g u
    ((hEω g).mpr fg₀) ((hQω u).mpr fu) (fun m hm => evaluation m (bω m hm))
  have last := ssat_spaces_l I hZF (R := R₁) code.2.1 bound hTω ht bω (fun _ h => h) code.2.2
    ((hTω v).mpr fv) ((ht v₀).mpr (fn0_function_l (ZF.modelsKP hZF) fv₁))
    (fun m x hm => ((vr.2 m x).trans (and_iff_right hm)).symm)
  exact (satisfies_decode_l I hZF.1 component.code code hQω).trans
    (old.symm.trans (measure.trans (last.symm.trans (satisfies_decode_l I hZF.1 h₁.1 code hTω).symm)))

end YesMetaZFC.SetTheory.LargeCardinal
