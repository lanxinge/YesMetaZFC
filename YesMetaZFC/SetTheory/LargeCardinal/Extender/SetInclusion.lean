import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Value
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingSetImage
import YesMetaZFC.SetTheory.LargeCardinal.Extender.ValueApply
import YesMetaZFC.Model.SetTheory.ReducedPower.Restriction
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.DirectedSystem.ElementaryFactor

/-! # 有限转置矩阵的超幂值

矩阵逐点编码有限代表列，其坍塌值便是这些代表值组成的有限赋值。
有界 Łoś 先给出函数图，再逐坐标辨认；输入矩阵可来自更小的实际源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_matrix_value_l {ω κ K L X R F J O Z A p T V q c C W d N S e n D a b B E H G t : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hN : M.TransitiveSet N) (target : Smem_d I d N S) (he : Smap_d I ω c d C N e)
    (haJ : M.mem a J) (ha : Fn0_d n L a) (space : Ep_space_d κ n D)
    (hb : M.mem b ω) (hB : M.mem B X) (hE : M.mem E X) (hH : M.mem H X)
    (assignments : M.IsFunctionSpace I E b B) (fh : Fn0_d D E H) (fg : Fn0_d b X G) (ft : Fn0_d b N t)
    (matrix : ∀ v s i f x, Rd_entry_d v s H → Rd_entry_d i f G → (Rd_entry_d i x s ↔ Rd_entry_d v x f))
    (values : ∀ i f x, Rd_entry_d i f G → Rd_entry_d i x t → Ep_value_d q e a f x) : Ep_value_d q e a H t := by
  obtain ⟨E₀, hE₀, rep⟩ := ep_repr_exists_l hZF family system limit haJ ha space hH
    (fh.mono_target_l (source.transitive E hE))
  obtain ⟨s, _, hEs⟩ := he.1.1.2.2 E₀ hE₀
  have value : Ep_value_d q e a H s := ⟨E₀, rep, hEs⟩
  obtain ⟨c₀, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent system limit model he haJ ha space
  have natural := hj.natural_l hZF source.omega source.transitive hN code target source.omega_mem
  obtain ⟨kb, _, fb, bc, bv⟩ := constants b b (natural b hb)
  obtain ⟨B', hB', hBB⟩ := hj.1.1.2.2 B hB
  obtain ⟨kB, _, fB, Bc, Bv⟩ := constants B B' hBB
  obtain ⟨_, n', hn, ha', _⟩ := rep.source_l hZF family system limit
  have en := ha'.domain_eq_l hZF.1 ha
  subst n'
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have fs : Fn0_d b B' s := by
    have los := ep_delta_value_l hZFC source family coherent system limit model hN target he haJ ha space haU (k := 3)
      (fn0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (fn0_delta_l ..)
      (Fin.cases H (Fin.cases kB (fun _ => kb)))
      ⟨Fin.cases s (Fin.cases B' (fun _ => b)), fun _ => b⟩ (Fin.cases value (Fin.cases Bv (fun _ => bv)))
    apply (fn0_sat_l hZF.1 ..).mp (los.mpr ⟨D, source.space_mem_l hZF hn space,
      (family.at_l hZF.1 haU ha space).base.top, fun _ h => h, ?_⟩)
    intro v hv η entries
    have eb := (fn0_function_l (ZF.modelsKP hZF) fb).1.2 v (η.bound 2) b (entries 2) (bc v hv)
    have eB := (fn0_function_l (ZF.modelsKP hZF) fB).1.2 v (η.bound 1) B (entries 1) (Bc v hv)
    apply (fn0_sat_l hZF.1 ..).mpr
    change Fn0_d (η.bound 2) (η.bound 1) (η.bound 0)
    rw [eb, eB]
    exact fn0_of_function_l (ZF.modelsKP hZF) ((assignments _).mp (fh.bound_l (entries 0)).2)
  have eq := (fs.mono_target_l (hN B' hB')).ext_l hZF.1 ft (fun i hi => by
    obtain ⟨f, _, hif⟩ := fg.2.1 i hi
    obtain ⟨x, _, hix⟩ := ft.2.1 i hi
    obtain ⟨ki, _, fi, ic, iv⟩ := constants i i (natural i (source.omega.transitive (ZF.modelsKP hZF) b hb i hi))
    have los := ep_delta_value_l hZFC source family coherent system limit model hN target he haJ ha space haU (k := 3)
      (rd_entry0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
      (Fin.cases H (Fin.cases f (fun _ => ki)))
      ⟨Fin.cases s (Fin.cases x (fun _ => i)), fun _ => i⟩
      (Fin.cases value (Fin.cases (values i f x hif hix) (fun _ => iv)))
    refine ⟨x, (rd_entry0_sat_l hZF.1 ..).mp (los.mpr ⟨D, source.space_mem_l hZF hn space,
      (family.at_l hZF.1 haU ha space).base.top, fun _ h => h, ?_⟩), hix⟩
    intro v hv η entries
    have ei := (fn0_function_l (ZF.modelsKP hZF) fi).1.2 v (η.bound 2) i (entries 2) (ic v hv)
    apply (rd_entry0_sat_l hZF.1 ..).mpr
    change Rd_entry_d (η.bound 2) (η.bound 1) (η.bound 0)
    rw [ei]
    exact (matrix v _ i f _ (entries 0) hif).mpr (entries 1))
  exact eq ▸ value

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 拥有集合的超幂像中的完整内部真值

把 A 的有限真值表整体送到 j(A)，再对表中条目使用源内 Łoś。
目标赋值可为任意代表的坍塌值，不要求它属于常值嵌入的像，也不要求 A 的高度正则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_value_l {ω κ K L X R F J O Z A p T V q c C W d N S μ K' e i j c₀
    a₀ A₀ R₀ a₁ A₁ R₁ n D a U b l P r g t : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' N S)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hm : Smem_d I c₀ X R) (hn : Smem_d I d N S)
    (he : Smap_d I ω c d C N e) (hj : Smap_d I ω c₀ d X N j)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (h₀ : Smem_d I a₀ A₀ R₀) (h₁ : Smem_d I a₁ A₁ R₁) (hA : Rd_entry_d A₀ A₁ j)
    (hnω : M.mem n ω) (haJ : M.mem a J) (ha : Fn0_d n L a) (space : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    (program : Sfm_d I ω l P) (hb : M.mem b ω) (bound : Sbound_d I P b) (hr : M.mem r l)
    (value : Ep_value_d q e a g t) : ∃ E E', M.IsFunctionSpace I E b A₀ ∧ M.IsFunctionSpace I E' b A₁ ∧
      (Ssat_d I A₁ R₁ E' P l r t ↔ ∃ B, M.mem B X ∧ M.mem B U ∧ M.MemberSubset B D ∧
        ∀ s, M.mem s B → ∀ f, Rd_entry_d s f g → Ssat_d I A₀ R₀ E P l r f) := by
  obtain ⟨E, E', C₀, H, C₁, H', hE, hE', _, hCC, hHH, old, new⟩ :=
    ep_set_tables_l hZF source target hm hn hj hA
      (ep_set_membership_l hZF source target hm hn hj h₀ h₁ hA) program hb bound
  have natural := hj.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have hrω := source.omega.transitive (ZF.modelsKP hZF) l program.1 r hr
  obtain ⟨cr, _, fr, rc, rv⟩ := ep_value_constant_l hZF source family system limit constants comp
    hnω haJ ha space (source.transitive ω source.omega_mem r hrω) (natural r hrω)
  obtain ⟨cH, _, fH, Hc, Hv⟩ := ep_value_constant_l hZF source family system limit constants comp
    hnω haJ ha space (hj.1.1.input_mem_of_pairMember hHH) hHH
  obtain ⟨cC, _, fC, Cc, Cv⟩ := ep_value_constant_l hZF source family system limit constants comp
    hnω haJ ha space (hj.1.1.input_mem_of_pairMember hCC) hCC
  have los := ep_delta_value_l hZFC source family coherent system limit model target.transitive hn he haJ ha space haU (k := 4)
    (fv_at_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (fv_at_delta_l ..)
    (Fin.cases g (Fin.cases cr (Fin.cases cH (fun _ => cC))))
    ⟨Fin.cases t (Fin.cases r (Fin.cases H' (fun _ => C₁))), fun _ => t⟩
    (Fin.cases value (Fin.cases rv (Fin.cases Hv (fun _ => Cv))))
  simp only [fv_at_sat_l hZF.1] at los
  refine ⟨E, E', hE, hE', (new r hr t).symm.trans (los.trans ?_)⟩
  constructor
  · rintro ⟨B, hBX, hBU, sub, all⟩
    refine ⟨B, hBX, hBU, sub, fun s hs f hsf => ?_⟩
    let η : Env M 4 := ⟨Fin.cases f (Fin.cases r (Fin.cases H (fun _ => C₀))), fun _ => f⟩
    have point := all s hs η
      (Fin.cases hsf (Fin.cases (rc s (sub s hs)) (Fin.cases (Hc s (sub s hs)) (fun _ => Cc s (sub s hs)))))
    exact (old r hr f).mp point
  · rintro ⟨B, hBX, hBU, sub, all⟩
    refine ⟨B, hBX, hBU, sub, fun s hs η values => ?_⟩
    have er := (fn0_function_l (ZF.modelsKP hZF) fr).1.2 s (η.bound 1) r (values 1) (rc s (sub s hs))
    have eh := (fn0_function_l (ZF.modelsKP hZF) fH).1.2 s (η.bound 2) H (values 2) (Hc s (sub s hs))
    have ec := (fn0_function_l (ZF.modelsKP hZF) fC).1.2 s (η.bound 3) C₀ (values 3) (Cc s (sub s hs))
    change Fv_at_d (η.bound 3) (η.bound 2) (η.bound 1) (η.bound 0)
    rw [er, eh, ec]
    exact (old r hr (η.bound 0)).mpr (all s hs (η.bound 0) (values 0))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 拥有集合之像中的完整分量嵌入

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' N S)
    (small : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ A₀ R₀)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
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
  have ext := rf_ext_mem_l I hZF.1 small.transitive h₀
  have hD₀ := small.space_mem_l hZF hnω space
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
  have bω := source.omega.transitive (ZF.modelsKP hZF) b hb
  obtain ⟨g, fg, eval⟩ := rp_representatives_l I hZFC component.map fu
  have fg₀ : M.IsSetFunctionFromTo I g ω A₀ := ⟨fg.1, fg.2.1, fun m hm =>
    (fg.2.2 m hm).imp fun f hf => ⟨((hG f).mp hf.1).1, hf.2⟩⟩
  have sf f (hf : M.mem f G) := (rf_fun_mem_l I hZF.1 small.transitive h₀ hD₀).mpr
    (small.function_l hZF ((hG f).mp hf).1 ((hG f).mp hf).2)
  have evaluation : Rs_eval_d I ω D A₀ R₀ p₀ g u := by
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
    obtain ⟨w, hw, pw⟩ := pe_value_exists_l I hZF ext hEω ((hEω g).mpr fg₀) bω (small.transitive D hD₀ s hsD)
      ((h₀.2 s D).mpr ⟨small.transitive D hD₀ s hsD, hD₀, hsD⟩)
      (fun m f hm => evaluation.repr_l I fg.1 m f (bω m hm))
    have ft := (fn0_of_function_l (ZF.modelsKP hZF) ((hE t).mp (fH.bound_l hst).2)).mono_target_l (small.transitive B hB)
    have same : Senv_agree_d I b w t := by
      intro m x hm
      obtain ⟨f, _, hmf⟩ := fg₁.2.1 m hm
      exact (pw.value_l I ext fg.1 ((hEω w).mp hw).1 hm ((gr.2 m f).mp hmf).2).trans
        ((rf_val_mem_l I hZF.1 small.transitive h₀ (fg₁.bound_l hmf).2).trans (matrix s t m f x hst hmf).symm)
    exact (pe_sat_value_l I hZF ext code.2.1 bound code.2.2 hEω ((hEω g).mpr fg₀) hw pw).trans
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

/-! ## 小源超幂到拥有集合之像的完整初等嵌入

包含诱导的实际关系嵌入落入 j(A)。有限矩阵定理证明每个分量在 j(A) 中
完整初等，定向极限因子遂保持全部内部公式；A 无须具有正则高度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_inclusion_l {ω κ K L X R F J O Z A p T V q c C W d N S μ K' e i j c₀
    a₀ A₀ R₀ a₁ A₁ R₁ K₀ J₀ O₀ Z₀ D₀ p₀ T₀ V₀ q₀ c₁ C₀ W₀ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' N S)
    (small : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ A₀ R₀)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hm : Smem_d I c₀ X R) (hn : Smem_d I d N S)
    (he : Smap_d I ω c d C N e) (hj : Smap_d I ω c₀ d X N j)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (h₀ : Smem_d I a₀ A₀ R₀) (h₁ : Smem_d I a₁ A₁ R₁) (hA : Rd_entry_d A₀ A₁ j)
    (cover : Ea_subset_d ω κ X A₀)
    (system₀ : Ep_system_d I ω κ L A₀ R₀ F J₀ O₀ Z₀ D₀ p₀ T₀ V₀)
    (limit₀ : Di_limit_d D₀ p₀ T₀ V₀ q₀ C₀ W₀) (model₀ : Smdl_d I c₁ C₀ W₀) :
    ∃ g, Smap_d I ω c₁ a₁ C₀ A₁ g ∧
      ∀ a f E x, Ep_repr_d q₀ a f E → Rd_entry_d E x g → Ep_value_d q e a f x := by
  have hA₀ := hj.1.1.input_mem_of_pairMember hA
  have inside := source.transitive A₀ hA₀
  have agree : Ea_agree_d ω κ X A₀ := fun n D B hn hd sub => ⟨cover n D B hn hd sub, inside B⟩
  have family₀ := family.transfer_l agree
  have coherent₀ := coherent.transfer_l hZF agree
  have elementary := system₀.toEp_graph_d.elementary_l hZF small family₀ coherent₀
  obtain ⟨r, hr, _, reps⟩ := ep_inclusion_l hZF h₀ hm inside family₀ family system₀ limit₀ system limit
  obtain ⟨g, fg, gs⟩ := ZF.exists_compositionFunction hZF I hr.1 he.1.1
  have inj x y z (hx : Rd_entry_d x z g) (hy : Rd_entry_d y z g) : x = y := by
    obtain ⟨_, E, hxE, hEz⟩ := (gs x z).mp hx
    obtain ⟨_, H, hyH, hHz⟩ := (gs y z).mp hy
    exact hr.2 x y H (he.1.2 E H z hEz hHz ▸ hxE) hyH
  have values a f E x (old : Ep_repr_d q₀ a f E) (hEx : Rd_entry_d E x g) : Ep_value_d q e a f x := by
    obtain ⟨_, H, hEH, hHx⟩ := (gs E x).mp hEx
    exact ⟨H, (reps a f E H old).mp hEH, hHx⟩
  have into E x (hEx : Rd_entry_d E x g) : M.mem x A₁ := by
    obtain ⟨n, a, D, f, hnω, _, ha, space, _, ff, old⟩ :=
      ep_repr_surjective_l hZF family₀ system₀ limit₀ (fg.input_mem_of_pairMember hEx)
    obtain ⟨H, rep, hHx⟩ := values a f E x old hEx
    obtain ⟨k, _, fk, kc, B, br, hBA⟩ := ep_value_constant_l hZF source family system limit constants comp
      hnω (rep.index_l hZF system limit) ha space hA₀ hA
    have member := ep_repr_bound_mem_l hZF source family system limit fk kc br hA₀ hnω ha space ff rep
    exact ((hn.2 x A₁).mp ((he.relation_l I hZF source.omega model hn.1 hHx hBA).mp member)).2.2
  have fg₁ := (fn0_of_function_l (ZF.modelsKP hZF) fg).retarget_l into
  have hg : M.IsSetInjectionFromTo I g C₀ A₁ := ⟨fn0_function_l (ZF.modelsKP hZF) fg₁, inj⟩
  obtain ⟨f, ff, fs⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) limit₀.projection) hg.1
  obtain ⟨_, hz⟩ := system₀.codes
  have models := system₀.components
  have component a o (hao : Rd_entry_d a o Z₀) : ∃ H Q k,
      Smdl_d I o H Q ∧ Smap_d I ω o a₁ H A₁ k ∧
        ∀ B x, Rd_entry_d B x k ↔ M.mem B H ∧ ∃ u, KPair_d M u a B ∧ Rd_entry_d u x f := by
    obtain ⟨n, D, U, G, p', H, Q, hnω, ha, space, haU, hG, cmp⟩ := models a o hao
    obtain ⟨t, ht, ts⟩ := ep_stage_embedding_l hZF small.omega system₀.toEg_graph_d system₀.diagram limit₀ elementary model₀ hao cmp.code
    obtain ⟨k, fk, ks⟩ := ZF.exists_compositionFunction hZF I ht.1.1 hg.1
    have hk : M.IsSetInjectionFromTo I k H A₁ := ⟨fk, fun B D x hBx hDx => by
      obtain ⟨_, E, hBE, hEx⟩ := (ks B x).mp hBx
      obtain ⟨_, E', hDE, hE'x⟩ := (ks D x).mp hDx
      exact ht.1.2 B D E' (inj E E' x hEx hE'x ▸ hBE) hDE⟩
    have val f₀ B x (hfB : Rd_entry_d f₀ B p') (hBx : Rd_entry_d B x k) : Ep_value_d q e a f₀ x := by
      obtain ⟨_, E, hBE, hEx⟩ := (ks B x).mp hBx
      obtain ⟨_, u, hu, huE⟩ := (ts B E).mp hBE
      exact values a f₀ E x ⟨u, B, hu, cmp.map.representative_l I (family₀.at_l hZF.1 haU ha space).base hfB, huE⟩ hEx
    have hk' := ep_set_component_l hZFC source target small family coherent system limit model hm hn he hj constants comp
      h₀ h₁ hA cover hnω ((system.indices a).mpr ((system₀.indices a).mp (hz.bound_l hao).1)) ha space haU hG cmp hk val
    refine ⟨H, Q, k, cmp.code, hk', fun B x => ⟨?_, ?_⟩⟩
    · intro hBx
      obtain ⟨hB, E, hBE, hEx⟩ := (ks B x).mp hBx
      obtain ⟨_, u, hu, huE⟩ := (ts B E).mp hBE
      exact ⟨hB, u, hu, (fs u x).mpr ⟨(limit₀.projection.bound_l huE).1, E, huE, hEx⟩⟩
    · rintro ⟨hB, u, hu, hux⟩
      obtain ⟨_, E, huE, hEx⟩ := (fs u x).mp hux
      exact (ks B x).mpr ⟨hB, E, (ts B E).mpr ⟨hB, u, hu, huE⟩, hEx⟩
  have cone a o Y Q (stage : Di_stage_d I D₀ p₀ V₀ a o Y Q) :
      ∃ k, Smap_d I ω o a₁ Y A₁ k ∧ ∀ u x, Rd_entry_d u x k ↔ M.mem u Y ∧ Rd_entry_d u x f := by
    obtain ⟨u, hu⟩ := stage.1.2.1
    obtain ⟨o', _, hao⟩ := hz.2.1 a (system₀.projection.bound_l ((stage.2.1 u).mp hu).2).2
    obtain ⟨H, Q', k, cmp, hk, ks⟩ := component a o' hao
    obtain ⟨t, _, ht, _, ts, _⟩ := ep_tag_l hZF small.omega system₀.codes system₀.nodes system₀.index
      system₀.toEg_graph_d.label_l system₀.toEg_graph_d.relation_l stage hao cmp
    obtain ⟨s, hs, ss⟩ := smap_comp_l I hZF ht hk
    refine ⟨s, hs, fun u x => (ss u x).trans (and_congr_right fun hu => ?_)⟩
    constructor
    · rintro ⟨B, huB, hBx⟩
      obtain ⟨_, v, hv, hvx⟩ := (ks B x).mp hBx
      exact ((I).unique ((ts u B).mp huB).2 hv).symm ▸ hvx
    · intro hux
      obtain ⟨B, hB, huB⟩ := ht.1.1.2.2 u hu
      exact ⟨B, huB, (ks B x).mpr ⟨hB, u, ((ts u B).mp huB).2, hux⟩⟩
  have comm u v x y (huv : Rd_entry_d u v T₀) (hux : Rd_entry_d u x f) (hvy : Rd_entry_d v y f) : x = y := by
    obtain ⟨_, E, huE, hEx⟩ := (fs u x).mp hux
    obtain ⟨_, H, hvH, hHy⟩ := (fs v y).mp hvy
    exact fg.1.2 E x y hEx ((limit₀.commute_l system₀.diagram huv huE hvH).symm ▸ hHy)
  obtain ⟨g', hg', _, unique⟩ := di_factor_elementary_l hZF small.omega system₀.diagram limit₀ elementary model₀ h₁.1
    (fn0_of_function_l (ZF.modelsKP hZF) ff) comm cone
  have eq := unique g fg₁ (fun u E x huE hux => by
    obtain ⟨_, H, huH, hHx⟩ := (fs u x).mp hux
    exact (fn0_function_l (ZF.modelsKP hZF) limit₀.projection).1.2 u H E huH huE ▸ hHx)
  exact ⟨g, eq.symm ▸ hg', values⟩

end YesMetaZFC.SetTheory.LargeCardinal
