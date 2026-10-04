import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.LosSyntax
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Witness
import YesMetaZFC.Model.SetTheory.Internal.Induction
import YesMetaZFC.Model.SetTheory.Internal.Satisfaction

/-! # 全部内部程序行的 Łoś 定理

在真实可分离的行性质上作内部强归纳。原子步读取商投影，或非步使用超滤二择，
存在步构造真实见证函数及更新后的赋值族。此处代表族明确为全部背景内部函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rp_los_l (hZFC : M.Models ZFC) {ω D Q U R c G p C T E K F n H r}
    (hU : FilterZF.Maximal_d (ℳ := M) D U) (hM : Rp_model_d I D Q U R c G p C T)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hE : M.IsFunctionSpace I E ω Q)
    (hK : M.IsFunctionSpace I K ω C) (hF : Sfm_d I ω n F) (hH : Seval_d I Q R E F n H)
    (hr : M.mem r n) : Rp_los_d I ω D U p E H C T K F n r := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF C T K F hF.2.1.1
  have hQ : ∃ x, M.mem x Q := by
    obtain ⟨B, hB⟩ := hM.code.2.1
    obtain ⟨f, hf⟩ := (hM.map.range B).mp hB
    obtain ⟨d, hd⟩ := hU.2.1 D hU.1.2.1
    exact ((hM.map.functions f (hM.map.projection.input_mem_of_pairMember hf)).2.1 d hd).imp fun _ hx => hx.1
  let ρ : Env M 11 := ⟨Fin.cases n (Fin.cases F (Fin.cases K (Fin.cases T (Fin.cases C (Fin.cases H
    (Fin.cases E (Fin.cases p (Fin.cases U (Fin.cases D (fun _ => ω)))))))))), fun _ => ω⟩
  let φ : UnarySchema 11 := {
    body := rp_los_m (𝒞 := 𝒞) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s : φ.denote ρ s ↔ Rp_los_d I ω D U p E H C T K F n s := rp_los_sat_l I hZF.1 ..
  suffices h : φ.denote ρ r from (sat r).mp h
  apply sfm_induction_l I hZF hF φ ρ ?_ hr
  intro r hr ih
  apply (sat r).mpr
  intro V e Z hV he hZ hv
  obtain ⟨o, ho⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r o ho with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨f, B, hf, hie, hfc⟩ := hv i hi
    obtain ⟨g, A, hg, hje, hgc⟩ := hv j hj
    have src v := (seval_row_l I hZF hF hH ho hZ v).trans
      (and_congr_right fun _ => snode_decode_l I (ZF.modelsKP hZF) 0 hs)
    exact (rp_holds_rel_l I hU.1.1 hV (hM.map.functions f (hM.map.projection.input_mem_of_pairMember hf))
      (hM.map.functions g (hM.map.projection.input_mem_of_pairMember hg)) hfc hgc src).trans
      ((hM.relation f g B A hf hg).symm.trans (ssat_rel_l I hZF hF hJ ho hs hK he hie hje).symm)
  · obtain ⟨f, B, hf, hie, hfc⟩ := hv i hi
    obtain ⟨g, A, hg, hje, hgc⟩ := hv j hj
    have src v := (seval_row_l I hZF hF hH ho hZ v).trans
      (and_congr_right fun _ => snode_decode_l I (ZF.modelsKP hZF) 1 hs)
    exact (rp_holds_eq_l I hU.1.1 hV (hM.map.functions f (hM.map.projection.input_mem_of_pairMember hf)) hfc hgc src).trans
      ((rp_kernel_l I hZF.1 hU.1.base_l hM.map hf hg).symm.trans (ssat_eq_l I hZF hF hJ ho hs hK he hie hje).symm)
  · obtain ⟨A, hA⟩ := (hH.1.2.2 i).mp (hH.1.1.transitive r hr i hi)
    obtain ⟨B, hB⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
    have spec v : M.mem v Z ↔ M.mem v E ∧ ¬ (M.mem v A ∨ M.mem v B) := by
      have src := (seval_row_l I hZF hF hH ho hZ v).trans
        (and_congr_right fun _ => snode_decode_l I (ZF.modelsKP hZF) 2 hs)
      refine src.trans ⟨?_, ?_⟩
      · rintro ⟨hv, A', B', hA', hB', ht⟩
        exact ⟨hv, hH.1.2.1.2 i A' A hA' hA ▸ hH.1.2.1.2 j B' B hB' hB ▸ ht⟩
      · exact fun ⟨hv, ht⟩ => ⟨hv, A, B, hA, hB, ht⟩
    exact (rp_holds_nor_l I hZF hU hV spec).trans ((not_congr (or_congr
      ((sat i).mp (ih i hi) V e A hV he hA hv) ((sat j).mp (ih j hj) V e B hV he hB hv))).trans
        (ssat_nor_l I hZF hF hJ ho hs he).symm)
  · obtain ⟨A, hA⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
    rw [rp_quantifier_row_l I hZFC hF hH ho hs hZ hA hE hV hU.1.1 hQ,
      ssat_exists_l I hZF hF hJ ho hs he]
    constructor
    · rintro ⟨f, W, hf, hW, hw⟩
      obtain ⟨B, hB, hfB⟩ := hM.map.projection.2.2 f (hG f hf)
      obtain ⟨e', he', hk⟩ := senv_update_exists_l I hZF ((hK e).mp he) hi hB
      exact ⟨B, e', hB, he', ((sat j).mp (ih j hj) W e' A hW.1 ((hK e').mpr hk) hA
        (hv.update_l I hf hfB hW he')).mp hw⟩
    · rintro ⟨B, e', hB, he', ht⟩
      obtain ⟨f, hfB⟩ := (hM.map.range B).mp hB
      have hf := hM.map.functions f (hM.map.projection.input_mem_of_pairMember hfB)
      obtain ⟨W, hW⟩ := rp_update_exists_l I hZF hE hV hi hf
      have hk := (hK e').mpr (he'.function_l I ((hK e).mp he) hi hB)
      exact ⟨f, W, hf, hW, ((sat j).mp (ih j hj) W e' A hW.1 hk hA (hv.update_l I hf hfB hW he')).mpr ht⟩

/-- 统一满足关系上的 Łoś 方程，公式遍历全部实际内部代码。 -/
theorem rp_satisfies_l (hZFC : M.Models ZFC) {ω D Q U R c G p C T s A E V e a}
    (hU : FilterZF.Maximal_d (ℳ := M) D U) (hM : Rp_model_d I D Q U R c G p C T)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hs : Smdl_d I s Q R) (hA : Scode_d I ω A)
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E)
    (he : M.IsSetFunctionFromTo I e ω C) (hv : Rp_eval_d I ω D p V e) (ha : M.mem a A) :
    Satisfies_d I ω c a e ↔ ∃ B, M.mem B U ∧ ∀ d, M.mem d B →
      ∃ v, M.PairMember I d v V ∧ Satisfies_d I ω s a v := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨n, F, r, hf⟩ := (hA a).mp ha
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  obtain ⟨H, hH⟩ := seval_exists_l I hZF Q R E F hf.2.1.2.1.1
  obtain ⟨Z, hZ⟩ := (hH.1.2.2 r).mp hf.2.2
  have src v := (satisfies_decode_l I hZF.1 hs hf hE).trans (ssat_value_l I hZF hH hZ v)
  have los := rp_los_l I hZFC hU hM hG hE hK hf.2.1 hH hf.2.2 V e Z hV ((hK e).mpr he) hZ hv
  refine (satisfies_decode_l I hZF.1 hM.code hf hK).trans (los.symm.trans ?_)
  exact exists_congr fun B => and_congr_right fun _ => forall_congr' fun d =>
    imp_congr Iff.rfl (exists_congr fun v => and_congr_right fun _ => (src v).symm)

/-- 商赋值和完整内部代码集自动构造，不把“存在代表赋值”作为操作参数。 -/
theorem rp_los_assignment_l (hZFC : M.Models ZFC) {ω D Q U R c G p C T s E V}
    (hω : M.IsOmega ω) (hU : FilterZF.Maximal_d (ℳ := M) D U) (hM : Rp_model_d I D Q U R c G p C T)
    (hG : ∀ f, Fn0_d D Q f → M.mem f G) (hs : Smdl_d I s Q R)
    (hE : M.IsFunctionSpace I E ω Q) (hV : M.IsSetFunctionFromTo I V D E) : ∃ e A,
      M.IsSetFunctionFromTo I e ω C ∧ Rp_eval_d I ω D p V e ∧ Scode_d I ω A ∧
      ∀ a, M.mem a A → (Satisfies_d I ω c a e ↔ ∃ B, M.mem B U ∧ ∀ d, M.mem d B →
        ∃ v, M.PairMember I d v V ∧ Satisfies_d I ω s a v) := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨e, he, hv⟩ := rp_eval_exists_l I hZF hM.map hG hE hV
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  exact ⟨e, A, he, hv, hA, fun _ ha => rp_satisfies_l I hZFC hU hM hG hs hA hE hV he hv ha⟩

end YesMetaZFC.SetTheory.Internal
