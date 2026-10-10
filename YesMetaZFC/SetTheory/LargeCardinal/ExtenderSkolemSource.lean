import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemRead

/-! # 模型内小 Skolem 壳的全参数传输

传输的是完整的全称存在句子，因此后继中的新结构和新种子同样适用。
读取结果包含源内的实际选择图、相对最小闭包及序数上的双射图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.skolem_output_l {ω κ K₀ Z W c : M.Domain} (source : Ep_source_d hZF ω κ K₀ Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A R U μ : Term d)
    (hw : (w.eval ρ).val = ω) (hm : Smdl_d I c (A.eval ρ).val (R.eval ρ).val) :
    Formula.satisfies ρ (sh_output_m w A R U μ) ↔
      Sh_data_d (ZF.modelsKP hZF) Z ω c (A.eval ρ).val (U.eval ρ).val (μ.eval ρ).val := by
  let v (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  have read (u C J T D K N f : (rt_model_l Z hz).Domain) :
      Formula.satisfies ((((((((ρ.push u).push C).push J).push T).push D).push K).push N).push f)
        (.conj (sh_skolem_m (v w) (v A) (v R) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
          (.conj (sh_hull_m (v w) (v A) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (v U) (.bound 1))
            (sh_bijection_m .newest (v μ) (.bound 1)))) ↔
        Ssk_d I ω c (A.eval ρ).val u.val C.val J.val T.val D.val K.val ∧
          Sh_hull_d (ZF.modelsKP hZF) Z ω (A.eval ρ).val T.val K.val (U.eval ρ).val N.val ∧
            M.IsSetBijectionFromTo I f.val (μ.eval ρ).val N.val := by
    let η := ((((((((ρ.push u).push C).push J).push T).push D).push K).push N).push f)
    have sk := source.skolem_sat_l hZF hz η (v w) (v A) (v R)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2)
      (by simpa only [η, v, Definitional.Term.eval_weaken] using hw)
      (by simpa only [η, v, Definitional.Term.eval_weaken] using hm)
    simp only [η, v, Definitional.Term.eval_weaken] at sk
    rw [Formula.satisfies_conj_iff, sk]
    apply and_congr_right
    intro h
    have hull := sh_hull_relative_l (ZF.modelsKP hZF) source.transitive hz η
      (v w) (v A) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (v U) (.bound 1)
      (by simpa only [η, v, Definitional.Term.eval_weaken, hw] using h.params) h.domain
      (by simpa only [η, v, Definitional.Term.eval_weaken] using h.graph)
    have bij := (rt_model_delta_l source.transitive hz (sh_bijection_delta_l .newest (v μ) (.bound 1)) η).trans
      (sh_bijection_sat_l (ZF.modelsKP hZF) ..)
    have tr := and_congr hull bij
    simp only [η, v, eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val,
      Definitional.Term.eval_weaken, hw] at tr
    change _ ↔ (Sh_hull_d (ZF.modelsKP hZF) Z ω (A.eval ρ).val T.val K.val (U.eval ρ).val N.val ∧
      M.IsSetBijectionFromTo I f.val (μ.eval ρ).val N.val) at tr
    exact (Formula.satisfies_conj_iff ..).trans tr
  simp only [sh_output_m, Formula.satisfies_exists_iff]
  constructor
  · rintro ⟨u, C, J, T, D, K, N, f, h⟩
    exact ⟨u.val, C.val, J.val, T.val, D.val, K.val, N.val, f.val,
      u.property, C.property, J.property, T.property, D.property, K.property, N.property, f.property,
      (read u C J T D K N f).mp h⟩
  · rintro ⟨u, C, J, T, D, K, N, f, hu, hC, hJ, hT, hD, hK, hN, hf, h⟩
    exact ⟨⟨u, hu⟩, ⟨C, hC⟩, ⟨J, hJ⟩, ⟨T, hT⟩, ⟨D, hD⟩, ⟨K, hK⟩, ⟨N, hN⟩, ⟨f, hf⟩,
      (read ⟨u, hu⟩ ⟨C, hC⟩ ⟨J, hJ⟩ ⟨T, hT⟩ ⟨D, hD⟩ ⟨K, hK⟩ ⟨N, hN⟩ ⟨f, hf⟩).mpr h⟩

theorem Ep_source_d.skolem_source_sat_l {ω κ K Z W : M.Domain} (source : Ep_source_d hZF ω κ K Z W)
    (hz : Nonempty {x // M.mem x Z}) (ρ : Env (rt_model_l Z hz) 1) (hw : (ρ.bound 0).val = ω) :
    Formula.satisfies ρ (sh_source_m .newest) ↔ Sh_source_d (ZF.modelsKP hZF) ω Z := by
  have input (A R U μ f : (rt_model_l Z hz).Domain) :
      Formula.satisfies (((((ρ.push A).push R).push U).push μ).push f)
        (sh_input_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ↔
      M.IsOrdinal μ.val ∧ M.MemberSubset ω μ.val ∧ M.MemberSubset U.val A.val ∧
        M.IsSetBijectionFromTo I f.val μ.val U.val ∧ M.IsSetRelationOn I R.val A.val := by
    have tr := (rt_model_delta_l source.transitive hz
      (sh_input_delta_l (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
      (((((ρ.push A).push R).push U).push μ).push f)).trans (sh_input_sat_l (ZF.modelsKP hZF) ..)
    change _ ↔ (M.IsOrdinal μ.val ∧ M.MemberSubset (ρ.bound 0).val μ.val ∧ M.MemberSubset U.val A.val ∧
      M.IsSetBijectionFromTo I f.val μ.val U.val ∧ M.IsSetRelationOn I R.val A.val) at tr
    exact hw ▸ tr
  have output {c} (A R U μ f : (rt_model_l Z hz).Domain) (hm : Smdl_d I c A.val R.val) :=
    source.skolem_output_l hZF hz (((((ρ.push A).push R).push U).push μ).push f)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) hw hm
  simp only [sh_source_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff]
  constructor
  · intro h c A R U μ f hA hR hU hμ hf hm ho hωμ hUA bij
    exact (output ⟨A, hA⟩ ⟨R, hR⟩ ⟨U, hU⟩ ⟨μ, hμ⟩ ⟨f, hf⟩ hm).mp
      (h ⟨A, hA⟩ ⟨R, hR⟩ ⟨U, hU⟩ ⟨μ, hμ⟩ ⟨f, hf⟩
        ((input ⟨A, hA⟩ ⟨R, hR⟩ ⟨U, hU⟩ ⟨μ, hμ⟩ ⟨f, hf⟩).mpr ⟨ho, hωμ, hUA, bij, hm.2.2⟩))
  · intro h A R U μ f hi
    obtain ⟨ho, hωμ, hUA, bij, relation⟩ := (input A R U μ f).mp hi
    obtain ⟨z, _, hzω⟩ := source.omega.1.1
    obtain ⟨x, hx, _⟩ := bij.1.1.2.2 z (hωμ z hzω)
    obtain ⟨c, hc⟩ := (kp_pair_l (ZF.modelsKP hZF)).total A.val R.val
    have hm : Smdl_d I c A.val R.val := ⟨hc, ⟨x, hUA x hx⟩, relation⟩
    exact (output A R U μ f hm).mpr
      (h c A.val R.val U.val μ.val f.val A.property R.property U.property μ.property f.property hm ho hωμ hUA bij)

theorem sh_source_iff_l {ω κ K X R μ L Y S c d q : M.Domain}
    (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω μ L Y S) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hq : Smap_d I ω c d X Y q) : Sh_source_d (ZF.modelsKP hZF) ω X ↔ Sh_source_d (ZF.modelsKP hZF) ω Y := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, target.omega_mem⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨ω, source.omega_mem⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨ω, target.omega_mem⟩, fun _ => ⟨ω, target.omega_mem⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF source.omega ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hq⟩
    nx ny (sh_source_m .newest) (by simp -implicitDefEqProofs) ρ η
    (fun _ => hq.omega_l I hZF source.omega source.transitive target.transitive hm hn source.omega_mem)
  exact (source.skolem_source_sat_l hZF nx ρ rfl).symm.trans (tr.trans (target.skolem_source_sat_l hZF ny η rfl))

/-- 小壳理论和原源数据一同传给初等后继，并允许换用后继中的新大小参数。 -/
theorem Ep_source_d.skolem_successor_l {ω κ K X R c d N W j μ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (h : Sh_source_d (ZF.modelsKP hZF) ω X)
    (hm : Smem_d I c X R) (hn : Smem_d I d N W) (hN : M.TransitiveSet N)
    (hj : Smap_d I ω c d X N j) (hμ : M.mem μ N) (hωμ : M.MemberSubset ω μ) (small : Sc_small_d N μ) :
    ∃ L, Ep_source_d hZF ω μ L N W ∧ Sh_source_d (ZF.modelsKP hZF) ω N := by
  obtain ⟨L, target⟩ := source.successor_l hZF hm hn hN hj hμ hωμ small
  exact ⟨L, target, (sh_source_iff_l hZF source target hm hn hj).mp h⟩

end YesMetaZFC.SetTheory.LargeCardinal
