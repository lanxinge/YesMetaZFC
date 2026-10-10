import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelationCode
import YesMetaZFC.Model.SetTheory.Internal.FiniteEvaluation

/-! # 实际源中的有限程序与有限赋值空间

任意合法内部程序的指令都由自然数配对得到；有限函数闭性将整张程序图
放入源中。所有空间与界均实际构造，不假设源包含完整的 ω 赋值空间。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.finite_space_l {ω κ K Z S A b : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hA : M.mem A Z) (hb : M.mem b ω) :
    ∃ E, M.mem E Z ∧ M.IsFunctionSpace I E b A := by
  obtain ⟨J, hJZ, hJ⟩ := source.sequences.space A hA
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 2 := ⟨Fin.cases b (fun _ => A), fun _ => b⟩
  let φ : UnarySchema 2 := { body := fn0_m (.bound 1) (.bound 2) .newest }
  obtain ⟨E, hEZ, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory
    φ (fn0_delta_l ..) ρ (Fin.cases (source.transitive ω source.omega_mem b hb) (fun _ => hA)) hJZ
  refine ⟨E, hEZ, fun f => (spec f).trans ?_⟩
  have sat : φ.denote ρ f ↔ Fn0_d b A f := fn0_sat_l hZF.1 ..
  exact (and_congr_right fun _ => sat).trans ⟨fun h => fn0_function_l (ZF.modelsKP hZF) h.2,
    fun hf => ⟨(hJ f).mpr ⟨b, hb, hf⟩, fn0_of_function_l (ZF.modelsKP hZF) hf⟩⟩

theorem Ep_source_d.program_l {ω κ K Z S n F : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hF : Sfm_d I ω n F) :
    M.mem F Z ∧ ∃ b L, M.mem L Z ∧ Fb_program_d (ZF.modelsKP hZF) ω b n L F := by
  have pair {p a b} (h : KPair_d M p a b) (ha : M.mem a Z) (hb : M.mem b Z) : M.mem p Z := by
    obtain ⟨q, hq, eq⟩ := source.kpair_l hZF ha hb
    exact kpair_unique_l M hZF.1 eq h ▸ hq
  have op {k c i j} (h : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) : M.mem c Z := by
    obtain ⟨a, o, ho, ha, hc⟩ := h
    exact pair hc (source.transitive ω source.omega_mem o (num_mem_l hZF.1 source.omega ho))
      (pair ha (source.transitive ω source.omega_mem i hi) (source.transitive ω source.omega_mem j hj))
  have row r c (hc : Rd_entry_d r c F) : M.mem c Z := by
    have hr := source.omega.transitive hZF n hF.1 r ((hF.2.1.2.2 r).mpr ⟨c, hc⟩)
    rcases hF.2.2 r c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
      ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · exact op hs hi hj
    · exact op hs hi hj
    · exact op hs (source.omega.transitive hZF r hr i hi) (source.omega.transitive hZF r hr j hj)
    · exact op hs hi (source.omega.transitive hZF r hr j hj)
  have fn : M.IsSetFunctionFromTo I F n Z := ⟨hF.2.1.2.1, hF.2.1.2.2, fun r hr =>
    ((hF.2.1.2.2 r).mp hr).imp fun c hc => ⟨row r c hc, hc⟩⟩
  obtain ⟨c, hc⟩ := source.code
  have hFZ := sc_finite_function_l hZF source.omega source.transitive hc source.theory source.omega_mem
    (fun _ h => h) hF.1 (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨_, L, hLZ, hfL⟩ := source.function_l hZF
    hFZ (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF source.omega hF
  exact ⟨hFZ, b, L, hLZ, fb_program_of_l (ZF.modelsKP hZF) hF hb bound hfL⟩

end YesMetaZFC.SetTheory.LargeCardinal
