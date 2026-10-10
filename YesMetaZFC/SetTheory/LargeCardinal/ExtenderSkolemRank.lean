import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankClosure
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemSource

/-! # 小壳闭包在严格相对秩段中的保持

代码、参数列、选择图及壳都给出已有集合上的有限秩界。
最小性仍是对秩段中的全部候选壳成立的原最小性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.codes_rank_l {ω κ K Z S α V C : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) (hC : M.mem C Z) (codes : Scode_d I ω C) : M.mem C V := by
  have algebra := source.theory.algebra.rank_l hZF source.transitive hV rank hα
  have sequences := source.rank_sequences_l hZF hV rank hα hω
  obtain ⟨Q, hQ, qs⟩ := algebra.product ω ω hω hω
  obtain ⟨P, hP, ps⟩ := algebra.product ω Q hω hQ
  obtain ⟨J, hJ, js⟩ := sequences.space P hP
  obtain ⟨B, hB, bs⟩ := algebra.product J ω hJ hω
  apply rank.subset_mem_l source.transitive hV hB hC
  intro a ha
  obtain ⟨n, F, r, pair, program, hr⟩ := (codes a).mp ha
  have row {k c i j} (hc : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) : M.mem c P := by
    obtain ⟨p, o, ho, hp, hc⟩ := hc
    exact (ps c).mpr ⟨o, num_mem_l hZF.1 source.omega ho, p, (qs p).mpr ⟨i, hi, j, hj, hp⟩, hc⟩
  have fn : M.IsSetFunctionFromTo I F n P := by
    refine ⟨program.2.1.2.1, program.2.1.2.2, fun t ht => ?_⟩
    obtain ⟨c, hc⟩ := (program.2.1.2.2 t).mp ht
    have tw := source.omega.transitive hZF n program.1 t ht
    refine ⟨c, ?_, hc⟩
    rcases program.2.2 t c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
      ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · exact row hs hi hj
    · exact row hs hi hj
    · exact row hs (source.omega.transitive hZF t tw i hi) (source.omega.transitive hZF t tw j hj)
    · exact row hs hi (source.omega.transitive hZF t tw j hj)
  exact (bs a).mpr ⟨F, (js F).mpr ⟨n, program.1, fn⟩, r, source.omega.transitive hZF n program.1 r hr, pair⟩

theorem Ep_source_d.skolem_rank_l {ω κ K Z S α V : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (small : Sh_source_d (ZF.modelsKP hZF) ω Z)
    (hV : M.mem V Z) (rank : Vr_d Z α V) (hα : M.IsLimitOrdinal α) (hω : M.mem ω V) :
    Sh_source_d (ZF.modelsKP hZF) ω V := by
  intro c A R U μ f hA hR hU hμ hf hm ho hw sub bij
  have vz := source.transitive V hV
  have vt := rank.transitive_l hZF source.transitive hV
  obtain ⟨u, C, J, T, D, G, N, g, _, hC, hJ, hT, hD, hG, hN, hg, skolem, hull, gb⟩ :=
    small c A R U μ f (vz A hA) (vz R hR) (vz U hU) (vz μ hμ) (vz f hf) hm ho hw sub bij
  have hCV := source.codes_rank_l hZF hV rank hα hω hC skolem.codes
  obtain ⟨J', hJ', seq⟩ := (source.rank_sequences_l hZF hV rank hα hω).space A hA
  have hJV : M.mem J V := hZF.1.eq_of_same_members J' J (fun s => (seq s).trans (skolem.params s).symm) ▸ hJ'
  have hTV := rank.relation_mem_l hZF source.transitive hV hα hCV hω hT (fun p hp => (skolem.labels p).mp hp)
  have hDV := rank.relation_mem_l hZF source.transitive hV hα hTV hJV hD (fun p hp => (skolem.domain p).mp hp)
  have hGV := rank.relation_mem_l hZF source.transitive hV hα hDV hA hG (fn0_of_function_l (ZF.modelsKP hZF) skolem.graph).1
  have hNV := rank.subset_mem_l source.transitive hV hA hN hull.2.1
  have hgV := rank.relation_mem_l hZF source.transitive hV hα hμ hNV hg (fn0_of_function_l (ZF.modelsKP hZF) gb.1.1).1
  exact ⟨u, C, J, T, D, G, N, g, vt A hA u skolem.point, hCV, hJV, hTV, hDV, hGV, hNV, hgV,
    skolem, ⟨hull.1, hull.2.1, hull.2.2.1, fun B hB => hull.2.2.2 B (vz B hB)⟩, gb⟩

end YesMetaZFC.SetTheory.LargeCardinal
