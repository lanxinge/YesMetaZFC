import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSupport
import YesMetaZFC.Model.SetTheory.Internal.SourceOmegaBound
import YesMetaZFC.SetTheory.CumulativeRelativeClosure

/-! # 可数支撑列属于所属源的严格秩段

源内支撑覆盖列的正则界同时界住每个有限坐标。两个有界关系构造依次
回收支撑列的值域和整张图，所需共尾性仅为源内部的 ω 界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ec_support_rank_l {ω κ K Y R L V S A : M.Domain}
    (owner : Ep_source_d hZF ω κ K Y R) (hL : M.mem L Y) (limit : M.IsLimitOrdinal L)
    (hωL : M.mem ω L) (bound : Sc_omega_bound_d ω Y L) (hV : M.mem V Y) (rank : Vr_d Y L V)
    (hA : M.mem A Y) (seq : Fseq_space_d I ω L S) (fa : Fn0_d ω S A) : M.mem A V := by
  obtain ⟨e, he, fe, cover⟩ := ec_source_cover_l hZF owner hL (limit.1.transitive ω hωL) hA seq fa
  obtain ⟨β, hβ, bounded⟩ := bound e he (fn0_of_function_l (ZF.modelsKP hZF) fe.1)
  obtain ⟨c, code⟩ := owner.code
  obtain ⟨B, hB, values⟩ := sc_range_source_l hZF owner.omega owner.transitive code owner.theory hA
  have hωV := rank.ordinal_subset_l hZF owner.transitive hV ω hωL
  have hβV := rank.ordinal_subset_l hZF owner.transitive hV β hβ
  have hBV := rank.relations_mem_l owner.transitive hV limit hωV hβV hB (fun a ha p hp => by
    obtain ⟨i, hia⟩ := (values a).mp ha
    obtain ⟨n, hn, fn⟩ := (seq a).mp (fa.bound_l hia).2
    obtain ⟨j, hj, x, _, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) fn).1 p hp
    obtain ⟨k, hk⟩ := cover i a j x hia ⟨p, pair, hp⟩
    exact ⟨j, owner.omega.transitive hZF n hn j hj, x, bounded k x hk, pair⟩)
  exact rank.relation_mem_l hZF owner.transitive hV limit hωV hBV hA (fun p hp => by
    obtain ⟨i, hi, a, _, pair⟩ := fa.1 p hp
    exact ⟨i, hi, a, (values a).mpr ⟨i, p, pair, hp⟩, pair⟩)

end YesMetaZFC.SetTheory.LargeCardinal
