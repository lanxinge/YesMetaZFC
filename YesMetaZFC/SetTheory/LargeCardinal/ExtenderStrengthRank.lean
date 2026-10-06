import YesMetaZFC.SetTheory.LargeCardinal.ExtenderExactStrength
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRank

/-! # 所属源的最大强度在严格秩截断中保持

相对幂集和整个有界超幂使用原来的见证。截断包含源中原有的每个 L 子集，
故支撑以下的覆盖与支撑处的遗漏同时保持。这里只消费截断源的实际闭包证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Ex_strength_d.rank_l (hZF : M.Models ZF) {ω κ K X α V R L F W : M.Domain}
    (source : Ep_source_d hZF ω κ K V R) (hX : M.TransitiveSet X) (hV : M.mem V X)
    (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hL : M.mem L V) (hF : M.mem F V)
    (limit : M.IsLimitOrdinal L) (hκ : M.mem κ L) (level : Er_level_d V L W)
    (h : Ex_strength_d hZF ω κ L X F) : Ex_strength_d hZF ω κ L V F := by
  obtain ⟨_, _, _, _, ho, K₀, P, A, Q, Y, e, _, hP, _, seq, power, collapse, strength⟩ := h
  have eq := hZF.1.eq_of_same_members K₀ K (fun f => (seq f).trans (source.finite f).symm)
  subst K₀
  have hPV := rank.subsets_mem_l hX hV hα source.cardinal_mem hP (fun x hx => ((power x).mp hx).2)
  have hκW := level.hierarchy.ordinal_subset_l hZF source.transitive level.member κ hκ
  have hPW := level.hierarchy.subsets_mem_l source.transitive level.member limit hκW hPV
    (fun x hx => ((power x).mp hx).2)
  obtain ⟨hYV, collapse'⟩ := collapse.rank_l hZF source hX hV rank hα hL hF limit level hκW hPW
  refine ⟨source.omega_mem, source.cardinal_mem, hL, hF, ho, K, P, A, Q, Y, e,
    source.finite_mem, hPV, hYV, source.finite, fun x => ?_, collapse', ?_, ?_⟩
  · exact ⟨fun hx => ⟨source.transitive P hPV x hx, ((power x).mp hx).2⟩,
      fun ⟨hx, sub⟩ => (power x).mpr ⟨hX V hV x hx, sub⟩⟩
  · exact fun β hβ x hx => strength.1 β hβ x (hX V hV x hx)
  · obtain ⟨x, hx, sub, missing⟩ := strength.2
    exact ⟨x, rank.subset_mem_l hX hV hL hx sub, sub, missing⟩

end YesMetaZFC.SetTheory.LargeCardinal
