import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeedSegment

/-! # 坍塌把坐标类精确识别为支撑序数

支撑初段已经独立于整体坍塌构造。把给定坍塌限制到该初段，局部递归
唯一性就识别出原支撑序数；不再重复坐标初段的构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_seed_collapse_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q C W N e : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L)
    (hωL : M.MemberSubset ω L) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (collapse : Wc_graph_d C W e) (he : Fn0_d C N e) :
    M.MemberSubset L N ∧ ∀ α E, Ep_seed_d κ L q α E → Rd_entry_d E α e := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, r, sub, map, _, read, down⟩ := ep_seed_segment_l hZF source hκ hL hωL family coherent atoms normal h limit
  obtain ⟨s, restriction⟩ := ZF.exists_restriction hZF I e B
  have fs := restriction.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) he) sub
  have graph : Wc_graph_d B W s := by
    refine ⟨fs.1.1, fun E α entry => ?_⟩
    obtain ⟨hE, original⟩ := (restriction.2 E α).mp entry
    refine ⟨hE, ?_, fun β => ?_⟩
    · intro H hH edge
      obtain ⟨β, _, hHβ⟩ := he.2.1 H (sub H hH)
      exact ⟨β, (restriction.2 H β).mpr ⟨hH, hHβ⟩⟩
    · rw [(collapse.2 E α original).2.2 β]
      exact ⟨fun ⟨H, _, edge, hHβ⟩ => ⟨H, down E H hE edge, edge,
        (restriction.2 H β).mpr ⟨down E H hE edge, hHβ⟩⟩,
        fun ⟨H, hH, edge, hHβ⟩ => ⟨H, sub H hH, edge, ((restriction.2 H β).mp hHβ).2⟩⟩
  have fixed : ∀ α E, Ep_seed_d κ L q α E → Rd_entry_d E α e := by
    intro α E seed
    have hEα := (read E α).mpr seed
    obtain ⟨β, _, hEβ⟩ := fs.2.2 E (map.function.bound_l hEα).1
    have eq := wc_value_unique_l hZF (map.well_founded_l (ZF.modelsKP hZF))
      ⟨s, graph, hEβ⟩ ⟨r, map.graph_l, hEα⟩
    exact eq ▸ ((restriction.2 E β).mp hEβ).2
  exact ⟨fun α hα => by
    obtain ⟨E, _, hs⟩ := ep_seed_exists_l hZF source family h limit hα
    exact (he.bound_l (fixed α E hs)).2, fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal
