import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceLimit
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceBranch
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemSource

/-! # 内部所属扩展器的完整实际后继节点

同一次定向极限和坍塌同时给出实际超幂边及全部下一步不变量：源理论、
枝反射、相对层级、相对幂集、传递包络和小 Skolem 壳闭包。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.node_l {ω κ K X R K' Y R' L F P : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y R')
    (branches : Sc_branch_d ω X) (hierarchy : Sc_hierarchy_d X) (power : Sc_power_d X) (cover : Sc_cover_d X)
    (small : Sh_source_d (ZF.modelsKP hZF) ω X) (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hP : M.mem P Y) (owner_power : FilterZF.Source_d Y K' P)
    (loc : It_local_d ω Y κ L F) : ∃ N S b d j K₀,
      Ep_successor_d hZF ω κ L X R F N S ∧ It_ultra_d hZF ω κ L F b d j ∧
      Smem_d I b X R ∧ Smem_d I d N S ∧ Smap_d I ω b d X N j ∧ Ep_source_d hZF ω ω K₀ N S ∧
      Sc_branch_d ω N ∧ Sc_hierarchy_d N ∧ Sc_power_d N ∧ Sc_cover_d N ∧ Sh_source_d (ZF.modelsKP hZF) ω N := by
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, system, limit, model, _, elementary, collapse⟩ :=
    loc.limit_l hZFC source owner branches cover power inside agree owner_branches hP owner_power
  obtain ⟨_, b, i, N, e, _, d, S, j, hm, hi, constants, ht, wc, bij, hn, he, _, _, _, hj, js, K₀, target⟩ := collapse
  have next : Ep_successor_d hZF ω κ L X R F N S := ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e,
    system, limit, model, hn, ht, wc, bij, he⟩
  have ultra : It_ultra_d hZF ω κ L F b d j := ⟨X, R, N, S, J, O, Z, A, p, T, V, q, c, C, W, i, e,
    hm, hn, system, limit, model, wc, bij, he, hi, constants, hj, hj.1.1.1.1,
    fun x y => (js x y).trans ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  exact ⟨N, S, b, d, j, K₀, next, ultra, hm, hn, hj, target,
    loc.branch_l hZF source owner (ZFC.dc_l I hZFC source.omega) branches cover power inside agree owner_branches hP owner_power
      system limit model elementary ht target.omega_mem target.theory.algebra hn he (fun y hy => (bij.2 y hy).imp fun _ h => h.2),
    (sc_hierarchy_iff_l hZF source.omega source.transitive ht hm hn hj).mp hierarchy,
    (sc_power_iff_l hZF source.omega source.transitive ht hm hn hj).mp power,
    (sc_cover_iff_l hZF source.omega source.transitive ht hm hn hj).mp cover,
    (sh_source_iff_l hZF source target hm hn hj).mp small⟩

end YesMetaZFC.SetTheory.LargeCardinal
