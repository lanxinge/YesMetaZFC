import YesMetaZFC.SetTheory.LargeCardinal.IterationApply
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceNode

/-! # 内部所属短扩展器直接延长实际迭代树

施加源包含所属模型，且两源在有限 κ 幂的子集上一致。实际良基性、坍塌、
超幂边及新节点不变量由内部所属判断自动构造，再把同一节点加入原树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_local_apply_l {ω c₀ α ξ T Q G E k c d X R Y S κ K K' L F P : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (owner : Ep_source_d hZF ω κ K X R) (source : Ep_source_d hZF ω κ K' Y S)
    (branches : Sc_branch_d ω Y) (hierarchy : Sc_hierarchy_d Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Y) (inside : M.MemberSubset X Y) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω X) (hP : M.mem P X) (owner_power : FilterZF.Source_d X K P)
    (loc : It_local_d ω X κ L F) : ∃ β U Q' G' E' b j p N V K₀,
      It_tree_d hZF ω c₀ β U Q' G' E' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d hZF ω κ L F d b j ∧
      It_payload_d p κ L F ∧ Rd_entry_d ξ p E' ∧ Smem_d I b N V ∧ Ep_source_d hZF ω ω K₀ N V ∧
      Sc_branch_d ω N ∧ Sc_hierarchy_d N ∧ Sc_power_d N ∧ Sc_cover_d N ∧ Sh_source_d (ZF.modelsKP hZF) ω N := by
  obtain ⟨N, V, a, b, j, K₀, _, ultra, code, target, _, ready, nb, nh, np, nc, ns⟩ :=
    loc.node_l hZFC source owner branches hierarchy power cover small inside
      (fun n D A hn hd sub => (agree n D A hn hd sub).symm) owner_branches hP owner_power
  have eq := (smem_unique_l I hZF.1 code my).1
  subst a
  obtain ⟨β, U, Q', G', E', p, built, extension, hb, edge, hu, payload, move⟩ :=
    it_apply_l hZF tree hα hc hd mx my loc agree ultra ⟨N, V, K₀, target, ready⟩
  exact ⟨β, U, Q', G', E', b, j, p, N, V, K₀, built, extension, hb, edge, hu, payload, move, target, ready, nb, nh, np, nc, ns⟩

end YesMetaZFC.SetTheory.LargeCardinal
