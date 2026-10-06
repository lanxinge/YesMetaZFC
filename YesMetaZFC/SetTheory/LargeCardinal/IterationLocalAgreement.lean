import YesMetaZFC.SetTheory.LargeCardinal.IterationLocalApply
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSuccessors

/-! # 内部所属扩展器的两侧实际后继保持子集一致性

树前驱和所属模型分别施加原内部短扩展器。原子条件与源内正规性直接读取
所属判断，后者由原有限幂一致性传到树前驱；两侧实际坍塌在支撑端点上一致。
这些有界子集还返回原所属模型，直接提供下一步小模型编码所需的搬运方向。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_local_apply_agree_l {ω c₀ α ξ T Q G E k c d X R Y S κ K K' L F : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (owner : Ep_source_d hZF ω κ K X R) (source : Ep_source_d hZF ω κ K' Y S)
    (branches : Sc_branch_d ω Y) (hierarchy : Sc_hierarchy_d Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Y) (inside : M.MemberSubset X Y) (agree : Ea_agree_d ω κ X Y)
    (ob : Sc_branch_d ω X) (oh : Sc_hierarchy_d X) (op : Sc_power_d X) (oc : Sc_cover_d X)
    (os : Sh_source_d (ZF.modelsKP hZF) ω X) (loc : It_local_d ω X κ L F) :
    ∃ β U Q' G' E' b j b' j' N V N' V' K₀ K₁,
      It_tree_d hZF ω c₀ β U Q' G' E' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d hZF ω κ L F d b j ∧ It_ultra_d hZF ω κ L F c b' j' ∧
      Smem_d I b N V ∧ Smem_d I b' N' V' ∧ M.mem L N ∧ M.mem L N' ∧ Ea_agree_d ω L N N' ∧
      Ea_subset_d ω L N X ∧
      Ep_source_d hZF ω L K₀ N V ∧ Ep_source_d hZF ω L K₁ N' V' ∧
      Sc_branch_d ω N ∧ Sc_branch_d ω N' ∧ Sc_hierarchy_d N ∧ Sc_hierarchy_d N' ∧
      Sc_power_d N ∧ Sc_power_d N' ∧ Sc_cover_d N ∧ Sc_cover_d N' ∧
      Sh_source_d (ZF.modelsKP hZF) ω N ∧ Sh_source_d (ZF.modelsKP hZF) ω N' := by
  obtain ⟨N, V, N', V', a, b, j, a', b', j', K₀, K₁, code, code', target, target', ultra, ultra', hLN, hLN', common,
      back, ready, ready', nb, nb', nh, nh', np, np', nc, nc', ns, ns'⟩ :=
    loc.successors_l hZFC source owner branches hierarchy power cover small inside
      (fun n D A hn hd sub => (agree n D A hn hd sub).symm) ob oh op oc os
  have eq := (smem_unique_l I hZF.1 code my).1
  have eq' := (smem_unique_l I hZF.1 code' mx).1
  subst a a'
  obtain ⟨K₂, omega_source⟩ := ready.rebase_l hZF ready.omega_mem (fun _ h => h) (ready.cardinal_small.mono_l ready.below)
  obtain ⟨β, U, Q', G', E', _, built, extension, hb, edge, _, _, _⟩ :=
    it_apply_l hZF tree hα hc hd mx my loc agree ultra ⟨N, V, K₂, target, omega_source⟩
  exact ⟨β, U, Q', G', E', b, j, b', j', N, V, N', V', K₀, K₁, built, extension, hb, edge, ultra, ultra', target, target',
    hLN, hLN', common, back, ready, ready', nb, nb', nh, nh', np, np', nc, nc', ns, ns'⟩

end YesMetaZFC.SetTheory.LargeCardinal
