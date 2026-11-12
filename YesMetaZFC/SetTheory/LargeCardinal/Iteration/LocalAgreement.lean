import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Fork
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceNode
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthAgreement
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceSuccessors

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

theorem it_local_apply_l {ω c₀ α ξ T Q G E k c d X R Y S κ μ K K' L F P : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (branches : Sc_branch_d ω Y) (hierarchy : Sc_hierarchy_d Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Y) (inside : M.MemberSubset X Y) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω X) (hP : M.mem P X) (owner_power : FilterZF.Source_d X K P)
    (loc : It_local_d I ω X R κ L F) : ∃ β U Q' G' E' b j p N V K₀,
      It_tree_d hZF ω c₀ β U Q' G' E' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F d b j ∧
      It_payload_d p κ L F ∧ Rd_entry_d ξ p E' ∧ Smem_d I b N V ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K₀ N V ∧
      Sc_branch_d ω N ∧ Sc_hierarchy_d N ∧ Sc_power_d N ∧ Sc_cover_d N ∧ Sh_source_d (ZF.modelsKP hZF) ω N := by
  obtain ⟨_, source⟩ := agree.subset_l.alphabet_l hZF owner source (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code).1
  obtain ⟨N, V, a, b, j, K₀, _, ultra, code, target, _, ready, nb, nh, np, nc, ns⟩ :=
    loc.node_l hZFC source owner branches hierarchy power cover small inside
      (fun n D A hn hd sub => (agree n D A hn hd sub).symm) owner_branches hP owner_power
  have eq := (smem_unique_l I hZF.1 code my).1
  subst a
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory
      (owner.finite_l (ZF.modelsKP hZF)) hP owner_power)).transfer_l agree
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF agree
  obtain ⟨p, payload, active⟩ := ultra.active_l hZF (owner.read_source_l hZF) mx owner.theory
    source my loc agree family coherent
  obtain ⟨β, U, Q', G', E', built, extension, hb, edge, payload', move⟩ :=
    it_apply_l hZF active tree hα hc hd (it_source_mem_l hZF target ready)
  exact ⟨β, U, Q', G', E', b, j, p, N, V, K₀, built, extension, hb, edge, ultra,
    payload, payload', target, ready, nb, nh, np, nc, ns⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 内部所属扩展器的两侧实际后继保持子集一致性

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

theorem it_local_apply_agree_l {ω c₀ α ξ T Q G E k c d X R Y S κ μ K K' L F : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (branches : Sc_branch_d ω Y) (hierarchy : Sc_hierarchy_d Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (small : Sh_source_d (ZF.modelsKP hZF) ω Y) (inside : M.MemberSubset X Y) (agree : Ea_agree_d ω κ X Y)
    (ob : Sc_branch_d ω X) (oh : Sc_hierarchy_d X) (op : Sc_power_d X) (oc : Sc_cover_d X)
    (os : Sh_source_d (ZF.modelsKP hZF) ω X) (loc : It_local_d I ω X R κ L F) :
    ∃ β U Q' G' E' b j b' j' N V N' V' K₀ K₁,
      It_tree_d hZF ω c₀ β U Q' G' E' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F d b j ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c b' j' ∧
      Smem_d I b N V ∧ Smem_d I b' N' V' ∧ M.mem L N ∧ M.mem L N' ∧ Ea_agree_d ω L N N' ∧
      Ea_subset_d ω L N X ∧
      Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L K₀ N V ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L K₁ N' V' ∧
      Sc_branch_d ω N ∧ Sc_branch_d ω N' ∧ Sc_hierarchy_d N ∧ Sc_hierarchy_d N' ∧
      Sc_power_d N ∧ Sc_power_d N' ∧ Sc_cover_d N ∧ Sc_cover_d N' ∧
      Sh_source_d (ZF.modelsKP hZF) ω N ∧ Sh_source_d (ZF.modelsKP hZF) ω N' := by
  obtain ⟨_, source⟩ := agree.subset_l.alphabet_l hZF owner source (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code).1
  obtain ⟨N, V, N', V', a, b, j, a', b', j', K₀, K₁, code, code', target, target', ultra, ultra', hLN, hLN', common,
      back, ready, ready', nb, nb', nh, nh', np, np', nc, nc', ns, ns'⟩ :=
    loc.successors_l hZFC source owner branches hierarchy power cover small inside
      (fun n D A hn hd sub => (agree n D A hn hd sub).symm) ob oh op oc os
  have eq := (smem_unique_l I hZF.1 code my).1
  have eq' := (smem_unique_l I hZF.1 code' mx).1
  subst a a'
  obtain ⟨K₂, omega_source⟩ := ready.rebase_l ready.omega_mem (fun _ h => h) (ready.cardinal_small.mono_mem_l I target ready.omega_mem ready.below)
  obtain ⟨P, hP, subsets⟩ := op K owner.finite.mem_l
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory
      (owner.finite_l (ZF.modelsKP hZF)) hP subsets)).transfer_l agree
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF agree
  obtain ⟨_, _, active⟩ := ultra.active_l hZF (owner.read_source_l hZF) mx owner.theory
    source my loc agree family coherent
  obtain ⟨β, U, Q', G', E', built, extension, hb, edge, _, _⟩ :=
    it_apply_l hZF active tree hα hc hd (it_source_mem_l hZF target omega_source)
  exact ⟨β, U, Q', G', E', b, j, b', j', N, V, N', V', K₀, K₁, built, extension, hb, edge, ultra, ultra', target, target',
    hLN, hLN', common, back, ready, ready', nb, nb', nh, nh', np, np', nc, nc', ns, ns'⟩

end YesMetaZFC.SetTheory.LargeCardinal
