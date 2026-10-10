import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceNode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSubsets
import YesMetaZFC.SetTheory.LargeCardinal.IterationAgreement

/-! # 同一内部扩展器的两侧后继及向原所属模型的编码搬运

两侧超幂均由内部所属判断实际构造，完整节点不变量同步保留。后继间的
支撑子集一致性与所属模型的自身迹计算复合，给出下降模型构造所需的单向包含。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.successors_l {ω κ K X R K' Y S L F : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (branches : Sc_branch_d ω X) (hierarchy : Sc_hierarchy_d X) (power : Sc_power_d X) (cover : Sc_cover_d X)
    (small : Sh_source_d (ZF.modelsKP hZF) ω X) (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (ob : Sc_branch_d ω Y) (oh : Sc_hierarchy_d Y) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (os : Sh_source_d (ZF.modelsKP hZF) ω Y) (loc : It_local_d ω Y κ L F) :
    ∃ N V N' V' b d j b' d' j' K₀ K₁,
      Smem_d I b X R ∧ Smem_d I b' Y S ∧ Smem_d I d N V ∧ Smem_d I d' N' V' ∧
      It_ultra_d hZF ω κ L F b d j ∧ It_ultra_d hZF ω κ L F b' d' j' ∧
      M.mem L N ∧ M.mem L N' ∧ Ea_agree_d ω L N N' ∧ Ea_subset_d ω L N Y ∧
      Ep_source_d hZF ω L K₀ N V ∧ Ep_source_d hZF ω L K₁ N' V' ∧
      Sc_branch_d ω N ∧ Sc_branch_d ω N' ∧ Sc_hierarchy_d N ∧ Sc_hierarchy_d N' ∧
      Sc_power_d N ∧ Sc_power_d N' ∧ Sc_cover_d N ∧ Sc_cover_d N' ∧
      Sh_source_d (ZF.modelsKP hZF) ω N ∧ Sh_source_d (ZF.modelsKP hZF) ω N' := by
  obtain ⟨P, hP, subsets⟩ := op K' owner.finite_mem
  obtain ⟨N, V, b, d, j, _, _, ultra, code, target, _, next, nb, nh, np, nc, ns⟩ :=
    loc.node_l hZFC source owner branches hierarchy power cover small inside agree ob hP subsets
  obtain ⟨N', V', b', d', j', _, successor', ultra', code', target', _, next', nb', nh', np', nc', ns'⟩ :=
    loc.node_l hZFC owner owner ob oh op oc os (fun _ h => h) (fun _ _ _ _ _ _ => Iff.rfl) ob hP subsets
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner hP subsets).transfer_l reverse
  have coherent := (loc.coherent_l hZF owner).transfer_l hZF reverse
  have atoms := loc.atoms_l hZF owner
  have normal := (loc.normal_l hZF owner).transfer_l hZF owner source agree.subset_l
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive
  have local_copy := loc
  obtain ⟨_, _, _, _, pre⟩ := local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω L := fun x hx => ord.2.transitive κ pre.1.2.2.2.2.1 x (source.below x hx)
  obtain ⟨hLN, hLN', common⟩ := it_ultra_agree_l hZFC source owner agree family coherent atoms normal ord.1 ord.2 below
    code code' target target' next.transitive next'.transitive ultra ultra'
  obtain ⟨K₀, ready⟩ := next.rebase_l hZF hLN below (sc_ordinal_small_l hZF source.omega next.transitive target next.theory hLN ord.2)
  obtain ⟨K₁, ready'⟩ := next'.rebase_l hZF hLN' below (sc_ordinal_small_l hZF owner.omega next'.transitive target' next'.theory hLN' ord.2)
  exact ⟨N, V, N', V', b, d, j, b', d', j', K₀, K₁, code, code', target, target', ultra, ultra', hLN, hLN', common,
    common.subset_l.trans_l (loc.subsets_l hZFC owner hP subsets successor'), ready, ready', nb, nb', nh, nh', np, np', nc, nc', ns, ns'⟩

end YesMetaZFC.SetTheory.LargeCardinal
