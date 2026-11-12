import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceTrace
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceLimit

/-! # 所属模型自身超幂的有界子集回收

内部原子条件和源内正规性识别实际坍塌中的全部支撑坐标。源内迹构造
随后把后继中的每个有限支撑幂子集送回原所属模型，供小模型编码塌缩使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.subsets_l {ω κ K X R L F P N S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hP : M.mem P X) (power : FilterZF.Source_d X K P)
    (loc : It_local_d I ω X R κ L F) (next : Ep_successor_d hZF ω κ L X R F N S) : Ea_subset_d ω L N X := by
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory (source.finite_l (ZF.modelsKP hZF)) hP power)
  have coherent := loc.coherent_l hZF (source.read_source_l hZF) source.code
  have atoms := loc.atoms_l hZF (source.read_source_l hZF) source.code
  have normal := loc.normal_l hZF (source.read_source_l hZF) source.code
  have ord := loc.ordinals_l (ZF.modelsKP hZF) source.transitive source.code
  obtain ⟨_, _, hL, hF, _⟩ := loc
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e, system, limit, model, target, trans, wc, bij, he⟩ := next
  have fixed := (ep_seed_collapse_l hZF source ord.1.transitive ord.2.transitive family coherent atoms normal
    system limit wc (fn0_of_function_l (ZF.modelsKP hZF) he.1.1)).2
  have range : M.IsRangeOf I N e := fun x => ⟨fun hx => (bij.2 x hx).imp fun _ h => h.2,
    fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩
  intro m D B hm hd sub hB
  exact ep_set_source_l hZFC source family coherent hL hF system limit model trans target he range fixed hm hB
    (fun t ht => (hd t).mp (sub t ht))

/-- 指定的实际后继也能回收编码：与所属模型自身超幂比较，不另换调用者的目标。 -/
theorem It_local_d.return_l {ω κ K X R K' Y S L F N V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (agree : Ea_agree_d ω κ X Y) (branches : Sc_branch_d ω Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (loc : It_local_d I ω Y S κ L F) (next : Ep_successor_d hZF ω κ L X R F N V) :
    Ea_subset_d ω L N Y ∧ ∃ b d N' V' j K₀,
      Smem_d I b Y S ∧ Smem_d I d N' V' ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d j ∧
      Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K₀ N' V' ∧ M.mem L N ∧ M.mem L N' ∧
      Ea_agree_d ω L N N' ∧ Ea_subset_d ω L N' Y := by
  obtain ⟨P, hP, subsets⟩ := power K' owner.finite.mem_l
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP subsets)).transfer_l reverse
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
  have atoms := loc.atoms_l hZF (owner.read_source_l hZF) owner.code
  have normal := (loc.normal_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF owner source agree.subset_l
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have local_copy := loc
  obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I owner.code).mp local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω L := fun x hx => ord.2.transitive κ pre.1.2.2.2.2.1 x (source.below x hx)
  obtain ⟨J, O, Z, A, p, T, U, q, c, C, W, d, e, h, limit, model, target, ht, wc, bij, he⟩ := next
  obtain ⟨J', O', Z', A', p', T', U', q', c', C', W', h', limit', model', _, _, collapse⟩ :=
    loc.limit_l hZFC owner owner branches cover power (fun _ h => h) (fun _ _ _ _ _ _ => Iff.rfl) branches hP subsets
  obtain ⟨_, b', i', N', e', _, d', V', j', code', hi', constants', ht', wc', bij', target', he', _, _, _, hj', js', K₀, ready'⟩ := collapse
  have next' : Ep_successor_d hZF ω κ L Y S F N' V' :=
    ⟨J', O', Z', A', p', T', U', q', c', C', W', d', e', h', limit', model', target', ht', wc', bij', he'⟩
  have range : M.IsRangeOf I N e := fun x => ⟨fun hx => (bij.2 x hx).imp fun _ h => h.2,
    fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩
  have range' : M.IsRangeOf I N' e' := fun x => ⟨fun hx => (bij'.2 x hx).imp fun _ h => h.2,
    fun ⟨_, hx⟩ => bij'.1.1.output_mem_of_pairMember hx⟩
  have common := ep_successor_agree_l hZFC source owner agree family coherent atoms normal ord.1 ord.2
    h limit model ht target he range wc h' limit' model' ht' target' he' range' wc'
  have back := loc.subsets_l hZFC owner hP subsets next'
  have ultra' : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b' d' j' :=
    ⟨Y, S, N', V', J', O', Z', A', p', T', U', q', c', C', W', i', e', code', target', h', limit', model',
      wc', bij', he', hi', constants', hj', hj'.1.1.1.1, fun x y => (js' x y).trans
        ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi'.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  exact ⟨common.2.2.subset_l.trans_l back, b', d', N', V', j', K₀, code', target', ultra', ready',
    common.1, common.2.1, common.2.2, back⟩

end YesMetaZFC.SetTheory.LargeCardinal
