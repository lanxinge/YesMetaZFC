import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceTrace
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLocalRead
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceLimit

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
    (source : Ep_source_d hZF ω κ K X R) (hP : M.mem P X) (power : FilterZF.Source_d X K P)
    (loc : It_local_d ω X κ L F) (next : Ep_successor_d hZF ω κ L X R F N S) : Ea_subset_d ω L N X := by
  have family := loc.measures_l hZF source hP power
  have coherent := loc.coherent_l hZF source
  have atoms := loc.atoms_l hZF source
  have normal := loc.normal_l hZF source
  have ord := loc.ordinals_l (ZF.modelsKP hZF) source.transitive
  obtain ⟨_, _, hL, hF, pre⟩ := loc
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω L := fun x hx => ord.2.transitive κ pre.1.2.2.2.2.1 x (source.below x hx)
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e, system, limit, model, target, trans, wc, bij, he⟩ := next
  have fixed := (ep_seed_collapse_l hZF source ord.1.transitive ord.2.transitive below family coherent atoms normal
    system limit wc (fn0_of_function_l (ZF.modelsKP hZF) he.1.1)).2
  have range : M.IsRangeOf I N e := fun x => ⟨fun hx => (bij.2 x hx).imp fun _ h => h.2,
    fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩
  intro m D B hm hd sub hB
  exact ep_set_source_l hZFC source family coherent hL hF system limit model trans target he range fixed below hm hB
    (fun t ht => (hd t).mp (sub t ht))

/-- 指定的实际后继也能回收编码：与所属模型自身超幂比较，不另换调用者的目标。 -/
theorem It_local_d.return_l {ω κ K X R K' Y S L F N V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (agree : Ea_agree_d ω κ X Y) (branches : Sc_branch_d ω Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (loc : It_local_d ω Y κ L F) (next : Ep_successor_d hZF ω κ L X R F N V) : Ea_subset_d ω L N Y := by
  obtain ⟨P, hP, subsets⟩ := power K' owner.finite_mem
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
  obtain ⟨J, O, Z, A, p, T, U, q, c, C, W, d, e, h, limit, model, target, ht, wc, bij, he⟩ := next
  obtain ⟨J', O', Z', A', p', T', U', q', c', C', W', h', limit', model', _, _, collapse⟩ :=
    loc.limit_l hZFC owner owner branches cover power (fun _ h => h) (fun _ _ _ _ _ _ => Iff.rfl) branches hP subsets
  obtain ⟨_, _, _, N', e', _, d', V', _, _, _, _, ht', wc', bij', target', he', _⟩ := collapse
  have next' : Ep_successor_d hZF ω κ L Y S F N' V' :=
    ⟨J', O', Z', A', p', T', U', q', c', C', W', d', e', h', limit', model', target', ht', wc', bij', he'⟩
  have range : M.IsRangeOf I N e := fun x => ⟨fun hx => (bij.2 x hx).imp fun _ h => h.2,
    fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩
  have range' : M.IsRangeOf I N' e' := fun x => ⟨fun hx => (bij'.2 x hx).imp fun _ h => h.2,
    fun ⟨_, hx⟩ => bij'.1.1.output_mem_of_pairMember hx⟩
  have common := (ep_successor_agree_l hZFC source owner agree family coherent atoms normal ord.1 ord.2 below
    h limit model ht target he range wc h' limit' model' ht' target' he' range' wc').2.2
  exact common.subset_l.trans_l (loc.subsets_l hZFC owner hP subsets next')

end YesMetaZFC.SetTheory.LargeCardinal
