import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceJointFiber
import YesMetaZFC.Model.SetTheory.Internal.SourceOmegaClosed

/-! # 有界可数闭所属模型实现背景中的全部可数测度约束

所有有限支撑属于所属源，所有测度一集合也由测度图回收。
有界值域的 ω 闭性使两列参数同时属于该源，原内部共同纤维公式遂可直接使用。
这里不要求所属模型包含于另一个施加模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem es_closed_joint_fiber_l {ω κ K Y R L F V S P A B : M.Domain}
    (owner : Ep_source_d hZF ω κ K Y R) (closed : Sc_bounded_omega_closed_d ω Y)
    (loc : It_local_d ω Y κ L F) (hV : M.mem V Y) (power : FilterZF.Source_d Y K V)
    (seq : Fseq_space_d I ω L S) (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U) :
    ∃ f g, M.mem f Y ∧ M.mem g Y ∧ M.IsSetInjectionFromTo I f ω L ∧ Fn0_d ω κ g ∧
      (∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f) ∧
      ∀ i a E, Rd_entry_d i a A → Rd_entry_d i E B → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L f g a r := by
  have family := loc.measures_l hZF owner hV power
  have coherent := loc.coherent_l hZF owner
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive
  have local_copy := loc
  obtain ⟨hw, hk, hl, hf, pre⟩ := local_copy
  have countable := (Formula.satisfies_conj_iff _ _ _).mp pre |>.2
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω L := fun x hx => ord.2.transitive κ pre.1.2.2.2.2.1 x (owner.below x hx)
  obtain ⟨S', hs, seq'⟩ := owner.sequences.space L hl
  have eq := hZF.1.eq_of_same_members S' S (fun a => (seq' a).trans (seq a).symm)
  have hS := eq ▸ hs
  have hA := closed S hS A fa
  have values i E (hiE : Rd_entry_d i E B) : M.mem E V := by
    obtain ⟨a, ha, hia⟩ := fa.2.1 i (fb.bound_l hiE).1
    obtain ⟨n, hn, fn⟩ := (seq a).mp ha
    obtain ⟨U, hu⟩ := family.total n a hn (fn0_of_function_l (ZF.modelsKP hZF) fn)
    have hEU := large i a E U hia hiE hu
    have hU := (rd_entry_transitive_l owner.transitive hf hu).2
    obtain ⟨m, D, hm, _, space, ultra⟩ := family.measure a U hu
    exact (power E).mpr ⟨owner.transitive U hU E hEU, fun s hs => (owner.finite s).mpr
      ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) ((space s).mp (ultra.base.bounds E hEU s hs))⟩⟩
  have fbV := fb.retarget_l values
  have hB := closed V hV B fbV
  obtain ⟨f, hfy, ff, covered⟩ := ec_source_cover_l hZF owner hl below hA seq fa
  obtain ⟨H, hH, levels, fiber, read⟩ := ec_source_levels_l hZF owner family coherent hl hV hA hB hfy seq fa fbV large ff
  obtain ⟨g, hgy, hg⟩ := ex_owned_fiber_l hZF owner.transitive owner.theory.algebra hw hk hl hf countable hH hfy levels fiber
  exact ⟨f, g, hfy, hgy, ff, hg.1, covered, ec_levels_realize_l hZF owner.omega seq fa ff covered hg read⟩

end YesMetaZFC.SetTheory.LargeCardinal
