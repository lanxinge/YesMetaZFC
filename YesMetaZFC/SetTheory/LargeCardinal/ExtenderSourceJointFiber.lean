import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceLevels
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSupport
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLocalRead
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLevelTransfer
import YesMetaZFC.SetTheory.LargeCardinal.JointFiber

/-! # 所属模型的共同纤维实现施加源中的全部可数约束

先在施加源构造单射支撑列及约束层族。有限 κ 幂子集的一致性将层族送回
所属模型，其原内部共同纤维条件遂给出同一个 κ 值列，实现所有有限支撑约束。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem es_source_joint_fiber_l {ω κ K X R K' Y R' L F V S P A B : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y R')
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (branches : Sc_branch_d ω Y) (loc : It_local_d ω Y κ L F)
    (hV : M.mem V Y) (power : FilterZF.Source_d Y K' V)
    (hP : M.mem P X) (hAX : M.mem A X) (hBX : M.mem B X)
    (seq : Fseq_space_d I ω L S) (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U) :
    ∃ f g, M.mem f X ∧ M.mem g Y ∧ M.IsSetInjectionFromTo I f ω L ∧ Fn0_d ω κ g ∧
      (∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f) ∧
      ∀ i a E, Rd_entry_d i a A → Rd_entry_d i E B → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L f g a r := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner hV power).transfer_l reverse
  have coherent := (loc.coherent_l hZF owner).transfer_l hZF reverse
  have ordinal := (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive).2
  have local_copy := loc
  obtain ⟨_, _, hL, _, pre⟩ := local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω L := fun x hx => ordinal.transitive κ pre.1.2.2.2.2.1 x (source.below x hx)
  obtain ⟨f, hfX, hf, covered⟩ := ec_source_cover_l hZF source (inside L hL) below hAX seq fa
  obtain ⟨H, hH, levels, fiber, read⟩ := ec_source_levels_l hZF source family coherent (inside L hL) hP hAX hBX hfX seq fa fb large hf
  obtain ⟨g, hgY, hg⟩ := It_local_d.source_fiber_l hZF source owner inside agree branches loc hH levels fiber
  exact ⟨f, g, hfX, hgY, hf, hg.1, covered, ec_levels_realize_l hZF source.omega seq fa hf covered hg read⟩

end YesMetaZFC.SetTheory.LargeCardinal
