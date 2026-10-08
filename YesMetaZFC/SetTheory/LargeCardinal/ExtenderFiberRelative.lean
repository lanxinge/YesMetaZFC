import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiberBranch
import YesMetaZFC.SetTheory.LargeCardinal.IterationStep
import YesMetaZFC.Model.SetTheory.Internal.TransitiveSource

/-! # 节点内部的共同纤维条件及实际源内见证

层族与两类纤维按原公式读取。测度像纤维先由源的枝反射回收，
内部短扩展器的存在量词再给出源内实际 κ 值共同纤维。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private theorem fr_fn_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X hn) d) (A B f : Term d) :
    Formula.satisfies ρ (fn0_m A B f) ↔ Fn0_d (A.eval ρ).val (B.eval ρ).val (f.eval ρ).val := by
  simpa only [eval_image_env_l (M := rt_model_l X hn) (N := M) Subtype.val] using
    (rt_model_delta_l hX hn (fn0_delta_l A B f) ρ).trans (fn0_sat_l hE ..)

private theorem fr_entry_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X hn) d) (a b f : Term d) :
    Formula.satisfies ρ (rd_entry0_m a b f) ↔ Rd_entry_d (a.eval ρ).val (b.eval ρ).val (f.eval ρ).val := by
  simpa only [eval_image_env_l (M := rt_model_l X hn) (N := M) Subtype.val] using
    (rt_model_delta_l hX hn (rd_entry0_delta_l a b f) ρ).trans (rd_entry0_sat_l hE ..)

private theorem fr_sub_l {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X hn) d) (a b : Term d) :
    Formula.satisfies ρ (Formula.subset a b) ↔ M.MemberSubset (a.eval ρ).val (b.eval ρ).val := by
  simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l X hn) (N := M) Subtype.val] using
    (rt_model_delta_l hX hn (.atom ..) ρ).trans (Formula.satisfies_subset_iff _ a b)

private theorem fr_pair_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X hn) d) (a b f : Term d) :
    Formula.satisfies ρ (Formula.orderedPairMem kpair_convention_l a b f) ↔
      Rd_entry_d (a.eval ρ).val (b.eval ρ).val (f.eval ρ).val :=
  (rd_entry_sat_l (rt_model_ext_l hE hX hn) ρ a b f).trans
    ((rd_entry0_sat_l (rt_model_ext_l hE hX hn) ρ a b f).symm.trans (fr_entry_l hE hX hn ρ a b f))

theorem ef_levels_relative_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (algebra : Sc_algebra_d X) (hn : Nonempty {x // M.mem x X}) {d}
    (ρ : Env (rt_model_l X hn) d) (ω κ H : Term d) :
    Formula.satisfies ρ (ef_levels_m ω κ H) ↔ Ef_levels_d (ω.eval ρ).val (κ.eval ρ).val (H.eval ρ).val := by
  simp only [ef_levels_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_forallMem_iff,
    fr_fn_l hE hX hn, fr_entry_l hE hX hn, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨⟨P, fn⟩, all⟩
    refine ⟨⟨P.val, fn⟩, fun n A h s hs => ?_⟩
    have mem := rd_entry_transitive_l hX (H.eval ρ).property h
    exact all ⟨n, mem.1⟩ ⟨A, mem.2⟩ h ⟨s, hX A mem.2 s hs⟩ hs
  · rintro ⟨⟨P, fn⟩, all⟩
    obtain ⟨B, hB, bound⟩ := algebra.envelope_l (H.eval ρ).property
    exact ⟨⟨⟨B, hB⟩, fn.retarget_l (fun n A h => (bound n A h).2)⟩,
      fun n A h s hs => all n.val A.val h s.val hs⟩

theorem es_fiber_relative_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X hn) d) (ω L F H f : Term d) :
    Formula.satisfies ρ (es_fiber_m (𝒞 := kpair_convention_l) ω L F H f) ↔
      Es_fiber_d (kp_pair_l hKP) (ω.eval ρ).val (L.eval ρ).val (F.eval ρ).val (H.eval ρ).val (f.eval ρ).val := by
  simp only [es_fiber_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, fr_fn_l hKP.1 hX hn, fr_entry_l hKP.1 hX hn,
    fr_sub_l hX hn, fr_pair_l hKP.1 hX hn, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨fn, all⟩
    refine ⟨fn, fun n h => ?_⟩
    obtain ⟨A, a, U, hA, ha, sub, hu, hAU⟩ := all ⟨n, hX _ (ω.eval ρ).property n h⟩ h
    exact ⟨A.val, a.val, U.val, hA, ha, sub, hu, hAU⟩
  · rintro ⟨fn, all⟩
    refine ⟨fn, fun n h => ?_⟩
    obtain ⟨A, a, U, hA, ha, sub, hu, hAU⟩ := all n.val h
    have hm := rd_entry_transitive_l hX (F.eval ρ).property hu
    exact ⟨⟨A, (rd_entry_transitive_l hX (H.eval ρ).property hA).2⟩, ⟨a, hm.1⟩, ⟨U, hm.2⟩, hA, ha, sub, hu, hAU⟩

theorem ef_fiber_relative_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) {d} (ρ : Env (rt_model_l X hn) d) (ω κ H f : Term d) :
    Formula.satisfies ρ (ef_fiber_m ω κ H f) ↔ Ef_fiber_d (ω.eval ρ).val (κ.eval ρ).val (H.eval ρ).val (f.eval ρ).val := by
  simp only [ef_fiber_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, fr_fn_l hE hX hn, fr_entry_l hE hX hn,
    fr_sub_l hX hn, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨fn, all⟩
    refine ⟨fn, fun n h => ?_⟩
    obtain ⟨A, s, ha, hs, fn, sub⟩ := all ⟨n, hX _ (ω.eval ρ).property n h⟩ h
    exact ⟨A.val, s.val, ha, hs, fn, sub⟩
  · rintro ⟨fn, all⟩
    refine ⟨fn, fun n h => ?_⟩
    obtain ⟨A, s, ha, hs, fn, sub⟩ := all n.val h
    have hA := (rd_entry_transitive_l hX (H.eval ρ).property ha).2
    exact ⟨⟨A, hA⟩, ⟨s, hX A hA s hs⟩, ha, hs, fn, sub⟩

/-- 已有源内层族与像纤维时，原公式直接给出源内共同纤维。 -/
theorem ex_owned_fiber_l (hZF : M.Models ZF) {ω X κ L F H f : M.Domain}
    (ht : M.TransitiveSet X) (algebra : Sc_algebra_d X) (hw : M.mem ω X)
    (hκ : M.mem κ X) (hL : M.mem L X) (hF : M.mem F X)
    (countable : Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hw⟩))), fun _ => ⟨ω, hw⟩⟩ :
        Env (rt_model_l X ⟨⟨ω, hw⟩⟩) 4) (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest))
    (hH : M.mem H X) (hf : M.mem f X) (levels : Ef_levels_d ω κ H) (fiber : Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f) :
    ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  let hn : Nonempty {x // M.mem x X} := ⟨⟨ω, hw⟩⟩
  let ρ : Env (rt_model_l X hn) 4 :=
    ⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hw⟩))), fun _ => ⟨ω, hw⟩⟩
  have bound := (ef_levels_relative_l hZF.1 ht algebra hn
    ((ρ.push ⟨H, hH⟩).push ⟨f, hf⟩) (.bound 5) (.bound 4) (.bound 1)).mpr levels
  have image := (es_fiber_relative_l (ZF.modelsKP hZF) ht hn
    ((ρ.push ⟨H, hH⟩).push ⟨f, hf⟩) (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest).mpr fiber
  simp only [ex_countable_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff] at countable
  obtain ⟨g, hg⟩ := countable ⟨H, hH⟩ ⟨f, hf⟩ bound image
  exact ⟨g.val, g.property, (ef_fiber_relative_l hZF.1 ht hn
    (((ρ.push ⟨H, hH⟩).push ⟨f, hf⟩).push g) (.bound 6) (.bound 5) (.bound 2) .newest).mp hg⟩

/-- 外部像纤维先经实际尝试树回收，然后调用同一个源内存在步骤。 -/
theorem Ep_source_d.internal_fiber_l (hZF : M.Models ZF) {ω μ K X R κ L F H f : M.Domain}
    (source : Ep_source_d hZF ω μ K X R) (branches : Sc_branch_d ω X)
    (hκ : M.mem κ X) (hL : M.mem L X) (hF : M.mem F X)
    (countable : Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, source.omega_mem⟩))), fun _ => ⟨ω, source.omega_mem⟩⟩ :
        Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4) (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest))
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) (fiber : Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f) :
    ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  obtain ⟨v, hv, vf⟩ := source.fiber_branch_l hZF branches hL hF hH fiber
  exact ex_owned_fiber_l hZF source.transitive source.theory.algebra source.omega_mem hκ hL hF countable hH hv levels vf

theorem It_local_d.fiber_l (hZF : M.Models ZF) {ω μ K X R κ L F H f : M.Domain}
    (source : Ep_source_d hZF ω μ K X R) (branches : Sc_branch_d ω X) (loc : It_local_d ω X κ L F)
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) (fiber : Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f) :
    ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  obtain ⟨_, hκ, hL, hF, sat⟩ := loc
  have countable := ((Formula.satisfies_conj_iff _ _ _).mp sat).2
  exact source.internal_fiber_l hZF branches hκ hL hF countable hH levels fiber

/-- 节点内部的序数仍是背景序数；不把内部基数性提升到背景。 -/
theorem It_local_d.ordinals_l (hKP : M.Models KP) {ω X κ L F : M.Domain}
    (hX : M.TransitiveSet X) (loc : It_local_d ω X κ L F) : M.IsOrdinal κ ∧ M.IsOrdinal L := by
  obtain ⟨hω, hκ, hL, hF, sat⟩ := loc
  let hn : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  have pre := ((Formula.satisfies_conj_iff _ _ _).mp sat).1
  simp only [ex_pre_m, Formula.satisfies_conj_iff] at pre
  have card := pre.2.1
  rw [Formula.isCardinal, Formula.satisfies_conj_iff] at card
  exact ⟨(rt_ordinal_iff_l hX hn hKP ⟨κ, hκ⟩).mp ((Formula.satisfies_isOrdinal_iff _ _).mp card.1),
    (rt_ordinal_iff_l hX hn hKP ⟨L, hL⟩).mp ((Formula.satisfies_isOrdinal_iff _ _).mp pre.2.2.2.1)⟩

end YesMetaZFC.SetTheory.LargeCardinal
