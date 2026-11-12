import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SourceProjection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.Model.SetTheory.Source.Relation

/-! # 把测度像的外部共同纤维回收到所属源

尝试树检查每个有限前缀对应的原测度是否包含指定层。
只要求层族与测度图属于源；原无限支撑列无需预先属于源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.fiber_branch_l {ω κ K X R L F H f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (branches : Sc_branch_d ω X)
    (hL : M.mem L X) (hF : M.mem F X) (hH : M.mem H X) (fiber : Es_fiber_d I ω L F H f) :
    ∃ g, M.mem g X ∧ Es_fiber_d I ω L F H g := by
  obtain ⟨J, hJ, seq⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 L hL
  obtain ⟨P, hP, hp⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hH
  obtain ⟨Q, hQ, hq⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hF
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 7 := ⟨Fin.cases ω (Fin.cases J (Fin.cases L (Fin.cases H
    (Fin.cases F (Fin.cases P (fun _ => Q)))))), fun _ => ω⟩
  let φ : UnarySchema 7 := { body := Formula.forallMem (.bound 1) (Formula.forallMem (.bound 3)
    (.imp (fn0_m (.bound 1) (.bound 5) .newest) (.imp (Formula.subset .newest (.bound 2))
      (Formula.existsMem (.bound 8) (Formula.existsMem (.bound 10) (.conj
        (rd_entry0_m (.bound 3) (.bound 1) (.bound 8)) (.conj
          (rd_entry0_m (.bound 2) .newest (.bound 9)) (.mem (.bound 1) .newest)))))))) }
  have read s : φ.denote ρ s ↔ ∀ n, M.mem n ω → ∀ a, M.mem a J → Fn0_d n L a → M.MemberSubset a s →
      ∃ A, M.mem A P ∧ ∃ U, M.mem U Q ∧ Rd_entry_d n A H ∧ Rd_entry_d a U F ∧ M.mem A U := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      fn0_sat_l hZF.1, Formula.satisfies_subset_iff, Formula.satisfies_existsMem_iff,
      Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨T, hT, ts⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.forallMem _ (.forallMem _ (.imp (fn0_delta_l ..) (.imp (.atom ..)
      (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.mem _ _)))))))))
    ρ (Fin.cases source.omega_mem (Fin.cases hJ (Fin.cases hL (Fin.cases hH
      (Fin.cases hF (Fin.cases hP (fun _ => hQ))))))) hJ
  have tree : Tree_d J T := ⟨fun s hs => ((ts s).mp hs).1, fun s hs t ht sub =>
    (ts t).mpr ⟨ht, (read t).mpr fun n hn a ha fn has =>
      (read s).mp ((ts s).mp hs).2 n hn a ha fn (fun p hp => sub p (has p hp))⟩⟩
  have fn := fn0_function_l (ZF.modelsKP hZF) fiber.1
  have branch : Branch_d J T f := by
    intro s hs sub
    refine (ts s).mpr ⟨hs, (read s).mpr fun n hn a _ ha has => ?_⟩
    obtain ⟨A, b, U, hnA, hb, hbf, hbU, hAU⟩ := fiber.2 n hn
    have eq : b = a := ((ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) hb) fn.1).mpr hbf).eq hZF.1
      ((ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) ha) fn.1).mpr (fun p hp => sub p (has p hp)))
    exact ⟨A, (hp n A hnA).2, U, (hq b U hbU).2, hnA, eq ▸ hbU, hAU⟩
  obtain ⟨g, hg, gf, gb⟩ := source.tree_branch_l hZF branches hL hT seq tree fn branch
  refine ⟨g, hg, fn0_of_function_l (ZF.modelsKP hZF) gf, fun n hn => ?_⟩
  obtain ⟨a, af, ag, _⟩ := ds_prefix_l I hZF source.omega gf hn
  have ha := (seq a).mpr ⟨n, hn, af⟩
  have sub := (ds_restrict_iff_l I af gf.1).mp ag
  obtain ⟨A, _, U, _, hnA, haU, hAU⟩ := (read a).mp ((ts a).mp (gb a ha sub)).2 n hn a ha
    (fn0_of_function_l (ZF.modelsKP hZF) af) (fun _ h => h)
  exact ⟨A, a, U, hnA, fn0_of_function_l (ZF.modelsKP hZF) af, sub, haU, hAU⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 节点内部的共同纤维条件及实际源内见证

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (branches : Sc_branch_d ω X)
    (hκ : M.mem κ X) (hL : M.mem L X) (hF : M.mem F X)
    (countable : Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, source.omega_mem⟩))), fun _ => ⟨ω, source.omega_mem⟩⟩ :
        Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4) (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest))
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) (fiber : Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f) :
    ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  obtain ⟨v, hv, vf⟩ := source.fiber_branch_l hZF branches hL hF hH fiber
  exact ex_owned_fiber_l hZF source.transitive (source.algebra_l (ZF.modelsKP hZF)) source.omega_mem hκ hL hF countable hH hv levels vf

theorem It_local_d.fiber_l (hZF : M.Models ZF) {ω μ K X R κ L F H f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (branches : Sc_branch_d ω X) (loc : It_local_d (kp_pair_l (ZF.modelsKP hZF)) ω X R κ L F)
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) (fiber : Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f) :
    ∃ g, M.mem g X ∧ Ef_fiber_d ω κ H g := by
  obtain ⟨_, hκ, hL, hF, sat⟩ := (it_local_mem_l (kp_pair_l (ZF.modelsKP hZF)) source.code).mp loc
  have countable := ((Formula.satisfies_conj_iff _ _ _).mp sat).2
  exact source.internal_fiber_l hZF branches hκ hL hF countable hH levels fiber

/-- 节点内部的序数仍是背景序数；不把内部基数性提升到背景。 -/
theorem It_local_d.ordinals_l (hKP : M.Models KP) {ω X R κ L F : M.Domain}
    (hX : M.TransitiveSet X) (code : ∃ c, Smem_d (kp_pair_l hKP) c X R) (loc : It_local_d (kp_pair_l hKP) ω X R κ L F) : M.IsOrdinal κ ∧ M.IsOrdinal L := by
  obtain ⟨hω, hκ, hL, hF, sat⟩ := (it_local_mem_l (kp_pair_l hKP) code).mp loc
  let hn : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  have pre := ((Formula.satisfies_conj_iff _ _ _).mp sat).1
  simp only [ex_pre_m, Formula.satisfies_conj_iff] at pre
  have card := pre.2.1
  rw [Formula.isCardinal, Formula.satisfies_conj_iff] at card
  exact ⟨(rt_ordinal_iff_l hX hn hKP ⟨κ, hκ⟩).mp ((Formula.satisfies_isOrdinal_iff _ _).mp card.1),
    (rt_ordinal_iff_l hX hn hKP ⟨L, hL⟩).mp ((Formula.satisfies_isOrdinal_iff _ _).mp pre.2.2.2.1)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一极限秩源中的短扩展器向所属模型提升

全部候选都由原秩历史界定。有限图、测度族和可数层族回到同一个源中，
故原短扩展器在所属模型的全部对象上成立；所属模型只用 KP。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

private theorem ex_maximal_up_l {δ X : M.Domain} (rank : V_d I δ X) (limit : M.IsLimitOrdinal δ)
    (nx : Nonempty {x // M.mem x X}) (D U : (rt_model_l X nx).Domain)
    (h : Maximal_d D U) : Maximal_d D.val U.val := by
  let N := rt_model_l X nx
  have ht := v_transitive_l I rank
  have sub (A B : N.Domain) : N.MemberSubset A B ↔ M.MemberSubset A.val B.val :=
    ⟨fun h x hx => h ⟨x, ht A.val A.property x hx⟩ hx, fun h x hx => h x.val hx⟩
  have own A (s : M.MemberSubset A D.val) := v_subset_mem_l I rank D.property s
  refine ⟨⟨fun A hA => (sub ⟨A, ht U.val U.property A hA⟩ D).mp (h.1.1 _ hA), h.1.2.1, ?_, ?_⟩, ?_, ?_⟩
  · intro A B hA ab bd
    exact h.1.2.2.1 ⟨A, ht U.val U.property A hA⟩ ⟨B, own B bd⟩ hA
      ((sub _ _).mpr ab) ((sub _ _).mpr bd)
  · intro A B hA hB
    obtain ⟨C, hC, ca, cb⟩ := h.1.2.2.2 ⟨A, ht U.val U.property A hA⟩ ⟨B, ht U.val U.property B hB⟩ hA hB
    exact ⟨C.val, hC, (sub _ _).mp ca, (sub _ _).mp cb⟩
  · intro A hA
    obtain ⟨x, hx⟩ := h.2.1 ⟨A, ht U.val U.property A hA⟩ hA
    exact ⟨x.val, hx⟩
  · intro G filter proper ug
    obtain ⟨P, power⟩ := v_power_exists_l I hKP rank D.property
    have hG := v_subset_mem_l I rank (v_power_mem_l I rank limit D.property power)
      (fun A hA => (power A).mpr (filter.1 A hA))
    let g : N.Domain := ⟨G, hG⟩
    have fg : IsFilter_d D g := by
      refine ⟨fun A hA => (sub A D).mpr (filter.1 A.val hA), filter.2.1,
        fun A B hA ab bd => filter.2.2.1 A.val B.val hA ((sub A B).mp ab) ((sub B D).mp bd), ?_⟩
      intro A B hA hB
      obtain ⟨C, hC, ca, cb⟩ := filter.2.2.2 A.val B.val hA hB
      exact ⟨⟨C, ht G hG C hC⟩, hC, (sub _ A).mpr ca, (sub _ B).mpr cb⟩
    have pg : Proper_d g := fun A hA => by
      obtain ⟨x, hx⟩ := proper A.val hA
      exact ⟨⟨x, ht A.val A.property x hx⟩, hx⟩
    exact (sub g U).mp (h.2.2 g fg pg ((sub U g).mpr ug))

/-- 源中同一张扩展器图满足所属模型的完整短扩展器公式，包含全部可数层族。 -/
theorem It_local_d.rank_absolute_l {ω κ X R δ L F : M.Domain}
    (hω : M.IsOmega ω) (rank : V_d I δ X) (limit : M.IsLimitOrdinal δ)
    (code : ∃ c, Smem_d I c X R)
    (loc : It_local_d I ω X R κ L F) : Ex_short_d I ω κ L F := by
  obtain ⟨hw, hk, hl, hf, valid⟩ := (it_local_mem_l I code).mp loc
  have ht := v_transitive_l I rank
  have pairs := sc_v_pair_l hKP limit rank
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hw⟩⟩
  let N := rt_model_l X nx
  let J := rt_pair_l ht nx hKP.1 pairs
  let w : N.Domain := ⟨ω, hw⟩
  let k : N.Domain := ⟨κ, hk⟩
  let l : N.Domain := ⟨L, hl⟩
  let e : N.Domain := ⟨F, hf⟩
  let ρ : Env N 4 := ⟨Fin.cases e (Fin.cases l (Fin.cases k (fun _ => w))), fun _ => w⟩
  have en := rt_model_ext_l hKP.1 ht nx
  have small := (ex_short_sat_l J en ρ (.bound 3) (.bound 2) (.bound 1) .newest).mp valid
  have fn := rt_fn_l ht nx hKP.1
  have entry := rt_entry_l ht nx hKP.1
  have cp := rt_cp_l ht nx hKP.1
  have sub (A B : N.Domain) : N.MemberSubset A B ↔ M.MemberSubset A.val B.val :=
    ⟨fun h x hx => h ⟨x, ht A.val A.property x hx⟩ hx, fun h x hx => h x.val hx⟩
  have own {A B f} (hA : M.mem A X) (hB : M.mem B X) (ff : Fn0_d A B f) : M.mem f X := by
    obtain ⟨Y, hY, ay, by'⟩ := v_joint_bound_l I rank hA hB
    exact v_relation_mem_l I rank limit hY (fun p hp => (ff.1 p hp).elim fun a ha =>
      ha.2.elim fun b hb => ⟨a, ay a ha.1, b, by' b hb.1, hb.2⟩)
  -- 同一个关系图界容纳所有内部有限 κ 列，不要求预先给出有限列空间。
  obtain ⟨Y, hY, wy, ky⟩ := v_joint_bound_l I rank hw hk
  obtain ⟨G, hG, cover⟩ := v_relation_cover_l I rank limit hY
  have bounded n f (hn : M.mem n ω) (ff : Fn0_d n κ f) : M.mem f G :=
    cover f (fun p hp => (ff.1 p hp).elim fun i hi => hi.2.elim fun x hx =>
      ⟨i, wy i (hω.transitive hKP n hn i hi.1), x, ky x hx.1, hx.2⟩)
  have finite n f (hn : M.mem n ω) (ff : Fn0_d n κ f) : M.mem f X := ht G hG f (bounded n f hn ff)
  have family n A (hn : M.mem n ω) (all : ∀ f, M.mem f A → Fn0_d n κ f) : M.mem A X :=
    v_subset_mem_l I rank hG (fun f hf => bounded n f hn (all f hf))
  have ends a U (ha : Rd_entry_d a U F) := rd_entry_transitive_l ht hf ha
  have space (n D : N.Domain) (hn : N.mem n w) (ds : Ep_space_d k n D) : Ep_space_d κ n.val D.val :=
    fun f => ⟨fun h => (fn n k ⟨f, ht D.val D.property f h⟩).mp ((ds _).mp h),
      fun h => (ds ⟨f, finite n.val f hn h⟩).mpr ((fn n k _).mpr h)⟩
  refine ⟨⟨hω, ?_, small.uncountable, (rt_ordinal_iff_l ht nx hKP l).mp small.length,
    small.above, (rt_function_l ht nx hKP.1 (KP.exists_pair hKP) pairs e).mp small.graph,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨(rt_ordinal_iff_l ht nx hKP k).mp small.critical.1, ?_⟩
    rintro μ hμ ⟨f, ff⟩
    have hμX := ht κ hk μ hμ
    have hfX := own hμX hk (fn0_of_function_l hKP ff.1.1)
    exact small.critical.2 ⟨μ, hμX⟩ hμ ⟨⟨f, hfX⟩,
      (rt_bijection_l ht nx hKP.1 (KP.exists_pair hKP) pairs _ _ k).mpr ff⟩
  · refine ⟨fun n a hn ha => ?_, fun a U V hu hv => ?_, fun a U hu => ?_⟩
    · let n' : N.Domain := ⟨n, ht ω hw n hn⟩
      let a' : N.Domain := ⟨a, own n'.property hl ha⟩
      obtain ⟨U, hu⟩ := small.measures.total n' a' hn ((fn n' l a').mpr ha)
      exact ⟨U.val, (entry a' U e).mp hu⟩
    · exact congrArg Subtype.val (small.measures.function ⟨a, (ends a U hu).1⟩
        ⟨U, (ends a U hu).2⟩ ⟨V, (ends a V hv).2⟩ ((entry ..).mpr hu) ((entry ..).mpr hv))
    · let a' : N.Domain := ⟨a, (ends a U hu).1⟩
      let u : N.Domain := ⟨U, (ends a U hu).2⟩
      obtain ⟨n, D, hn, ha, ds, maximal⟩ := small.measures.measure a' u ((entry a' u e).mpr hu)
      exact ⟨n.val, D.val, hn, (fn n l a').mp ha, space n D hn ds, ex_maximal_up_l hKP rank limit nx D u maximal⟩
  · intro m n q a b U V A hm hn hq ha hb hav hbu all
    let m' : N.Domain := ⟨m, ht ω hw m hm⟩
    let n' : N.Domain := ⟨n, ht ω hw n hn⟩
    let q' : N.Domain := ⟨q, own m'.property n'.property hq⟩
    let a' : N.Domain := ⟨a, (ends a V hav).1⟩
    let b' : N.Domain := ⟨b, (ends b U hbu).1⟩
    let u : N.Domain := ⟨U, (ends b U hbu).2⟩
    let v : N.Domain := ⟨V, (ends a V hav).2⟩
    let A' : N.Domain := ⟨A, family m A hm all⟩
    obtain ⟨B, pull, decide⟩ := small.coherent m' n' q' a' b' u v A' hm hn
      ((fn ..).mpr hq) ((fn ..).mpr ha) ((cp ..).mpr hb) ((entry ..).mpr hav) ((entry ..).mpr hbu)
      (fun t ht => (fn m' k t).mpr (all t.val ht))
    refine ⟨B.val, fun s => ⟨fun hs => ?_, fun hs => ?_⟩, decide⟩
    · let s' : N.Domain := ⟨s, ht B.val B.property s hs⟩
      obtain ⟨ff, t, hA, ct⟩ := (pull s').mp hs
      exact ⟨(fn n' k s').mp ff, t.val, hA, (cp m' n' k q' s' t).mp ct⟩
    · obtain ⟨ff, t, hA, ct⟩ := hs
      exact (pull ⟨s, finite n s hn ff⟩).mpr ⟨(fn ..).mpr ff,
        ⟨t, ht A A'.property t hA⟩, hA, (cp ..).mpr ct⟩
  · intro n a U D ha hu ds μ hμ f ff
    let a' : N.Domain := ⟨a, (ends a U hu).1⟩
    let u : N.Domain := ⟨U, (ends a U hu).2⟩
    obtain ⟨m, _, hm, ma, _⟩ := small.measures.measure a' u ((entry a' u e).mpr hu)
    have eq := ((fn m l a').mp ma).domain_eq_l hKP.1 ha
    have hn : M.mem n ω := eq ▸ hm
    let n' : N.Domain := ⟨n, ht ω hw n hn⟩
    let D' : N.Domain := ⟨D, family n D hn (fun s hs => (ds s).mp hs)⟩
    let μ' : N.Domain := ⟨μ, ht κ hk μ hμ⟩
    let f' : N.Domain := ⟨f, own μ'.property u.property ff⟩
    obtain ⟨B, hB, spec⟩ := small.complete n' a' u D' ((fn ..).mpr ha) ((entry ..).mpr hu)
      (fun s => (ds s.val).trans (fn n' k s).symm) μ' hμ f' ((fn ..).mpr ff)
    have read (x : N.Domain) : M.mem x.val B.val ↔ M.mem x.val D ∧ Ed_all_d μ U f x.val := by
      let η : Env N 4 := ⟨Fin.cases x (Fin.cases f' (Fin.cases u (fun _ => μ'))), fun _ => μ'⟩
      exact (spec x).trans (and_congr Iff.rfl ((ed_all_sat_l en η (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((rt_model_delta_l ht nx (ed_all_delta_l ..) η).trans (ed_all_sat_l hKP.1 ..))))
    exact ⟨B.val, hB, fun x => ⟨fun hx => (read ⟨x, ht B.val B.property x hx⟩).mp hx,
      fun hx => (read ⟨x, ht D D'.property x hx.1⟩).mpr hx⟩⟩
  · intro p n a U i r β γ hn ha hu hi hr
    let n' : N.Domain := ⟨n, ht ω hw n hn⟩
    let a' : N.Domain := ⟨a, (ends a U hu).1⟩
    let u : N.Domain := ⟨U, (ends a U hu).2⟩
    have ib := rd_entry_transitive_l ht a'.property hi
    have rg := rd_entry_transitive_l ht a'.property hr
    let i' : N.Domain := ⟨i, ib.1⟩; let r' : N.Domain := ⟨r, rg.1⟩
    let β' : N.Domain := ⟨β, ib.2⟩; let γ' : N.Domain := ⟨γ, rg.2⟩
    obtain ⟨B, spec, decide⟩ := small.atoms p n' a' u i' r' β' γ' hn
      ((fn ..).mpr ha) ((entry ..).mpr hu) ((entry ..).mpr hi) ((entry ..).mpr hr)
    have read (s : N.Domain) : M.mem s.val B.val ↔ Fn0_d n κ s.val ∧ Ea_test_d p κ i r s.val := by
      let η : Env N 4 := ⟨Fin.cases s (Fin.cases r' (Fin.cases i' (fun _ => k))), fun _ => k⟩
      exact (spec s).trans (and_congr (fn n' k s) ((ea_test_sat_l en η p (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((rt_model_delta_l ht nx (ea_test_delta_l ..) η).trans (ea_test_sat_l hKP.1 ..))))
    refine ⟨B.val, fun s => ⟨fun hs => (read ⟨s, ht B.val B.property s hs⟩).mp hs,
      fun hs => (read ⟨s, finite n s hn hs.1⟩).mpr hs⟩, ?_⟩
    cases p with
    | false => exact decide
    | true => exact decide.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · intro n a U D f i β A hn ha hu ds ff hi hA reg
    let n' : N.Domain := ⟨n, ht ω hw n hn⟩
    let a' : N.Domain := ⟨a, (ends a U hu).1⟩
    let u : N.Domain := ⟨U, (ends a U hu).2⟩
    let D' : N.Domain := ⟨D, family n D hn (fun s hs => (ds s).mp hs)⟩
    let f' : N.Domain := ⟨f, own D'.property hk ff⟩
    have ib := rd_entry_transitive_l ht a'.property hi
    let i' : N.Domain := ⟨i, ib.1⟩; let β' : N.Domain := ⟨β, ib.2⟩
    let A' : N.Domain := ⟨A, ht U u.property A hA⟩
    obtain ⟨m, b, V, γ, B, hm, succ, fb, ab, last, lt, hbV, hBV, graph⟩ := small.normal n' a' u D' f' i' β' A' hn
      ((fn ..).mpr ha) ((entry ..).mpr hu) (fun s => (ds s.val).trans (fn n' k s).symm)
      ((fn ..).mpr ff) ((entry ..).mpr hi) hA
      (fun s hs x y fx iy => reg s.val hs x.val y.val ((entry ..).mp fx) ((entry ..).mp iy))
    refine ⟨m.val, b.val, V.val, γ.val, B.val, hm, (rt_successor_l ht nx hKP.1 m n').mp succ,
      (fn m l b).mp fb, (sub a' b).mp ab, (entry n' γ b).mp last, lt, (entry b V e).mp hbV, hBV, fun s hs => ?_⟩
    let s' : N.Domain := ⟨s, ht B.val B.property s hs⟩
    let η : Env N 5 := ⟨Fin.cases s' (Fin.cases f' (Fin.cases A' (Fin.cases k (fun _ => n')))), fun _ => n'⟩
    exact ((en_graph_sat_l en η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
      ((rt_model_delta_l ht nx (en_graph_delta_l ..) η).trans (en_graph_sat_l hKP.1 ..))).mp (graph s' hs)
  · intro n a U hn ha hu A
    let n' : N.Domain := ⟨n, ht ω hw n hn⟩
    let a' : N.Domain := ⟨a, (ends a U hu).1⟩
    let u : N.Domain := ⟨U, (ends a U hu).2⟩
    have read (B : N.Domain) := small.principal n' a' u hn ((fn ..).mpr ha) ((entry ..).mpr hu) B
    constructor
    · intro hA
      obtain ⟨all, haA⟩ := (read ⟨A, ht U u.property A hA⟩).mp hA
      exact ⟨fun s hs => (fn n' k ⟨s, ht A (ht U u.property A hA) s hs⟩).mp (all _ hs), haA⟩
    · rintro ⟨all, haA⟩
      exact (read ⟨A, family n A hn all⟩).mpr ⟨fun s hs => (fn n' k s).mpr (all s.val hs), haA⟩
  · intro a U i β hu hi hβ x s single hs
    let a' : N.Domain := ⟨a, (ends a U hu).1⟩
    let u : N.Domain := ⟨U, (ends a U hu).2⟩
    have ib := rd_entry_transitive_l ht a'.property hi
    let i' : N.Domain := ⟨i, ib.1⟩; let β' : N.Domain := ⟨β, ib.2⟩
    let s' : N.Domain := ⟨s, ht U u.property s hs⟩
    let x' : N.Domain := ⟨x, ht s s'.property x ((single x).mpr rfl)⟩
    exact small.nonprincipal a' u i' β' ((entry ..).mpr hu) ((entry ..).mpr hi) hβ x' s'
      (fun y => (single y.val).trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩) hs
  · -- 整个可数层族的值域是同一关系图界的子集族；先收纳值域，再收纳图。
    intro H f levels fiber
    obtain ⟨B, range⟩ := rd_fun_exists_l hKP .range H H H
    obtain ⟨P, power⟩ := v_power_exists_l I hKP rank hG
    have hB := v_subset_mem_l I rank (v_power_mem_l I rank limit hG power) (fun A hA => (power A).mpr (fun s hs => by
      obtain ⟨n, hn⟩ := (range A).mp hA
      obtain ⟨_, fn⟩ := levels.1
      exact bounded n s (fn.bound_l hn).1 (levels.2 n A hn s hs)))
    obtain ⟨_, fh⟩ := levels.1
    have hH := own hw hB (fh.retarget_l (fun n A hn => (range A).mpr ⟨n, hn⟩))
    have hf' := own hw hl fiber.1
    let H' : N.Domain := ⟨H, hH⟩
    let f' : N.Domain := ⟨f, hf'⟩
    have lv : Ef_levels_d w k H' := ⟨⟨⟨B, hB⟩,
      (fn w ⟨B, hB⟩ H').mpr (fh.retarget_l (fun n A hn => (range A).mpr ⟨n, hn⟩))⟩,
      fun n A ha s hs => (fn n k s).mpr (levels.2 n.val A.val ((entry n A H').mp ha) s.val hs)⟩
    let ε : Env N 5 := ⟨Fin.cases f' (Fin.cases H' (Fin.cases e (Fin.cases l (fun _ => w)))), fun _ => w⟩
    have fb := (es_fiber_relative_l hKP ht nx ε (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).mpr fiber
    obtain ⟨g, gf⟩ := small.countable H' f'
      lv ((es_fiber_sat_l J en ..).mp fb)
    let θ : Env N 4 := ⟨Fin.cases g (Fin.cases H' (Fin.cases k (fun _ => w))), fun _ => w⟩
    exact ⟨g.val, (ef_fiber_relative_l hKP.1 ht nx θ (.bound 3) (.bound 2) (.bound 1) .newest).mp
      ((ef_fiber_sat_l en ..).mpr gf)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原短扩展器在初始秩模型中的所属判断

同一张背景测度图、全部有限函数和可数共同纤维由极限秩闭包回收。
直接证明原公式的相对满足关系；不额外假设整个 Vδ 满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

private theorem ei_maximal_l {δ X : M.Domain} (hX : V_d I δ X)
    (nx : Nonempty {x // M.mem x X}) (D U : (rt_model_l X nx).Domain)
    (maximal : Maximal_d D.val U.val) : Maximal_d (ℳ := rt_model_l X nx) D U := by
  let N := rt_model_l X nx
  have ht := v_transitive_l I hX
  have sub (A B : N.Domain) : M.MemberSubset A.val B.val ↔ N.MemberSubset A B :=
    ⟨fun h x hx => h x.val hx, fun h x hx => h ⟨x, ht A.val A.property x hx⟩ hx⟩
  refine ⟨⟨fun A hA => (sub A D).mp (maximal.1.1 A.val hA), maximal.1.2.1,
    fun A B hA ab bd => maximal.1.2.2.1 A.val B.val hA ((sub A B).mpr ab) ((sub B D).mpr bd), ?_⟩, ?_, ?_⟩
  · intro A B hA hB
    obtain ⟨C, hC, ca, cb⟩ := maximal.1.2.2.2 A.val B.val hA hB
    let c : N.Domain := ⟨C, ht U.val U.property C hC⟩
    exact ⟨c, hC, (sub c A).mp ca, (sub c B).mp cb⟩
  · intro A hA
    obtain ⟨x, hx⟩ := maximal.2.1 A.val hA
    exact ⟨⟨x, ht A.val A.property x hx⟩, hx⟩
  · intro G filter proper ug
    have full : IsFilter_d D.val G.val := by
      refine ⟨fun A hA => ?_, filter.2.1, fun A B hA ab bd => ?_, fun A B hA hB => ?_⟩
      · let a : N.Domain := ⟨A, ht G.val G.property A hA⟩
        exact (sub a D).mpr (filter.1 a hA)
      · let a : N.Domain := ⟨A, ht G.val G.property A hA⟩
        let b : N.Domain := ⟨B, v_subset_mem_l I hX D.property bd⟩
        exact filter.2.2.1 a b hA ((sub a b).mp ab) ((sub b D).mp bd)
      · let a : N.Domain := ⟨A, ht G.val G.property A hA⟩
        let b : N.Domain := ⟨B, ht G.val G.property B hB⟩
        obtain ⟨C, hC, ca, cb⟩ := filter.2.2.2 a b hA hB
        exact ⟨C.val, hC, (sub C a).mpr ca, (sub C b).mpr cb⟩
    have proper' : Proper_d G.val := fun A hA => by
      obtain ⟨x, hx⟩ := proper ⟨A, ht G.val G.property A hA⟩ hA
      exact ⟨x.val, hx⟩
    exact (sub G U).mp (maximal.2.2 G.val full proper' ((sub U G).mpr ug))

/-- 源内实际参数的原短扩展器具有所属模型内部的全部短扩展器性质。 -/
theorem Ex_short_d.local_l {ω κ L F δ X R : M.Domain} (h : Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ) (hL : M.mem L X) (hF : M.mem F X) (code : ∃ c, Smem_d I c X R) : It_local_d I ω X R κ L F := by
  apply (it_local_mem_l I code).mpr
  have ht := v_transitive_l I hX
  have hκ := ht L hL κ h.above
  have hω := ht κ hκ ω h.uncountable
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  have he := rt_model_ext_l hZF.1 ht nx
  have pairs := sc_v_pair_l (ZF.modelsKP hZF) hδ hX
  let J := rt_pair_l ht nx hZF.1 pairs
  let w : N.Domain := ⟨ω, hω⟩
  let k : N.Domain := ⟨κ, hκ⟩
  let z : N.Domain := ⟨L, hL⟩
  let e : N.Domain := ⟨F, hF⟩
  let ρ : Env N 4 := ⟨Fin.cases e (Fin.cases z (Fin.cases k (fun _ => w))), fun _ => w⟩
  have fn := rt_fn_l ht nx hZF.1
  have entry := rt_entry_l ht nx hZF.1
  have cp := rt_cp_l ht nx hZF.1
  have sub (A B : N.Domain) : N.MemberSubset A B ↔ M.MemberSubset A.val B.val :=
    ⟨fun g x hx => g ⟨x, ht A.val A.property x hx⟩ hx, fun g x hx => g x.val hx⟩
  -- 极限秩闭包同时回收函数图和由这些图组成的集合，供各条扩展器公理共用。
  have owned {A B f} (ha : M.mem A X) (hb : M.mem B X) (ff : Fn0_d A B f) : M.mem f X := by
    obtain ⟨Y, hy, ay, by'⟩ := v_joint_bound_l I hX ha hb
    exact v_relation_mem_l I hX hδ hy (fun p hp => (ff.1 p hp).elim fun a ha =>
      ha.2.elim fun b hb => ⟨a, ay a ha.1, b, by' b hb.1, hb.2⟩)
  have family (n : N.Domain) (A : M.Domain) (all : ∀ s, M.mem s A → Fn0_d n.val κ s) : M.mem A X := by
    obtain ⟨Y, hy, ny, ky⟩ := v_joint_bound_l I hX n.property hκ
    exact v_relations_mem_l I hX hδ hy (fun f hf p hp => ((all f hf).1 p hp).elim fun a ha =>
      ha.2.elim fun b hb => ⟨a, ny a ha.1, b, ky b hb.1, hb.2⟩)
  have space (n D : N.Domain) (hd : ∀ s, N.mem s D ↔ Fn0_d n k s) : ∀ s, M.mem s D.val ↔ Fn0_d n.val κ s :=
    fun s => ⟨fun hs => (fn ..).mp ((hd ⟨s, ht D.val D.property s hs⟩).mp hs),
      fun hs => (hd ⟨s, owned n.property hκ hs⟩).mpr ((fn ..).mpr hs)⟩
  refine ⟨hω, hκ, hL, hF, (Formula.satisfies_conj_iff _ _ _).mpr ⟨?_, ?_⟩⟩
  · change Formula.satisfies ρ (ex_pre_m (.bound 3) (.bound 2) (.bound 1) .newest)
    simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
      Formula.satisfies_isCardinal_iff J he, Formula.satisfies_mem_iff, Formula.satisfies_isOrdinal_iff,
      Formula.satisfies_isFunction_iff J he, em_family_sat_l he, es_coherent_sat_l J he,
      ex_complete_sat_l he, ea_atoms_sat_l he, en_normal_sat_l he, ex_principal_sat_l he, ex_nonprincipal_sat_l he]
    refine ⟨rt_omega_l ht nx hZF.1 w h.omega,
      rt_cardinal_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pairs k h.critical, h.uncountable,
      rt_ordinal_l ht nx z h.length, h.above,
      (rt_function_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pairs e).mpr h.graph, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun n a hn ha => ?_, fun a U V hu hv => ?_, fun a U hu => ?_⟩
      · obtain ⟨U, hu⟩ := h.measures.total n.val a.val hn ((fn ..).mp ha)
        exact ⟨⟨U, (rd_entry_transitive_l ht hF hu).2⟩, (entry ..).mpr hu⟩
      · exact Subtype.ext (h.measures.function a.val U.val V.val ((entry ..).mp hu) ((entry ..).mp hv))
      · obtain ⟨n, D, hn, ha, hd, maximal⟩ := h.measures.measure a.val U.val ((entry ..).mp hu)
        let n' : N.Domain := ⟨n, ht ω hω n hn⟩
        let D' : N.Domain := ⟨D, ht U.val U.property D maximal.1.2.1⟩
        exact ⟨n', D', hn, (fn n' z a).mpr ha, fun s => (hd s.val).trans (fn n' k s).symm,
          ei_maximal_l hZF hX nx D' U maximal⟩
    · intro m n q a b U V A hm hn hq ha hb hav hbu all
      obtain ⟨Z, pull, decide⟩ := h.coherent m.val n.val q.val a.val b.val U.val V.val A.val hm hn
        ((fn ..).mp hq) ((fn ..).mp ha) ((cp ..).mp hb) ((entry ..).mp hav) ((entry ..).mp hbu)
        (fun s hs => (fn ..).mp (all ⟨s, ht A.val A.property s hs⟩ hs))
      have hz := family n Z (fun s hs => ((pull s).mp hs).1)
      refine ⟨⟨Z, hz⟩, fun s => (pull s.val).trans (and_congr (fn n k s).symm ?_), decide⟩
      exact ⟨fun ⟨t, ht', comp⟩ => ⟨⟨t, ht A.val A.property t ht'⟩, ht', (cp ..).mpr comp⟩,
        fun ⟨t, ht', comp⟩ => ⟨t.val, ht', (cp ..).mp comp⟩⟩
    · intro n a U D ha hu hd μ hμ f hf
      obtain ⟨B, hB, spec⟩ := h.complete n.val a.val U.val D.val ((fn ..).mp ha) ((entry ..).mp hu)
        (space n D hd) μ.val hμ f.val ((fn ..).mp hf)
      refine ⟨⟨B, ht U.val U.property B hB⟩, hB, fun x => (spec x.val).trans (and_congr Iff.rfl ?_)⟩
      let η : Env N 4 := ⟨Fin.cases x (Fin.cases f (Fin.cases U (fun _ => μ))), fun _ => μ⟩
      exact ((ed_all_sat_l he η (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((rt_model_delta_l ht nx (ed_all_delta_l ..) η).trans (ed_all_sat_l hZF.1 _ _ _ _ _))).symm
    · intro p n a U i r α β hn ha hu hi hr
      obtain ⟨T, spec, decide⟩ := h.atoms p n.val a.val U.val i.val r.val α.val β.val hn
        ((fn ..).mp ha) ((entry ..).mp hu) ((entry ..).mp hi) ((entry ..).mp hr)
      have ht' := family n T (fun s hs => ((spec s).mp hs).1)
      refine ⟨⟨T, ht'⟩, fun s => (spec s.val).trans (and_congr (fn n k s).symm ?_), ?_⟩
      · let η : Env N 4 := ⟨Fin.cases s (Fin.cases r (Fin.cases i (fun _ => k))), fun _ => k⟩
        exact ((ea_test_sat_l he η p (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
          ((rt_model_delta_l ht nx (ea_test_delta_l ..) η).trans (ea_test_sat_l hZF.1 _ _ _ _ _ _))).symm
      · cases p with
        | false => exact decide
        | true => exact decide.trans ⟨Subtype.ext, congrArg Subtype.val⟩
    · intro n a U D f i α A hn ha hu hd hf hi hA reg
      obtain ⟨m, b, W, β, B, hm, succ, fb, ab, last, lt, hbW, hBW, graph⟩ := h.normal
        n.val a.val U.val D.val f.val i.val α.val A.val hn ((fn ..).mp ha) ((entry ..).mp hu)
        (space n D hd) ((fn ..).mp hf) ((entry ..).mp hi) hA (fun s hs x y hfx hiy => by
          have hsX := ht A.val A.property s hs
          have hx := (rd_entry_transitive_l ht f.property hfx).2
          have hy := (rd_entry_transitive_l ht hsX hiy).2
          exact reg ⟨s, hsX⟩ hs ⟨x, hx⟩ ⟨y, hy⟩ ((entry ..).mpr hfx) ((entry ..).mpr hiy))
      have bw := rd_entry_transitive_l ht hF hbW
      let m' : N.Domain := ⟨m, ht ω hω m hm⟩
      let b' : N.Domain := ⟨b, bw.1⟩
      let W' : N.Domain := ⟨W, bw.2⟩
      let β' : N.Domain := ⟨β, ht α.val α.property β lt⟩
      let B' : N.Domain := ⟨B, ht W bw.2 B hBW⟩
      refine ⟨m', b', W', β', B', hm, (rt_successor_l ht nx hZF.1 ..).mpr succ, (fn ..).mpr fb,
        (sub ..).mpr ab, (entry ..).mpr last, lt, (entry ..).mpr hbW, hBW, fun s hs => ?_⟩
      let η : Env N 5 := ⟨Fin.cases s (Fin.cases f (Fin.cases A (Fin.cases k (fun _ => n)))), fun _ => n⟩
      exact ((en_graph_sat_l he η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((rt_model_delta_l ht nx (en_graph_delta_l ..) η).trans (en_graph_sat_l hZF.1 _ _ _ _ _ _))).mpr (graph s.val hs)
    · intro n a U hn ha hu A
      refine (h.principal n.val a.val U.val hn ((fn ..).mp ha) ((entry ..).mp hu) A.val).trans (and_congr ?_ Iff.rfl)
      exact ⟨fun all s hs => (fn ..).mpr (all s.val hs),
        fun all s hs => (fn ..).mp (all ⟨s, ht A.val A.property s hs⟩ hs)⟩
    · intro a U i α hu hi hα x s single
      apply h.nonprincipal a.val U.val i.val α.val ((entry ..).mp hu) ((entry ..).mp hi) hα x.val s.val
      intro y
      exact ⟨fun hy => congrArg Subtype.val ((single ⟨y, ht s.val s.property y hy⟩).mp hy),
        fun eq => eq.symm ▸ (single x).mpr rfl⟩
  -- 可数完备性：先读取原层族和纤维条件，再将实际共同纤维的图回收到源。
  · change Formula.satisfies ρ (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest)
    simp only [ex_countable_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff]
    intro H f levels fiber
    have levels := (ef_levels_sat_l he _ _ _ _).mp levels
    have levels' : Ef_levels_d ω κ H.val := by
      obtain ⟨⟨P, fp⟩, all⟩ := levels
      refine ⟨⟨P.val, (fn ..).mp fp⟩, fun n A hn s hs => ?_⟩
      have na := rd_entry_transitive_l ht H.property hn
      exact (fn ..).mp (all ⟨n, na.1⟩ ⟨A, na.2⟩ ((entry ..).mpr hn) ⟨s, ht A na.2 s hs⟩ hs)
    have fiber := (es_fiber_relative_l (ZF.modelsKP hZF) ht nx _ _ _ _ _ _).mp fiber
    obtain ⟨g, hg⟩ := h.countable H.val f.val levels' fiber
    exact ⟨⟨g, owned hω hκ hg.1⟩, (ef_fiber_relative_l hZF.1 ht nx _ _ _ _ _).mpr hg⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 在嵌套施加源之间搬运完整可数层族

先用两源共有的序数编号把任意子集编码成 κ 上的二元关系。
有限幂子集一致性搬运关系码；按有限列长度切片后恢复原来的层族。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一实际编号属于两源时，其定义域的任意源内子集均可搬运。 -/
theorem Ea_subset_d.indexed_subset_l {ω κ K X R K' Y S A e T : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (hAY : M.mem A Y) (heX : M.mem e X) (heY : M.mem e Y)
    (inj : M.IsSetInjectionFromTo I e A κ) (hT : M.mem T X) (sub : M.MemberSubset T A) : M.mem T Y := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨d, hd⟩ := target.code
  obtain ⟨P, hP, ps⟩ := source.square_l hZF source.cardinal_mem
  let ρ : Env M 3 := ⟨Fin.cases T (Fin.cases κ (fun _ => e)), fun _ => κ⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 5)) (kpair0_m (.bound 2) .newest .newest))) }
  have read p : φ.denote ρ p ↔ ∃ a, M.mem a T ∧ ∃ x, M.mem x κ ∧ Rd_entry_d a x e ∧ KPair_d M p x x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1]; rfl
  obtain ⟨Q, hQ, qs⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (kpair0_delta_l ..)))) ρ
    (Fin.cases hT (Fin.cases source.cardinal_mem (fun _ => heX))) hP
  have hQY := subsets.relation_l hZF source target hQ (fun p hp => (ps p).mp ((qs p).mp hp).1)
  have entry x : Rd_entry_d x x Q ↔ ∃ a, M.mem a T ∧ Rd_entry_d a x e := by
    constructor
    · rintro ⟨p, pair, hp⟩
      obtain ⟨a, ha, y, _, hay, code⟩ := (read p).mp ((qs p).mp hp).2
      exact ⟨a, ha, (kpair_injective_l M code pair).1 ▸ hay⟩
    · rintro ⟨a, ha, hax⟩
      obtain ⟨p, hp⟩ := (I).total x x
      have hx := inj.1.output_mem_of_pairMember hax
      exact ⟨p, hp, (qs p).mpr ⟨(ps p).mpr ⟨x, hx, x, hx, hp⟩, (read p).mpr ⟨a, ha, x, hx, hax, hp⟩⟩⟩
  let η : Env M 3 := ⟨Fin.cases κ (Fin.cases e (fun _ => Q)), fun _ => κ⟩
  let ψ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 1) (.conj (rd_entry0_m (.bound 1) .newest (.bound 3)) (rd_entry0_m .newest .newest (.bound 4))) }
  have decode a : ψ.denote η a ↔ ∃ x, M.mem x κ ∧ Rd_entry_d a x e ∧ Rd_entry_d x x Q := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨B, hB, bs⟩ := sc_separate_source_l I hZF target.omega target.transitive hd target.theory ψ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) η
    (Fin.cases target.cardinal_mem (Fin.cases heY (fun _ => hQY))) hAY
  have eq : B = T := hZF.1.eq_of_same_members B T (fun a => by
    rw [bs a, decode a]
    constructor
    · rintro ⟨_, x, _, hax, hx⟩
      obtain ⟨b, hb, hbx⟩ := (entry x).mp hx
      exact inj.2 b a x hbx hax ▸ hb
    · intro ha
      obtain ⟨x, hx, hax⟩ := inj.1.2.2 a (sub a ha)
      exact ⟨sub a ha, x, hx, hax, (entry x).mpr ⟨a, ha, hax⟩⟩)
  exact eq ▸ hB

/-- 层族由其全部有限列之并及列长度唯一确定，无须预先共享整张 ω 列。 -/
theorem Ea_subset_d.levels_l {ω κ K X R K' Y S H : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (inside : M.MemberSubset Y X) (hκ : M.IsOrdinal κ)
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) : M.mem H Y := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨d, hd⟩ := target.code
  obtain ⟨P, hP, bound⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hH
  let ρ : Env M 3 := ⟨Fin.cases ω (Fin.cases P (fun _ => H)), fun _ => ω⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 5)) (.mem (.bound 2) .newest))) }
  have read s : φ.denote ρ s ↔ ∃ n, M.mem n ω ∧ ∃ A, M.mem A P ∧ Rd_entry_d n A H ∧ M.mem s A := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨T, hT, ts⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.mem _ _)))) ρ
    (Fin.cases source.omega_mem (Fin.cases hP (fun _ => hH))) (inside K' target.finite.mem_l)
  obtain ⟨e, he, index⟩ := target.finite_index_l hZF hκ
  have hTY := subsets.indexed_subset_l hZF source target target.finite.mem_l (inside e he) he index hT
    (fun s hs => ((ts s).mp hs).1)
  obtain ⟨P₀, fn⟩ := levels.1
  let η : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  let ψ : BinarySchema 1 := { body := fn0_m (.bound 1) (.bound 2) .newest }
  have decode n s : ψ.denote η n s ↔ Fn0_d n κ s := fn0_sat_l hZF.1 ..
  obtain ⟨G, _, hG, _, gf, gs⟩ := sc_separation_function_l hZF target.omega target.transitive hd target.theory ψ
    (fn0_delta_l ..) η (fun _ => target.cardinal_mem) target.omega_mem hTY
  have row n A B (hnA : Rd_entry_d n A H) (hnB : Rd_entry_d n B G) : A = B := by
    apply hZF.1.eq_of_same_members A B
    intro s
    rw [gs n B hnB s, decode n s]
    constructor
    · intro hs
      have fs := levels.2 n A hnA s hs
      exact ⟨(ts s).mpr ⟨((target.finite_l (ZF.modelsKP hZF)) s).mpr ⟨n, (fn.bound_l hnA).1, fn0_function_l (ZF.modelsKP hZF) fs⟩,
        (read s).mpr ⟨n, (fn.bound_l hnA).1, A, (bound n A hnA).2, hnA, hs⟩⟩, fs⟩
    · rintro ⟨hs, fs⟩
      obtain ⟨m, _, C, _, hmC, hsC⟩ := (read s).mp ((ts s).mp hs).2
      have eq := (levels.2 m C hmC s hsC).domain_eq_l hZF.1 fs
      subst m
      exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 n C A hmC hnA ▸ hsC
  have eq : H = G := (fn0_function_l (ZF.modelsKP hZF) fn).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) gf).1.1 (fun n A => ⟨fun hnA => by
      obtain ⟨B, _, hnB⟩ := gf.2.1 n (fn.bound_l hnA).1
      exact (row n A B hnA hnB).symm ▸ hnB, fun hnA => by
      obtain ⟨B, _, hnB⟩ := fn.2.1 n (gf.bound_l hnA).1
      exact row n B A hnB hnA ▸ hnB⟩)
  exact eq.symm ▸ hG

/-- 较小所属模型的局部短扩展器，决定较大施加源中已有层族的共同纤维。 -/
theorem It_local_d.source_fiber_l {ω κ K X R K' Y S L F H f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (branches : Sc_branch_d ω Y) (loc : It_local_d I ω Y S κ L F)
    (hH : M.mem H X) (levels : Ef_levels_d ω κ H) (fiber : Es_fiber_d I ω L F H f) :
    ∃ g, M.mem g Y ∧ Ef_fiber_d ω κ H g :=
  loc.fiber_l hZF owner branches
    (agree.subset_l.levels_l hZF source owner inside (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code).1 hH levels) levels fiber

end YesMetaZFC.SetTheory.LargeCardinal
