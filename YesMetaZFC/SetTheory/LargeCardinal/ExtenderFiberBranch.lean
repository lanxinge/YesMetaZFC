import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTreeBranch
import YesMetaZFC.SetTheory.LargeCardinal.SupportCompleteness

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
    (source : Ep_source_d hZF ω κ K X R) (branches : Sc_branch_d ω X)
    (hL : M.mem L X) (hF : M.mem F X) (hH : M.mem H X) (fiber : Es_fiber_d I ω L F H f) :
    ∃ g, M.mem g X ∧ Es_fiber_d I ω L F H g := by
  obtain ⟨J, hJ, seq⟩ := source.sequences.space L hL
  obtain ⟨P, hP, hp⟩ := source.theory.algebra.envelope_l hH
  obtain ⟨Q, hQ, hq⟩ := source.theory.algebra.envelope_l hF
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
