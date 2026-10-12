import YesMetaZFC.SetTheory.Descriptive.GameWinningPositions

/-! # 避开玩家 II 获胜局面的策略

补集在 II 的走法下封闭；轮到 I 时至少有一个后继仍在补集中。
本层用选择公理把实际可走字母关系单值化为策略图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_avoid_d (ω X J Q s x : M.Domain) : Prop := ∀ n, Fn0_d n X s →
  M.mem n J → ¬ M.mem s Q → ∀ t, Fseq_end_d I ω t s x → ¬ M.mem t Q

def cg_avoid_m {d} (ω X J Q s x : Term d) : Formula 1 d := .forallE (.imp
  (fn0_m .newest X.weaken s.weaken) (.imp (.mem .newest J.weaken) (.imp (.neg (.mem s.weaken Q.weaken))
    (.forallE (.imp (fseq_end_m (𝒞 := kpair_convention_l) ω.weaken.weaken .newest s.weaken.weaken x.weaken.weaken)
      (.neg (.mem .newest Q.weaken.weaken)))))))
derive_free_closed cg_avoid_m

theorem cg_avoid_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X J Q s x : Term d) :
    Formula.satisfies ρ (cg_avoid_m ω X J Q s x) ↔
      Cg_avoid_d I (ω.eval ρ) (X.eval ρ) (J.eval ρ) (Q.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [cg_avoid_m, Cg_avoid_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    fseq_end_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_avoid_l {ω X F J B W Z Q a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d K ω X F) (runs : M.IsFunctionSpace K B ω X)
    (strategies : M.IsFunctionSpace K Z F X) (positions : Cg_ii_d K ω X F J B W Q) (ha : M.mem a X) :
    ∃ σ, Fn0_d F X σ ∧ ∀ s x, Rd_entry_d s x σ → Cg_avoid_d K ω X J Q s x := by
  classical
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push J).push Q
  let φ : BinarySchema 4 := { body := cg_avoid_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s x : φ.denote ρ s x ↔ Cg_avoid_d K ω X J Q s x := cg_avoid_sat_l K hZF.1 _ _ _ _ _ _ _
  obtain ⟨σ, fn, read⟩ := ZFC.uniformize_formula_l K hZFC φ ρ (X := F) (Y := X) (by
    intro s hsF
    obtain ⟨n, hn, hs⟩ := (space s).mp hsF
    by_cases outside : ¬ M.mem s Q
    · by_cases turn : M.mem n J
      · have good : ∃ x, M.mem x X ∧ ∀ t, Fseq_end_d K ω t s x → ¬ M.mem t Q := by
          apply Classical.byContradiction
          intro no
          apply outside (cg_ii_all_l hZFC hω space runs strategies positions hn hs ha ?_)
          intro x hx t endt
          apply Classical.byContradiction
          intro bad
          exact no ⟨x, hx, fun u endu hu => bad (fseq_end_rebuild_l K hZF.1 endu endt ▸ hu)⟩
        obtain ⟨x, hx, good⟩ := good
        exact ⟨x, hx, (sat s x).mpr (fun _ _ _ _ => good)⟩
      · refine ⟨a, ha, (sat s a).mpr (fun m hm hmJ _ => ?_)⟩
        have eq := hm.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hs)
        exact (turn (eq ▸ hmJ)).elim
    · exact ⟨a, ha, (sat s a).mpr (fun _ _ _ bad => (outside bad).elim)⟩)
  exact ⟨σ, fn0_of_function_l (ZF.modelsKP hZF) fn, fun s x hx => (sat s x).mp (read s x hx)⟩

end YesMetaZFC.SetTheory.Descriptive
