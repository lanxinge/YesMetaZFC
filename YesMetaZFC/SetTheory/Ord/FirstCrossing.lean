import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.Ord.DefinableMinimum
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 内部自然数单射首次越过给定界

编号列不必单调。ω 不能单射入有限序数，保证越界时刻存在；对实际图公式
取内部最小元，得到此前全部编号严格低于界的首达时刻。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (modelsKP hZF))

theorem omega_first_crossing_l {ω E i : M.Domain} (hw : M.IsOmega ω)
    (f : M.IsSetInjectionFromTo I E ω ω) (hi : M.mem i ω) :
    ∃ n v, M.mem n ω ∧ Rd_entry_d n v E ∧ ¬ M.mem v i ∧
      ∀ m w, M.mem m n → Rd_entry_d m w E → M.mem w i := by
  classical
  have hit : ∃ n v, M.mem n ω ∧ Rd_entry_d n v E ∧ ¬ M.mem v i := by
    apply Classical.byContradiction
    intro no
    apply omega_not_le_finite_l I hZF hw i hi
    refine ⟨E, ⟨f.1.1, f.1.2.1, fun n hn => ?_⟩, f.2⟩
    obtain ⟨v, _, nv⟩ := f.1.2.2 n hn
    exact ⟨v, Classical.byContradiction (fun hv => no ⟨n, v, hn, nv, hv⟩), nv⟩
  let ρ : Env M 3 := ⟨fun j => [ω, E, i].get j, fun _ => ω⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪⌜(.newest : Term 4)⌝ₛ ∈ ⌜(.bound 1 : Term 4)⌝ₛ ∧
    (∃ v, ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ, v, ⌜(.bound 2 : Term 4)⌝ₛ) ∧ ¬ v ∈ ⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ M.mem n ω ∧ ∃ v, Rd_entry_d n v E ∧ ¬ M.mem v i := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl
  obtain ⟨n, v, hn, nv, hv⟩ := hit
  obtain ⟨m, _, hm, first⟩ := ordinal_min_l hZF φ ρ (hw.members_areOrdinals hZF n hn) ((sat n).mpr ⟨hn, v, nv, hv⟩)
  obtain ⟨hm, w, mw, hw'⟩ := (sat m).mp hm
  exact ⟨m, w, hm, mw, hw', fun j x hj jx => Classical.byContradiction fun hx =>
    first j hj ((sat j).mpr ⟨hw.transitive hZF m hm j hj, x, jx, hx⟩)⟩

end YesMetaZFC.SetTheory.ZF
