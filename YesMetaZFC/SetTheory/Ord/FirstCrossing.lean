import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.Ord.DefinableMinimum
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.Card.FiniteOrdinal
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 内部自然数单射首次越过给定界

编号列不必单调。ω 不能单射入有限序数，保证越界时刻存在；对实际图公式
取内部最小元，得到此前全部编号严格低于界的首达时刻。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (modelsKP hZF))

/-- 任意已给定有限轮以前的全部编号都有一个内部自然数严格上界。 -/
theorem omega_prefix_bound_l {ω E ℓ : M.Domain} (hw : M.IsOmega ω)
    (fn : M.IsSetFunctionFromTo I E ω ω) (hℓ : M.mem ℓ ω) :
    ∃ B, M.mem B ω ∧ ∀ n v, (M.mem n ℓ ∨ n = ℓ) → Rd_entry_d n v E → M.mem v B := by
  obtain ⟨m, succ, hm⟩ := hw.1.2 ℓ hℓ
  obtain ⟨F, cut⟩ := exists_restriction hZF I E m
  have ff := cut.isSetFunctionFromTo fn (hw.transitive hZF m hm)
  obtain ⟨R, range⟩ := exists_range_of_setFunction hZF I ff.1 ff.2.1
  have fr : M.IsSetFunctionFromTo I F m R := ⟨ff.1, ff.2.1,
    fun n hn => (ff.2.2 n hn).imp fun v hv => ⟨(range v).mpr ⟨n, hv.2⟩, hv.2⟩⟩
  have finite : Finite_d I ω R := ⟨m, hm, ordinal_image_bound_l I hZF (hw.members_areOrdinals hZF m hm)
    (exists_inclusionInjection hZF I (source := m) (fun _ h => h)) fr
    (fun v hv => ((range v).mp hv).imp fun n hn => ⟨ff.input_mem_of_pairMember hn, hn⟩)⟩
  obtain ⟨v, _, lv⟩ := ff.2.2 ℓ succ.predecessor_mem
  obtain ⟨a, ha, max⟩ := finite_max_l I hZF hw (hw.isOrdinal hZF) finite
    (fun v hv => ((range v).mp hv).elim fun _ h => ff.output_mem_of_pairMember h) ⟨v, (range v).mpr ⟨ℓ, lv⟩⟩
  have haω := ((range a).mp ha).elim fun _ h => ff.output_mem_of_pairMember h
  obtain ⟨B, next, hB⟩ := hw.1.2 a haω
  refine ⟨B, hB, fun n v hn nv => ?_⟩
  have nm : M.mem n m := hn.elim (fun h => (succ n).mpr (Or.inl h)) (fun eq => eq.symm ▸ succ.predecessor_mem)
  have hv := max v ((range v).mpr ⟨n, (cut.2 n v).mpr ⟨nm, nv⟩⟩)
  exact hv.elim (fun h => (next v).mpr (Or.inl h)) (fun eq => eq.symm ▸ next.predecessor_mem)

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
