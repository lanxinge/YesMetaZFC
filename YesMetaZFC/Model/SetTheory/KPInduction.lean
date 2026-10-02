import YesMetaZFC.SetTheory.Axioms.KPInduction
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.SetTheory.Kuratowski
import YesMetaZFC.SetTheory.Definitional.Project.Derivation

/-! # 成员归纳理论的语义、原推导核与实际模型实例 -/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem mi_core_sat_l {n} (φ : UnarySchema n) (ρ : Env M n) :
    Formula.satisfies ρ (Axioms.Schema.mi_core_m φ) ↔
      ((∀ x, (∀ y, M.mem y x → φ.denote ρ y) → φ.denote ρ x) → ∀ x, φ.denote ρ x) := by
  simp only [Axioms.Schema.mi_core_m, UnarySchema.denote, Formula.satisfies_imp_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_rename,
    Env.reindex_push_unaryUnderOne, Definitional.Term.eval_newest]

/-- 新理论的附加内容恰为实际公式的成员归纳。 -/
theorem KPi.models_iff_l : M.Models KPi ↔ M.Models KP ∧ Mem_ind_d M := by
  constructor
  · intro h
    refine ⟨⟨h.1, fun s hs => h.2 s (.kp hs)⟩, ?_⟩
    intro n φ ρ
    have hs := h.2 (Axioms.Schema.mi_axiom φ) (.induction φ) ρ.free
    have hc := (Formula.satisfies_forallClosure_iff ρ.free (Axioms.Schema.mi_core_m φ)).mp hs ρ.bound
    exact (mi_core_sat_l φ ρ).mp hc
  · rintro ⟨h, hi⟩
    refine ⟨h.1, fun s hs => ?_⟩
    cases hs with
    | kp hs => exact h.2 s hs
    | induction φ =>
      intro f
      apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.mi_core_m φ)).mpr
      intro b
      exact (mi_core_sat_l φ ⟨b, f⟩).mpr (hi φ ⟨b, f⟩)

/-- 归纳句作为原 Hilbert 推导核的理论公理使用。 -/
theorem KPi.induction_d {n} (φ : UnarySchema n) :
    Definitional.Project.Derives KPi (Axioms.Schema.mi_axiom φ) := by
  have h := Logic.FirstOrder.Derives.theory_axiom
    (free := []) (Γ := []) (T := fo_theory KPi)
    (show fo_theory KPi (fo_sentence (Axioms.Schema.mi_axiom φ)) from ⟨_, .induction φ, rfl⟩)
  simpa [Logic.FirstOrder.Formula.fromSentence, Logic.FirstOrder.Renaming.emptyFree] using! h

/-- 所有现有 ZF 模型都给出新理论的实际实例，不增加模型存在前提。 -/
theorem ZF.models_kpi_l (hZF : M.Models ZF) : M.Models KPi := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  exact KPi.models_iff_l.mpr ⟨ZF.modelsKP hZF, ZF.mem_ind_l M hZF I⟩

end YesMetaZFC.SetTheory
