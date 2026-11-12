import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 实际传递集上的有界成员归纳

只对给定 Δ₀ 公式分离反例，再取成员极小元；不把外部任意谓词或外部
良基性加入模型。传递性保证每个递归前驱仍在同一实际集合中。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem KP.transitive_induction_l (hKP : M.Models KP) {Γ : M.Domain} (trans : M.TransitiveSet Γ)
    {n} (φ : Delta0UnarySchema n) (ρ : Env M n)
    (step : ∀ x, M.mem x Γ → (∀ y, M.mem y x → φ.toUnarySchema.denote ρ y) → φ.toUnarySchema.denote ρ x) :
    ∀ x, M.mem x Γ → φ.toUnarySchema.denote ρ x := by
  classical
  let ψ : Delta0UnarySchema n := {
    body := .neg φ.body
    freeClosed := φ.freeClosed
    delta0 := .neg φ.delta0 }
  obtain ⟨B, sep⟩ := KP.separation_exists_d hKP ψ ρ Γ
  have bad x : M.mem x B ↔ M.mem x Γ ∧ ¬ φ.toUnarySchema.denote ρ x := by
    simpa only [ψ, UnarySchema.denote, Formula.satisfies_neg_iff] using sep x
  intro x hx
  apply Classical.byContradiction
  intro fail
  obtain ⟨a, ha, minimal⟩ := KP.mem_minimal_exists_d hKP ⟨x, (bad x).mpr ⟨hx, fail⟩⟩
  apply ((bad a).mp ha).2 (step a ((bad a).mp ha).1 ?_)
  intro b hb
  apply Classical.byContradiction
  intro fail
  exact minimal b ((bad b).mpr ⟨trans a ((bad a).mp ha).1 b hb, fail⟩) hb

end YesMetaZFC.SetTheory
