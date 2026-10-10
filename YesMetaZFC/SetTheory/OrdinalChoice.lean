import YesMetaZFC.SetTheory.Ord.DefinableMinimum
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # ZF 中序数值关系的规范统一化

每个非空纤维取其最小序数。唯一值替代给出实际函数图，不消费选择公理。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem ordinal_uniformize_l (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n)
    {D κ : M.Domain} (hκ : M.IsOrdinal κ)
    (total : ∀ s, M.mem s D → ∃ x, φ.denote ρ s x)
    (bound : ∀ s x, M.mem s D → φ.denote ρ s x → M.mem x κ) :
    ∃ f, Fn0_d D κ f ∧ ∀ s x, Rd_entry_d s x f → φ.denote ρ s x := by
  let e : Fin (n + 2) → Fin (n + 3) := Fin.cases 0 (Fin.cases 2 (fun i => ⟨i.val + 3, by omega⟩))
  let ψ : BinarySchema n := {
    body := .conj φ.body (Formula.forallMem .newest (.neg (φ.body.rename e)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, φ.freeClosed] }
  have eq s x y : (((ρ.push s).push x).push y).reindex e = (ρ.push s).push y := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))), rfl⟩
  have sat s x : ψ.denote ρ s x ↔ φ.denote ρ s x ∧ ∀ y, M.mem y x → ¬ φ.denote ρ s y := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_rename, eq]; rfl
  obtain ⟨f, hf, spec⟩ := exists_setFunctionFromTo_of_denote hZF (kp_pair_l (modelsKP hZF)) ψ ρ
    (source := D) (target := κ) (fun s hs => by
      obtain ⟨x, hx⟩ := total s hs
      let θ : UnarySchema (n + 1) := { body := φ.body, freeClosed := φ.freeClosed }
      obtain ⟨y, _, hy, least⟩ := ordinal_min_l hZF θ (ρ.push s) (hκ.mem (bound s x hs hx)) hx
      exact ⟨y, (sat s y).mpr ⟨hy, least⟩⟩)
    (fun s hs x y hx hy => by
      obtain ⟨hx, leastx⟩ := (sat s x).mp hx
      obtain ⟨hy, leasty⟩ := (sat s y).mp hy
      rcases hκ.wellOrder.linear.compare x (bound s x hs hx) y (bound s y hs hy) with he | hxy | hyx
      · exact hZF.1.eq_of_same_members x y he
      · exact (leasty x hxy hx).elim
      · exact (leastx y hyx hy).elim)
    (fun s x hs hx => bound s x hs ((sat s x).mp hx).1)
  exact ⟨f, fn0_of_function_l (modelsKP hZF) hf, fun s x hx => ((sat s x).mp ((spec s x).mp hx).2).1⟩

end YesMetaZFC.SetTheory.ZF
