import YesMetaZFC.SetTheory.InnerModel.Jensen.Separation

/-! # J 类内的 Δ₀ 收集

背景 Σ₁ 收集同时界住输出及其 J 层证书，再取统一的内部序数界。
收集结果选为已构造的 J 层，因而本身属于 J。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem l_collection_l (hM : M.Models KPi) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, L_d y ∧ φ.toBinarySchema.denote ρ x y) :
    ∃ Y, L_d Y ∧ ∀ x, M.mem x X → ∃ y, M.mem y Y ∧ φ.toBinarySchema.denote ρ x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ψ : S1_binary n := { matrix := {
    body := .conj φ.body.weaken (l0_m .newest (.bound 1))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, φ.freeClosed]
    delta0 := .conj (φ.delta0.rename_l Fin.succ) (l0_delta_l ..) } }
  have hψ x y T : Formula.satisfies (((ρ.push x).push y).push T) ψ.matrix.body ↔
      φ.toBinarySchema.denote ρ x y ∧ L0_d T y := by
    simp only [ψ, Formula.satisfies_conj_iff, Definitional.Formula.weaken, Formula.satisfies_rename, l0_sat_l hKP]
    rfl
  obtain ⟨B, hB⟩ := KP.s1_collection_l hKP ψ ρ X (by
    intro x hx
    obtain ⟨y, hy, hp⟩ := ht x hx
    obtain ⟨T, hT⟩ := (l_witness_l hKP.1 y).mp hy
    exact ⟨y, (ψ.sat_l ρ x y).mpr ⟨T, (hψ x y T).mpr ⟨hp, hT⟩⟩⟩)
  obtain ⟨a, Y, ha, hy⟩ := l_bound_witness_l hM B
  refine ⟨Y, l_layer_l hM ha, fun x hx => ?_⟩
  obtain ⟨y, _, T, hT, hp⟩ := hB x hx
  have hp := (hψ x y T).mp hp
  exact ⟨y, hy T hT y hp.2, hp.1⟩

end YesMetaZFC.SetTheory.InnerModel
