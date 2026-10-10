import YesMetaZFC.SetTheory.IndexedIteration
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 沿内部 ω 的带指标依赖选择

先将实际原公式关系单值化为 (指标,当前值) 上的函数图，再调用 ZF 的确定递归。
指标正确性与序列投影共用 IndexedIteration，不重复内部归纳证明。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem indexed_choice_l (hZFC : M.Models ZFC) {n} (φ : UnarySchema (n+2)) (ρ : Env M n)
    {ω X a} (hω : M.IsOmega ω) (ha : M.mem a X)
    (ht : ∀ i x, M.mem i ω → M.mem x X → ∃ y, M.mem y X ∧ φ.denote ((ρ.push i).push x) y) :
    ∃ F, M.IsSetFunctionFromTo I F ω X ∧
      (∀ o, (∀ x, ¬ M.mem x o) → M.PairMember I o a F) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x F → M.PairMember I j y F →
        φ.denote ((ρ.push i).push x) y := by
  have hZF := models_zf_l hZFC
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I ω X
  let e : Fin (n+2) → Term (n+4) := Fin.cases .newest (Fin.cases (.bound 1) (fun i => .bound ⟨i.val+4, by omega⟩))
  have he : ∀ i, (e i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (fun _ => rfl))
  let ψ : BinarySchema n := {
    body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest) (pred_m φ e (.bound 2))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, he] }
  have hψ p y : ψ.denote ρ p y ↔ ∃ i x, I.Codes p i x ∧ φ.denote ((ρ.push i).push x) y := by
    have henv i x : (⟨fun k => (e k).eval ((((ρ.push p).push y).push i).push x),
        ((((ρ.push p).push y).push i).push x).free⟩ : Env M (n+2)) = (ρ.push i).push x := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))), rfl⟩
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.realizes, pred_sat_l M, henv]
    rfl
  obtain ⟨K, hK, hk⟩ := uniformize_formula_l I hZFC ψ ρ (X := D) (Y := X) (by
    intro p hp
    obtain ⟨i, hi, x, hx, hp⟩ := (hD p).mp hp
    obtain ⟨y, hy, hxy⟩ := ht i x hi hx
    exact ⟨y, hy, (hψ p y).mpr ⟨i, x, hp, hxy⟩⟩)
  obtain ⟨F, hF, hz, hs⟩ := ZF.indexed_iteration_l I hZF hω hD hK ha
  refine ⟨F, hF, hz, fun i j x y hij hix hjy => ?_⟩
  obtain ⟨p, hp, hpy⟩ := hs i j x y hij hix hjy
  obtain ⟨i', x', hp', hxy⟩ := (hψ p y).mp (hk p y hpy)
  obtain ⟨rfl, rfl⟩ := I.injective hp hp'
  exact hxy

end YesMetaZFC.SetTheory.ZFC
