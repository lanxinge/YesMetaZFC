import YesMetaZFC.SetTheory.InnerModel.Jensen.Constructibility

/-! # ZF 背景下 J 的全收集

将任意公式相对化到 J，收集背景见证后取其 J 部分，最后用统一的 J 层包住它们。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem jl_trace_l (hZF : M.Models ZF) (B : M.Domain) :
    ∃ D, ∀ x, M.mem x D ↔ M.mem x B ∧ L_d x := by
  let φ : UnarySchema 0 := { body := l_m .newest }
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ (jh_env_l B) B
  exact ⟨D, fun x => (hd x).trans (and_congr_right fun _ => l_sat_l (ZF.modelsKP hZF) _ _)⟩

theorem l_model_full_collection_l (hZF : M.Models ZF) {n} (φ : BinarySchema n)
    (ρ : Env (l_model_l (ZF.models_kpi_l hZF)) n)
    (X : (l_model_l (ZF.models_kpi_l hZF)).Domain)
    (ht : ∀ x, (l_model_l (ZF.models_kpi_l hZF)).mem x X → ∃ y, φ.denote ρ x y) :
    ∃ Y : (l_model_l (ZF.models_kpi_l hZF)).Domain,
      ∀ x, (l_model_l (ZF.models_kpi_l hZF)).mem x X →
        ∃ y, (l_model_l (ZF.models_kpi_l hZF)).mem y Y ∧ φ.denote ρ x y := by
  let hM := ZF.models_kpi_l hZF
  let N := l_model_l hM
  let η := image_env_l (M := N) (N := M) Subtype.val ρ
  let ψ : BinarySchema n := {
    body := .conj (l_m .newest) (l_rel_m φ.body)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, φ.freeClosed] }
  have hψ x y : ψ.denote η x y ↔ L_d y ∧ Formula.satisfies ((η.push x).push y) (l_rel_m φ.body) := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, l_sat_l (ZF.modelsKP hZF),
      Definitional.Term.eval_newest]
  have tr (x y : N.Domain) : φ.denote ρ x y ↔
      Formula.satisfies ((η.push x.val).push y.val) (l_rel_m φ.body) := by
    have h := l_rel_sat_l hM φ.body ((ρ.push x).push y)
    rw [image_env_push_l (M := N) (N := M) Subtype.val (ρ.push x) y,
      image_env_push_l (M := N) (N := M) Subtype.val ρ x] at h
    exact h
  obtain ⟨B, hB⟩ := ZF.collection_exists_d hZF ψ η X.val (by
    intro x hx
    let z : N.Domain := ⟨x, l_transitive_l hM X.property hx⟩
    obtain ⟨y, hy⟩ := ht z hx
    exact ⟨y.val, (hψ x y.val).mpr ⟨y.property, (tr z y).mp hy⟩⟩)
  obtain ⟨D, hD⟩ := jl_trace_l hZF B
  obtain ⟨a, Y, ha, hy⟩ := l_bound_l hM (fun x hx => ((hD x).mp hx).2)
  refine ⟨⟨Y, l_layer_l hM ha⟩, fun x hx => ?_⟩
  obtain ⟨y, hyB, hp⟩ := hB x.val hx
  have hp := (hψ x.val y).mp hp
  exact ⟨⟨y, hp.1⟩, hy y ((hD y).mpr ⟨hyB, hp.1⟩), (tr x ⟨y, hp.1⟩).mpr hp.2⟩

end YesMetaZFC.SetTheory.InnerModel
