import YesMetaZFC.SetTheory.Cumulative

/-! # 任意内部累积层族之并

收集各层的序数指标并取上确界，所得层精确等于原族的并。指标和族可以为空，
不要求给定枚举、共尾性或外部良基性。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ZF.v_union_l (hZF : M.Models ZF) {C X} (hX : M.IsUnionOf X C)
    (hC : ∀ Y, M.mem Y C → ∃ α, V_d I α Y) : ∃ α, V_d I α X := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => C⟩
  let φ : BinarySchema 0 := { body := v_m 𝒞 .newest (.bound 1) }
  have hφ Y α : φ.denote ρ Y α ↔ V_d I α Y := v_sat_l I hZF.1 _ _ _
  obtain ⟨D, hD⟩ := collection_exists_d hZF φ ρ C (fun Y hY => (hC Y hY).elim fun α hα => ⟨α, (hφ Y α).mpr hα⟩)
  let ψ : UnarySchema 1 := { body := Formula.existsMem (.bound 1) (v_m 𝒞 (.bound 1) .newest) }
  obtain ⟨S, hS'⟩ := separation_exists_d hZF ψ (ρ.push C) D
  have hS α : M.mem α S ↔ M.mem α D ∧ ∃ Y, M.mem Y C ∧ V_d I α Y := by
    simpa only [ψ, Formula.satisfies_existsMem_iff, v_sat_l I hZF.1,
      Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push] using hS' α
  obtain ⟨δ, hδ⟩ := KP.exists_union (modelsKP hZF) S
  have hδo := Structure.IsOrdinal.of_union (modelsKP hZF) hδ (fun α hα =>
    ((hS α).mp hα).2.elim fun Y hY => v_ordinal_l I hY.2)
  obtain ⟨V, hV⟩ := v_exists_l I hZF hδo
  have he : X = V := hZF.1.eq_of_same_members X V (fun x => by
    constructor
    · intro hx
      obtain ⟨Y, hYC, hxY⟩ := (hX x).mp hx
      obtain ⟨α, hαD, hαY⟩ := hD Y hYC
      have hαS := (hS α).mpr ⟨hαD, Y, hYC, (hφ Y α).mp hαY⟩
      exact v_mono_l I hZF ((hφ Y α).mp hαY) hV (fun i hi => (hδ i).mpr ⟨α, hαS, hi⟩) x hxY
    · intro hx
      obtain ⟨β, W, hβ, hW, hxW⟩ := (v_unfold_l I hZF hV x).mp hx
      obtain ⟨α, hαS, hβα⟩ := (hδ β).mp hβ
      obtain ⟨Y, hYC, hY⟩ := ((hS α).mp hαS).2
      exact (hX x).mpr ⟨Y, hYC, (v_unfold_l I hZF hY x).mpr ⟨β, W, hβα, hW, hxW⟩⟩)
  exact ⟨δ, he.symm ▸ hV⟩

end YesMetaZFC.SetTheory
