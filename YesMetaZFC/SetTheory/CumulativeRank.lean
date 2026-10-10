import YesMetaZFC.SetTheory.Cumulative
import YesMetaZFC.SetTheory.MembershipInduction

/-! # 累积层级覆盖原模型中的全部集合

对“属于某层”的实际公式作内部成员归纳。收集每个成员的层级界，取序数上确界，
再取一次幂集；全过程只用原 ZF，不假定模型的外部成员关系良基。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def V_bound_d (x α : M.Domain) : Prop := ∃ V, V_d I α V ∧ M.mem x V

def v_bound_m (𝒞 : OrderedPairConvention) {n} (x α : Term n) : Formula 1 n :=
  .existsE (.conj (v_m 𝒞 α.weaken .newest) (.mem x.weaken .newest))
derive_free_closed v_bound_m

theorem v_bound_sat_l (hE : Extensional M) {n} (ρ : Env M n) (x α : Term n) :
    Formula.satisfies ρ (v_bound_m 𝒞 x α) ↔ V_bound_d I (x.eval ρ) (α.eval ρ) := by
  simp only [v_bound_m, V_bound_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 原模型中的每个集合属于一个实际累积层；输入可以是外部非良基模型对象。 -/
theorem ZF.v_cover_l (hZF : M.Models ZF) (x : M.Domain) : ∃ α V, V_d I α V ∧ M.mem x V := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => x⟩
  let φ : UnarySchema 0 := { body := .existsE (v_bound_m 𝒞 (.bound 1) .newest) }
  let ψ : BinarySchema 0 := { body := v_bound_m 𝒞 (.bound 1) .newest }
  have hφ y : φ.denote ρ y ↔ ∃ α, V_bound_d I y α := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, v_bound_sat_l I hZF.1]
    rfl
  have hψ y α : ψ.denote ρ y α ↔ V_bound_d I y α := v_bound_sat_l I hZF.1 ((ρ.push y).push α) _ _
  change ∃ α, V_bound_d I x α
  refine (hφ x).mp ((mem_ind_l M hZF I) φ ρ ?_ x)
  intro y ih
  obtain ⟨A, hA⟩ := collection_exists_d hZF ψ ρ y (fun z hz => by
    obtain ⟨α, hα⟩ := (hφ z).mp (ih z hz)
    exact ⟨α, (hψ z α).mpr hα⟩)
  let χ : UnarySchema 0 := { body := Formula.isOrdinal .newest }
  obtain ⟨B, hB'⟩ := separation_exists_d hZF χ ρ A
  have hB α : M.mem α B ↔ M.mem α A ∧ M.IsOrdinal α := by
    simpa only [χ, Formula.satisfies_isOrdinal_iff, Definitional.Term.eval_newest] using hB' α
  obtain ⟨β, hβ⟩ := KP.exists_union (modelsKP hZF) B
  have hβo := Structure.IsOrdinal.of_union (modelsKP hZF) hβ (fun α hα => ((hB α).mp hα).2)
  obtain ⟨V, hV⟩ := v_exists_l I hZF hβo
  have hyV : M.MemberSubset y V := by
    intro z hz
    obtain ⟨α, hαA, hα⟩ := hA z hz
    obtain ⟨W, hW, hzW⟩ := (hψ z α).mp hα
    have hαB := (hB α).mpr ⟨hαA, v_ordinal_l I hW⟩
    exact v_mono_l I hZF hW hV (fun i hi => (hβ i).mpr ⟨α, hαB, hi⟩) z hzW
  obtain ⟨γ, hγ⟩ := KP.exists_successor (modelsKP hZF) β
  obtain ⟨W, hW⟩ := v_exists_l I hZF (KP.successor_isOrdinal (modelsKP hZF) hβo hγ)
  exact (hφ y).mpr ⟨γ, W, hW, (v_successor_l I hZF hV hW hγ y).mpr hyV⟩

end YesMetaZFC.SetTheory
