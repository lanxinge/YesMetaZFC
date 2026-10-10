import YesMetaZFC.SetTheory.InnerModel.Computation.Search

/-! # 从实际命中阶段到最早停机阶段

归纳发生在模型的原公式成员归纳模式内；即使序数在外部非良基，证明仍成立。
这里仅要求某一步确实命中，构造性公理将在 Δ₁ 编译中负责提供这样的阶段。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem cs_scan_exists_l (hM : M.Models KPi) {n} (p : Cp_code (n + 2)) (ρ : Env M n) (x : M.Domain)
    {a y : M.Domain} (ha : M.IsOrdinal a) (hy : Cs_stage_d p (ρ.push x) a y) (hn : ∃ t, M.mem t y) :
    ∃ v, Cs_scan_d p (ρ.push x) v := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ψ : UnarySchema (n + 1) := {
    body := .imp (.conj (KP.ord0_m .newest) (.existsE
      (.conj (binary_pred_m (cs_stage_s p).schema (fun i => .bound ⟨i.val + 2, by omega⟩) (.bound 1) .newest)
        (Formula.existsMem .newest .truth))))
      (.existsE (binary_pred_m (cs_scan_s p).schema (fun i => .bound ⟨i.val + 3, by omega⟩) (.bound 2) .newest)) }
  have hψ b : ψ.denote (ρ.push x) b ↔
      ((M.IsOrdinal b ∧ ∃ v, Cs_stage_d p (ρ.push x) b v ∧ ∃ t, M.mem t v) → ∃ v, Cs_scan_d p (ρ.push x) v) := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_truth_iff, and_true,
      KP.ord0_sat_l hKP, binary_pred_sat_l, cs_stage_sat_l hKP, cs_scan_sat_l hKP]
    rfl
  apply (hψ a).mp ((KPi.models_iff_l.mp hM).2 ψ (ρ.push x) ?_ a) ⟨ha, y, hy, hn⟩
  intro b ih
  apply (hψ b).mpr
  rintro ⟨hb, v, hv, hn⟩
  classical
  by_cases hl : ∃ c, M.mem c b ∧ ∃ w, Cs_stage_d p (ρ.push x) c w ∧ ∃ t, M.mem t w
  · obtain ⟨c, hc, w, hw, ht⟩ := hl
    exact (hψ c).mp (ih c hc) ⟨hb.mem hc, w, hw, ht⟩
  · obtain ⟨e, he⟩ := KP.exists_empty hKP
    refine ⟨v, b, e, hb, he, hv, hn, fun c hc => ?_⟩
    obtain ⟨w, hw⟩ := cs_stage_total_l hM p (ρ.push x) c
    have hwe : w = e := hKP.1.eq_of_same_members w e
      (fun t => iff_of_false (fun ht => hl ⟨c, hc, w, hw, t, ht⟩) (he t))
    exact hwe ▸ hw

theorem cs_eval_exists_l (hM : M.Models KPi) {n} (p : Cs_code (n + 1)) (ρ : Env M n) (x : M.Domain)
    {a y : M.Domain} (ha : M.IsOrdinal a) (hy : Cs_stage_d p.step (ρ.push x) a y) (hn : ∃ t, M.mem t y) :
    ∃ v, Cs_eval_d p (ρ.push x) v := by
  obtain ⟨z, hz⟩ := cs_scan_exists_l hM p.step ρ x ha hy hn
  obtain ⟨v, hv⟩ := KP.exists_union (KPi.models_iff_l.mp hM).1 z
  exact ⟨v, z, hz, hv⟩

end YesMetaZFC.SetTheory.InnerModel
