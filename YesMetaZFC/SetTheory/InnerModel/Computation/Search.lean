import YesMetaZFC.SetTheory.InnerModel.Computation.Stage

/-! # 内部序数搜索及其 Σ₁ 执行证书

扫描 J₀、J₁……，直至阶段程序首次返回非空集合。证书要求所有此前阶段
均实际返回空集；最后取返回集合之并。因此 {y} 表示携带输出 y 的停机状态。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

structure Cs_code (n : Nat) where
  step : Cp_code (n + 1)

def Cs_scan_d {n} (p : Cp_code (n + 1)) (ρ : Env M n) (y : M.Domain) : Prop :=
  ∃ a e, M.IsOrdinal a ∧ (∀ t, ¬ M.mem t e) ∧ Cs_stage_d p ρ a y ∧
    (∃ t, M.mem t y) ∧ ∀ b, M.mem b a → Cs_stage_d p ρ b e

def Cs_eval_d {n} (p : Cs_code n) (ρ : Env M n) (y : M.Domain) : Prop :=
  ∃ v, Cs_scan_d p.step ρ v ∧ M.IsUnionOf y v

def cs_scan_s {n} (p : Cp_code (n + 2)) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (KP.ord0_m (.bound 2)) (.conj (Formula.forallMem (.bound 1) .falsum)
        (.conj ((cs_stage_s p).matrix_m (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 2) (.bound 4) .newest)
          (.conj (Formula.existsMem (.bound 4) .truth)
            (Formula.forallMem (.bound 2) (Formula.existsMem (.bound 4)
              ((cs_stage_s p).matrix_m (fun i => .bound ⟨i.val + 7, by omega⟩) (.bound 1) (.bound 3) .newest)))))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (KP.ord0_delta_l _)
      (.conj (.forallMem _ .falsum) (.conj ((cs_stage_s p).matrix.delta0.bind_l _)
        (.conj (.existsMem _ .truth) (.forallMem _ (.existsMem _ ((cs_stage_s p).matrix.delta0.bind_l _))))))))) }

theorem cs_scan_sat_l (hKP : M.Models KP) {n} (p : Cp_code (n + 2)) (ρ : Env M n) (x y : M.Domain) :
    (cs_scan_s p).schema.denote ρ x y ↔ Cs_scan_d p (ρ.push x) y := by
  let φ := cs_stage_s p
  let η := ρ.push x
  rw [S1_binary.sat_l]
  simp only [cs_scan_s, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff,
    KP.ord0_sat_l hKP, S1_binary.matrix_sat_l, and_true]
  change (∃ T a, M.mem a T ∧ ∃ e, M.mem e T ∧ ∃ w, M.mem w T ∧ M.IsOrdinal a ∧
    (∀ t, ¬ M.mem t e) ∧ φ.matrix_binary.toBinarySchema.denote (η.push a) y w ∧
    (∃ t, M.mem t y) ∧ ∀ b, M.mem b a → ∃ v, M.mem v T ∧
      φ.matrix_binary.toBinarySchema.denote (η.push b) e v) ↔ _
  constructor
  · rintro ⟨T, a, _, e, _, w, _, ha, he, hw, hy, hb⟩
    refine ⟨a, e, ha, he, (cs_stage_sat_l hKP ..).mp ((φ.sat_l η a y).mpr ⟨w, hw⟩), hy, fun b h => ?_⟩
    obtain ⟨v, _, hv⟩ := hb b h
    exact (cs_stage_sat_l hKP ..).mp ((φ.sat_l η b e).mpr ⟨v, hv⟩)
  · rintro ⟨a, e, ha, he, hy, hn, hb⟩
    obtain ⟨w, hw⟩ := (φ.sat_l η a y).mp ((cs_stage_sat_l hKP ..).mpr hy)
    let δ : Delta0BinarySchema (n + 2) := {
      body := φ.matrix_m (fun i => .bound ⟨i.val + 3, by omega⟩) (.bound 1) (.bound 2) .newest
      freeClosed := by simp -implicitDefEqProofs
      delta0 := φ.matrix.delta0.bind_l _ }
    have hδ b v : δ.toBinarySchema.denote (η.push e) b v ↔
        φ.matrix_binary.toBinarySchema.denote (η.push b) e v := by
      rw [BinarySchema.denote, S1_binary.matrix_sat_l]; rfl
    obtain ⟨B, hB⟩ := KP.collection_exists_d hKP δ (η.push e) a (fun b h =>
      ((φ.sat_l η b e).mp ((cs_stage_sat_l hKP ..).mpr (hb b h))).imp (fun v hv => (hδ b v).mpr hv))
    obtain ⟨T, ht⟩ := kp_finite_cover_l hKP [a, e, w, B]
    refine ⟨T, a, (ht a (by simp)).2, e, (ht e (by simp)).2, w, (ht w (by simp)).2,
      ha, he, hw, hn, fun b h => ?_⟩
    obtain ⟨v, hv, hδv⟩ := hB b h
    exact ⟨v, (ht B (by simp)).1 v hv, (hδ b v).mp hδv⟩

def cs_graph_s {n} (p : Cs_code (n + 1)) : S1_binary n := (cs_scan_s p.step).comp (S1_binary.of_delta0 {
  body := rd_graph_m .union (.bound 1) (.bound 1) (.bound 1) .newest
  delta0 := rd_graph_delta_l .. })

theorem cs_graph_sat_l (hKP : M.Models KP) {n} (p : Cs_code (n + 1)) (ρ : Env M n) (x y : M.Domain) :
    (cs_graph_s p).schema.denote ρ x y ↔ Cs_eval_d p (ρ.push x) y := by
  rw [cs_graph_s, S1_binary.comp_sat_l hKP]
  simp only [cs_scan_sat_l hKP, S1_binary.of_delta0_sat_l]
  simp only [BinarySchema.denote, rd_graph_sat_l hKP]
  rfl

theorem cs_scan_unique_l (hM : M.Models KPi) {n} {p : Cp_code (n + 1)} {ρ : Env M n} {y z : M.Domain}
    (hy : Cs_scan_d p ρ y) (hz : Cs_scan_d p ρ z) : y = z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, e, ha, he, hy, ty, hb⟩ := hy
  obtain ⟨b, f, hbo, hf, hz, tz, hc⟩ := hz
  rcases Structure.IsOrdinal.trichotomy hKP.1 ha hbo (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP a b) with h | h | h
  · have h := hKP.1.eq_of_same_members a b h; subst b
    exact cs_stage_unique_l hM hy hz
  · have h := cs_stage_unique_l hM hy (hc a h)
    exact (ty.elim (fun t ht => hf t (h ▸ ht))).elim
  · have h := cs_stage_unique_l hM hz (hb b h)
    exact (tz.elim (fun t ht => he t (h ▸ ht))).elim

theorem cs_eval_unique_l (hM : M.Models KPi) {n} {p : Cs_code n} {ρ : Env M n} {y z : M.Domain}
    (hy : Cs_eval_d p ρ y) (hz : Cs_eval_d p ρ z) : y = z := by
  obtain ⟨v, hv, hy⟩ := hy
  obtain ⟨w, hw, hz⟩ := hz
  have he := cs_scan_unique_l hM hv hw; subst w
  exact (KPi.models_iff_l.mp hM).1.1.eq_of_same_members y z (fun t => (hy t).trans (hz t).symm)

end YesMetaZFC.SetTheory.InnerModel
