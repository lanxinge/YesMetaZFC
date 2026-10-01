import YesMetaZFC.SetTheory.InnerModel.Computation.Formula

/-! # KP 中程序的总性及求值—公式双向对应 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem cp_cover_l (hKP : M.Models KP) (L : List M.Domain) :
    ∃ T, ∀ A ∈ L, M.MemberSubset A T ∧ M.mem A T := by
  induction L with
  | nil => obtain ⟨a⟩ := M.nonempty; exact ⟨a, fun _ h => (List.not_mem_nil h).elim⟩
  | cons A L ih =>
    obtain ⟨R, hr⟩ := ih
    obtain ⟨U, hu⟩ := KP.exists_unionOfTwo hKP A R
    obtain ⟨T, ht⟩ := KP.exists_insert hKP U A
    have ar x hx := (ht x).mpr (Or.inl ((hu x).mpr (Or.inl hx)))
    have rr x hx := (ht x).mpr (Or.inl ((hu x).mpr (Or.inr hx)))
    refine ⟨T, fun B hb => ?_⟩
    rcases List.mem_cons.mp hb with he | hb
    · subst B; exact ⟨ar, (ht A).mpr (Or.inr rfl)⟩
    · exact ⟨fun x hx => rr x ((hr B hb).1 x hx), rr B (hr B hb).2⟩

theorem cp_cert_total_l (hKP : M.Models KP) {n} (p : Cp_code n) (ρ : Env M n) :
    ∃ y T, Cp_cert_d p ρ y T := by
  induction p with
  | var i => exact ⟨ρ.bound i, ρ.bound i, rfl⟩
  | zero => obtain ⟨E, he⟩ := KP.exists_empty hKP; exact ⟨E, E, he⟩
  | op k p q r ih jh kh =>
    obtain ⟨a, A, ha⟩ := ih ρ
    obtain ⟨b, B, hb⟩ := jh ρ
    obtain ⟨c, C, hc⟩ := kh ρ
    obtain ⟨y, hy⟩ := rd_fun_exists_l hKP k a b c
    obtain ⟨T, ht⟩ := cp_cover_l hKP [A, B, C, a, b, c]
    exact ⟨y, T, a, (ht a (by simp)).2, b, (ht b (by simp)).2, c, (ht c (by simp)).2,
      cp_cert_mono_l p ρ (ht A (by simp)).1 ha, cp_cert_mono_l q ρ (ht B (by simp)).1 hb,
      cp_cert_mono_l r ρ (ht C (by simp)).1 hc, hy⟩
  | let1 p q ih jh =>
    obtain ⟨a, A, ha⟩ := ih ρ
    obtain ⟨y, B, hy⟩ := jh (ρ.push a)
    obtain ⟨T, ht⟩ := cp_cover_l hKP [A, B, a]
    exact ⟨y, T, a, (ht a (by simp)).2, cp_cert_mono_l p ρ (ht A (by simp)).1 ha,
      cp_cert_mono_l q (ρ.push a) (ht B (by simp)).1 hy⟩
  | bunion p q ih jh =>
    obtain ⟨X, A, hx⟩ := ih ρ
    let φ := cp_graph_s q
    have total z : ∃ v, φ.schema.denote ρ z v := by
      obtain ⟨v, T, hv⟩ := jh (ρ.push z)
      exact ⟨v, (φ.sat_l ρ z v).mpr ⟨T, (cp_matrix_sat_l hKP q ρ z v T).mpr hv⟩⟩
    obtain ⟨B, hb⟩ := KP.s1_collection_l hKP φ ρ X (fun z _ => total z)
    obtain ⟨R, hr⟩ := KP.s1_image_l hKP φ ρ X (fun z _ => total z)
      (fun z _ v w hv hw => cp_eval_unique_l hKP.1 q (ρ.push z)
        (cp_graph_sound_l hKP q ρ hv) (cp_graph_sound_l hKP q ρ hw))
    obtain ⟨V, hv⟩ := KP.exists_union hKP B
    obtain ⟨T, ht⟩ := cp_cover_l hKP [A, V, X, R]
    have body z (hz : M.mem z X) : ∃ v, M.mem v R ∧ Cp_cert_d q (ρ.push z) v T := by
      obtain ⟨v, _, W, hwB, hw⟩ := hb z hz
      exact ⟨v, (hr v).mpr ⟨z, hz, (φ.sat_l ρ z v).mpr ⟨W, hw⟩⟩,
        cp_cert_mono_l q (ρ.push z) (fun a ha => (ht V (by simp)).1 a ((hv a).mpr ⟨W, hwB, ha⟩))
          ((cp_matrix_sat_l hKP q ρ z v W).mp hw)⟩
    obtain ⟨y, hy⟩ := KP.exists_union hKP R
    refine ⟨y, T, X, (ht X (by simp)).2, R, (ht R (by simp)).2,
      cp_cert_mono_l p ρ (ht A (by simp)).1 hx, body, fun v hvR => ?_, hy⟩
    obtain ⟨z, hz, hvφ⟩ := (hr v).mp hvR
    obtain ⟨w, _, hw⟩ := body z hz
    have he := cp_eval_unique_l hKP.1 q (ρ.push z) (cp_cert_sound_l hKP.1 q _ hw) (cp_graph_sound_l hKP q ρ hvφ)
    exact ⟨z, hz, he ▸ hw⟩

theorem cp_eval_total_l (hKP : M.Models KP) {n} (p : Cp_code n) (ρ : Env M n) :
    ∃ y, Cp_eval_d p ρ y := by
  obtain ⟨y, T, h⟩ := cp_cert_total_l hKP p ρ
  exact ⟨y, cp_cert_sound_l hKP.1 p ρ h⟩

theorem cp_cert_complete_l (hKP : M.Models KP) {n} {p : Cp_code n} {ρ : Env M n} {y : M.Domain}
    (hy : Cp_eval_d p ρ y) : ∃ T, Cp_cert_d p ρ y T := by
  obtain ⟨z, T, hz⟩ := cp_cert_total_l hKP p ρ
  have he := cp_eval_unique_l hKP.1 p ρ hy (cp_cert_sound_l hKP.1 p ρ hz)
  exact ⟨T, he.symm ▸ hz⟩

theorem cp_graph_sat_l (hKP : M.Models KP) {n} (p : Cp_code (n + 1)) (ρ : Env M n) (x y : M.Domain) :
    (cp_graph_s p).schema.denote ρ x y ↔ Cp_eval_d p (ρ.push x) y := by
  refine ⟨cp_graph_sound_l hKP p ρ, fun hy => ?_⟩
  obtain ⟨T, ht⟩ := cp_cert_complete_l hKP hy
  exact ((cp_graph_s p).sat_l ρ x y).mpr ⟨T, (cp_matrix_sat_l hKP p ρ x y T).mpr ht⟩

end YesMetaZFC.SetTheory.InnerModel
