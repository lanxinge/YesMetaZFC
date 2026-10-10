import YesMetaZFC.SetTheory.InnerModel.Order.State
import YesMetaZFC.SetTheory.KP.Sigma1Matrix
import YesMetaZFC.SetTheory.InnerModel.Separation.Witness

/-! # 配对状态及其见证的局部集合界 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rw_state_local_l (hKP : M.Models KP) {C p q U R : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U) (hp : KPair_d M p U R)
    (hR : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem R T) (h : Rw_state_d p q) :
    ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ Rw_state_cert_d B p q ∧ M.mem q B := by
  obtain ⟨A, Q, V, S, ha, hq, hw, hpair⟩ := h
  have he : A = U := (rp_proj_pair_l hKP.1 hp false).mp ha; subst A
  have he : Q = R := (rp_proj_pair_l hKP.1 hp true).mp hq; subst Q
  obtain ⟨W, hWC, hwt, hw, hV, hS⟩ := rw_successor_local_l hKP hC hc hU hu hR hw
  have hUe := rd_transitive_enclosed_l hKP hC hU hu
  have hWe := rd_transitive_enclosed_l hKP hC hWC hwt
  have hqe := rd_fun_enclosed_l hKP hC hV hS hV (rd_opair_value_l hKP.1 hpair)
  obtain ⟨B, hBC, hbt, _, hb⟩ := rd_finite_enclosed_l hKP hC hU hu [U, R, V, S, W, q] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h
    · exact h ▸ hUe
    · exact h ▸ hR
    · exact h ▸ hV
    · exact h ▸ hS
    · exact h ▸ hWe
    · exact h ▸ hqe)
  exact ⟨B, hBC, hbt, ⟨U, hb U (by simp), R, hb R (by simp), V, hb V (by simp),
    S, hb S (by simp), W, hb W (by simp), ha, hq, hw, hpair⟩, hb q (by simp)⟩

theorem rw_state_in_l (hKP : M.Models KP) {C p q U R : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U) (hp : KPair_d M p U R)
    (hR : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem R T) (h : Rw_state_d p q) (ρ : Env M 0) :
    Si_cert_d C rw_state_s ρ p q := by
  obtain ⟨B, hBC, hb, h, hq⟩ := rw_state_local_l hKP hC hc hU hu hp hR h
  exact ⟨B, hBC, hb, hq, (rw_state_matrix_l hKP ρ p q B).mpr h⟩

end YesMetaZFC.SetTheory.InnerModel
