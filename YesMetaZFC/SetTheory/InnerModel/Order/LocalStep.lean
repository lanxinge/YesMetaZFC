import YesMetaZFC.SetTheory.InnerModel.Order.Local

/-! # 规范追加及其证书留在同一闭包

原输入的参数域固定；每次把像序及追加后的关系表重新界在闭包中的传递集合内。
有限菜单归纳同时保存实际构造证书，避免只证明输出在层内却遗失验证见证。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rw_add_local_l (hKP : M.Models KP) {C U R P V S W T : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U) {k} (hp : Rw_domain_d U P)
    (hR : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem R A)
    (hV : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem V A)
    (hS : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem S A) (h : Rw_add_d k U R P V S W T) :
    ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ Rw_add_cert_d k B U R P V S W T ∧
      (∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem W A) ∧
      (∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem T A) := by
  obtain ⟨Y, Q, hy, hq, hw, ht⟩ := h
  obtain ⟨A, hAC, ha, _, hUA⟩ := rd_bounded_enclosed_l hKP hC hU hu hU (fun _ h => h)
  have hUe : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem U A := ⟨A, hAC, ha, hUA⟩
  have hP := rd_triples_enclosed_l hKP hC hU hu (rw_domain_closed_l hKP hC hU hp) (by
    intro p hpP; obtain ⟨a, ha, b, hb, c, hc, ht⟩ := (hp p).mp hpP; exact ⟨a, b, c, ha, hb, hc, ht⟩)
  have hY := rw_image_enclosed_l hKP hC hU hu k hp hy
  let ρ : Env M 3 := ⟨Fin.cases U (Fin.cases R (fun _ => P)), fun _ => U⟩
  have hQ := rw_rel_enclosed_l hKP hC hc (rw_cmp_s k) ρ
    (Fin.cases hUe (Fin.cases hR (fun _ => hP))) hY
    (hq.congr_l fun x y => (rw_cmp_sat_l hKP k ρ x y).symm)
  have hW := rd_union_enclosed_l hKP hC hc hV hY hw
  let η : Env M 3 := ⟨Fin.cases V (Fin.cases S (fun _ => Q)), fun _ => U⟩
  have hT := rw_rel_enclosed_l hKP hC hc rw_append_s η
    (Fin.cases hV (Fin.cases hS (fun _ => hQ))) hW
    (ht.congr_l fun x y => (rw_append_sat_l hKP.1 η x y).symm)
  obtain ⟨B, hBC, hbT, _, hb⟩ := rd_finite_enclosed_l hKP hC hU hu [Y, Q] (by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact hY
    · have he : x = Q := List.mem_singleton.mp hx; exact he ▸ hQ)
  exact ⟨B, hBC, hbT, ⟨Y, hb Y (by simp), Q, hb Q (by simp), hy, hq, hw, ht⟩, hW, hT⟩

theorem rw_fold_local_l (hKP : M.Models KP) {C U R P V S W T : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U) (L : List Rd_sym) (hp : Rw_domain_d U P)
    (hR : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem R A)
    (hV : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem V A)
    (hS : ∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem S A) (h : Rw_fold_d L U R P V S W T) :
    ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ Rw_fold_cert_d L B U R P V S W T ∧
      (∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem W A) ∧
      (∃ A, M.mem A C ∧ M.TransitiveSet A ∧ M.mem T A) := by
  induction L generalizing V S with
  | nil => exact ⟨U, hU, hu, h, h.1.symm ▸ hV, h.2.symm ▸ hS⟩
  | cons k L ih =>
    obtain ⟨A, Q, h, hf⟩ := h
    obtain ⟨D, hDC, hdT, hd, hA, hQ⟩ := rw_add_local_l hKP hC hc hU hu hp hR hV hS h
    obtain ⟨E, hEC, heT, he, hW, hT⟩ := ih hA hQ hf
    have hD := rd_transitive_enclosed_l hKP hC hDC hdT
    have hE := rd_transitive_enclosed_l hKP hC hEC heT
    obtain ⟨B, hBC, hbT, _, hb⟩ := rd_finite_enclosed_l hKP hC hU hu [A, Q, D, E] (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      exact hx.elim (fun h => h ▸ hA) (fun h => h.elim (fun h => h ▸ hQ)
        (fun h => h.elim (fun h => h ▸ hD) (fun h => h ▸ hE))))
    obtain ⟨Y, hyD, Z, hzD, hd⟩ := hd
    exact ⟨B, hBC, hbT, ⟨A, hb A (by simp), Q, hb Q (by simp),
      ⟨Y, hbT D (hb D (by simp)) Y hyD, Z, hbT D (hb D (by simp)) Z hzD, hd⟩,
      rw_fold_cert_mono_l he (hbT E (hb E (by simp)))⟩, hW, hT⟩

end YesMetaZFC.SetTheory.InnerModel
