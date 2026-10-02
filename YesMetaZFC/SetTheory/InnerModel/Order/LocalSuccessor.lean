import YesMetaZFC.SetTheory.InnerModel.Order.LocalStep

/-! # 规范微后继的层内 Σ₁ 解释

同时把载体、序关系和整份 Δ₀ 证书放入同一个传递 rud 闭包。
最后用矩阵的绝对性识别层内解释；层本身不需要满足 KP。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rw_adjoin_local_l (hKP : M.Models KP) {C U R A Q : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U)
    (hR : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem R T) (h : Rw_adjoin_d U R A Q) :
    M.mem A C ∧ M.TransitiveSet A ∧ (∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem Q T) := by
  obtain ⟨Y, E, hy, he, ha, hq⟩ := h
  have hYC := hC .pair U U U hU hU hU Y hy
  have hEC := hC .diff U U U hU hU hU E (fun x => iff_of_false (he x) (fun h => h.2 h.1))
  obtain ⟨A', hAC, ha'⟩ := hC.union_l hKP hU hYC
  have eq := hKP.1.eq_of_same_members A' A (fun x => (ha' x).trans (ha x).symm)
  subst A'
  have haT : M.TransitiveSet A := fun x hx y hyx => (ha y).mpr (Or.inl (((ha x).mp hx).elim
    (fun hx => hu x hx y hyx) (fun hx => (((hy x).mp hx).elim id id) ▸ hyx)))
  obtain ⟨X, hXC, hx, _, hAX⟩ := rd_bounded_enclosed_l hKP hC hAC haT hAC (fun _ h => h)
  obtain ⟨Z, hZC, hz, _, hUZ⟩ := rd_bounded_enclosed_l hKP hC hU hu hU (fun _ h => h)
  obtain ⟨F, hFC, hf, _, hEF⟩ := rd_bounded_enclosed_l hKP hC hU hu hEC (fun x hx => (he x hx).elim)
  let ρ : Env M 3 := ⟨Fin.cases U (Fin.cases R (fun _ => E)), fun _ => U⟩
  exact ⟨hAC, haT, rw_rel_enclosed_l hKP hC hc rw_append_s ρ
    (Fin.cases ⟨Z, hZC, hz, hUZ⟩ (Fin.cases hR (fun _ => ⟨F, hFC, hf, hEF⟩))) ⟨X, hXC, hx, hAX⟩
    (hq.congr_l fun x y => (rw_append_sat_l hKP.1 ρ x y).symm)⟩

theorem rw_successor_local_l (hKP : M.Models KP) {C U R V S : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U)
    (hR : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem R T) (h : Rw_successor_d U R V S) :
    ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ Rw_successor_cert_d B U R V S ∧
      (∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem V T) ∧
      (∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem S T) := by
  obtain ⟨A, Q, ha, P, hp, hf⟩ := h
  obtain ⟨hAC, haT, hQ⟩ := rw_adjoin_local_l hKP hC hc hU hu hR ha
  obtain ⟨X, hXC, hx, _, hAX⟩ := rd_bounded_enclosed_l hKP hC hAC haT hAC (fun _ h => h)
  obtain ⟨D, hDC, hdT, hd, hV, hS⟩ := rw_fold_local_l hKP hC hc hAC haT rd_menu_l hp hQ ⟨X, hXC, hx, hAX⟩ hQ hf
  obtain ⟨Y, E, hy, he, ha, hq⟩ := ha
  have hYC := hC .pair U U U hU hU hU Y hy
  have hEC := hC .diff U U U hU hU hU E (fun x => iff_of_false (he x) (fun h => h.2 h.1))
  have hPC := rw_domain_closed_l hKP hC hAC hp
  have hA := rd_transitive_enclosed_l hKP hC hAC haT
  have hP := rd_triples_enclosed_l hKP hC hAC haT hPC (by
    intro p hpP; obtain ⟨a, ha, b, hb, c, hc, h⟩ := (hp p).mp hpP; exact ⟨a, b, c, ha, hb, hc, h⟩)
  obtain ⟨Y', hyC, hyT, _, hYY'⟩ := rd_bounded_enclosed_l hKP hC hAC haT hYC (fun x hx => (ha x).mpr (Or.inr hx))
  obtain ⟨E', heC, heT, _, hEE'⟩ := rd_bounded_enclosed_l hKP hC hAC haT hEC (fun x hx => (he x hx).elim)
  have hD := rd_transitive_enclosed_l hKP hC hDC hdT
  obtain ⟨B, hBC, hbT, _, hb⟩ := rd_finite_enclosed_l hKP hC hU hu [A, Q, P, Y, E, D] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h
    · exact h ▸ hA
    · exact h ▸ hQ
    · exact h ▸ hP
    · exact h ▸ ⟨Y', hyC, hyT, hYY'⟩
    · exact h ▸ ⟨E', heC, heT, hEE'⟩
    · exact h ▸ hD)
  exact ⟨B, hBC, hbT, ⟨A, hb A (by simp), Q, hb Q (by simp), P, hb P (by simp),
    Y, hb Y (by simp), E, hb E (by simp), hy, he, ha, hq, hp,
    rw_fold_cert_mono_l hd (hbT D (hb D (by simp)))⟩, hV, hS⟩

/-- 微后继的同一 Σ₁ 公式可在非可容许的传递 rud 闭包内解释。 -/
theorem rw_successor_absolute_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hn : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hn) 2)
    (U V : (rt_model_l C hn).Domain) (hu : M.TransitiveSet U.val)
    (hR : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem (ρ.bound 0).val T) :
    rw_successor_s.schema.denote ρ U V ↔ Rw_successor_d U.val (ρ.bound 0).val V.val (ρ.bound 1).val := by
  let η := image_env_l Subtype.val ρ
  have matrix (B : (rt_model_l C hn).Domain) :
      Formula.satisfies (((ρ.push U).push V).push B) rw_successor_s.matrix.body ↔
        Rw_successor_cert_d B.val U.val (ρ.bound 0).val V.val (ρ.bound 1).val := by
    apply (rt_model_delta_l hc hn rw_successor_s.matrix.delta0 _).trans
    apply Iff.trans ?_ (rw_successor_matrix_l hKP η U.val V.val B.val)
    exact Formula.closed_env_l _ rw_successor_s.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  rw [S1_binary.sat_l]
  simp only [matrix]
  constructor
  · rintro ⟨B, h⟩; exact rw_successor_cert_sound_l h
  · intro h
    obtain ⟨B, hBC, _, hb, _⟩ := rw_successor_local_l hKP hC hc U.property hu hR h
    exact ⟨⟨B, hBC⟩, hb⟩

end YesMetaZFC.SetTheory.InnerModel
