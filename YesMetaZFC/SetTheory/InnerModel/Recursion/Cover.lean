import YesMetaZFC.SetTheory.InnerModel.Recursion.Uniqueness

/-! # 将实际递归图装配为有界证书

先用 Δ₀ 收集所需限制及算子的见证，再与函数图放入一个实际传递容器。
这一步把纸面递归方程恢复为前一层可供 Σ₁ 收集调用的正规形。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rc_cert_cover_l (hM : M.Models KPi) {n} (φ : S1_binary n) (ρ : Env M n)
    {A B F : M.Domain} (hA : M.TransitiveSet A) (hF : Fn0_d A B F)
    (hs : ∀ a, M.mem a A → ∀ y, Rd_entry_d a y F →
      ∃ R, M.IsRestrictionOf (kp_pair_l (KPi.models_iff_l.mp hM).1) R F a ∧ φ.schema.denote ρ R y) :
    ∃ T, Rc_cert_d φ ρ A F T := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let η := (ρ.push F).push B
  let ψ : Delta0BinarySchema (n + 2) := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1) (Formula.existsMem (.bound 4)
      (.conj (res0_m (.bound 2) (.bound 6) (.bound 4) (.bound 5))
        (.conj (rd_entry0_m (.bound 4) .newest (.bound 6))
          (φ.matrix_m (fun i => .bound ⟨i.val + 7, by omega⟩) (.bound 2) .newest (.bound 1))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (res0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (φ.matrix.delta0.bind_l _))))) }
  have hψ a p : ψ.toBinarySchema.denote η a p ↔ ∃ R, M.mem R p ∧ ∃ w, M.mem w p ∧
      ∃ y, M.mem y B ∧ Res0_d R F a B ∧ Rd_entry_d a y F ∧
        φ.matrix_binary.toBinarySchema.denote (ρ.push R) y w := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      res0_sat_l hKP.1, rd_entry0_sat_l hKP.1, S1_binary.matrix_sat_l]
    rfl
  obtain ⟨D, hD⟩ := KP.collection_exists_d hKP ψ η A (by
    intro a ha
    obtain ⟨y, hyB, hy⟩ := hF.2.1 a ha
    obtain ⟨R, hR, hr⟩ := hs a ha y hy
    obtain ⟨w, hw⟩ := (φ.sat_l ρ R y).mp hr
    obtain ⟨p, hp⟩ := KP.exists_pair hKP R w
    exact ⟨p, (hψ a p).mpr ⟨R, (hp R).mpr (Or.inl rfl), w, (hp w).mpr (Or.inr rfl),
      y, hyB, res0_of_restriction_l hKP hF hR, hy, hw⟩⟩)
  obtain ⟨P, hP⟩ := KP.exists_pair hKP A F
  obtain ⟨Q, hQ⟩ := KP.exists_pair hKP P D
  obtain ⟨T, ht, hQT⟩ := KPi.transitive_cover_l hM Q
  have hPT := ht Q hQT P ((hQ P).mpr (Or.inl rfl))
  have hDT := ht Q hQT D ((hQ D).mpr (Or.inr rfl))
  have hAT := ht P hPT A ((hP A).mpr (Or.inl rfl))
  have hFT := ht P hPT F ((hP F).mpr (Or.inr rfl))
  have hf := fn0_function_l hKP hF
  have hfT : Fn0_d A T F := fn0_of_function_l hKP ⟨hf.1, hf.2.1, fun a ha => by
    obtain ⟨y, _, hy⟩ := hF.2.1 a ha
    exact ⟨y, (rd_entry_transitive_l ht hFT hy).2, hy⟩⟩
  refine ⟨T, ht, hAT, hFT, hA, hfT, fun a ha => ?_⟩
  obtain ⟨p, hpD, hp⟩ := hD a ha
  obtain ⟨R, hRp, w, hwp, y, _, hR, hy, hw⟩ := (hψ a p).mp hp
  have hpT := ht D hDT p hpD
  have hr := res0_restriction_l hKP hF hR
  refine ⟨R, ht p hpT R hRp, res0_of_restriction_l hKP hfT hr, fun z _ hz => ?_⟩
  have he := hF.2.2 a ha y (hF.bound_l hy).2 z (hF.bound_l hz).2 hy hz
  exact ⟨w, ht p hpT w hwp, he ▸ hw⟩

end YesMetaZFC.SetTheory.InnerModel
