import YesMetaZFC.SetTheory.Collapse.Mostowski

/-! # 通过实际坍塌双射回拉集合单射

中间值界在坍塌值域中，因此复合逆映射的图为 Δ₀ 查询，KP 已足够。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Mc_iso_d.pull_injection_l (hKP : M.Models KP) {X B F A G : M.Domain} (h : Mc_iso_d X B F)
    (hg : M.IsSetInjectionFromTo (kp_pair_l hKP) G A B) :
    ∃ H, M.IsSetInjectionFromTo (kp_pair_l hKP) H A X := by
  let ρ : Env M 3 := ⟨Fin.cases B (Fin.cases G (fun _ => F)), fun _ => B⟩
  let δ : Delta0BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (.conj (rd_entry0_m (.bound 2) .newest (.bound 4))
      (rd_entry0_m (.bound 1) .newest (.bound 5)))
    delta0 := .existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)) }
  let φ := S1_binary.of_delta0 δ
  have sat a x : φ.schema.denote ρ a x ↔ ∃ b, M.mem b B ∧ Rd_entry_d a b G ∧ Rd_entry_d x b F := by
    rw [S1_binary.of_delta0_sat_l]
    simp only [BinarySchema.denote, δ, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hKP.1]; rfl
  obtain ⟨H, hf, he⟩ := s1_function_l hKP φ ρ A X (by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hg.1.2.2 a ha
    obtain ⟨x, hx⟩ := h.onto b hb
    exact ⟨x, (sat a x).mpr ⟨b, hb, hab, hx⟩⟩) (by
      intro a _ x y hx hy
      obtain ⟨b, _, hab, hxb⟩ := (sat a x).mp hx
      obtain ⟨c, _, hac, hyc⟩ := (sat a y).mp hy
      have eq := hg.1.1.2 a b c hab hac; subst c
      exact h.injective x y b hxb hyc) (by
        intro a _ x hx
        obtain ⟨b, _, _, hxb⟩ := (sat a x).mp hx
        exact (h.function.bound_l hxb).1)
  refine ⟨H, fn0_function_l hKP hf, fun a c x ha hc => ?_⟩
  obtain ⟨b, _, hab, hxb⟩ := (sat a x).mp ((he a x).mp ha).2
  obtain ⟨d, _, hcd, hxd⟩ := (sat c x).mp ((he c x).mp hc).2
  have eq := (fn0_function_l hKP h.function).1.2 x b d hxb hxd; subst d
  exact hg.2 a c b hab hcd

end YesMetaZFC.SetTheory
