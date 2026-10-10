import YesMetaZFC.SetTheory.InnerModel.Separation.Witness

/-! # 从已有共同界装配层内递归证书

限制图和算子见证已被同一个层内传递集合界住时，只需有限扩大该界。
此处不调用层内收集，也不假定所选层满足 KP。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rc_local_cover_l (hKP : M.Models KP) {C B A F : M.Domain} (hC : Rd_closed_d C)
    (hBC : M.mem B C) (hb : M.TransitiveSet B) (ha : M.TransitiveSet A) (hf : Fn0_d A B F)
    (hA : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem A T)
    (hF : ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem F T) {n} (φ : S1_binary n) (ρ : Env M n)
    (hs : ∀ a, M.mem a A → ∀ y, Rd_entry_d a y F → ∃ G, M.mem G B ∧ ∃ w, M.mem w B ∧
      M.IsRestrictionOf (kp_pair_l hKP) G F a ∧ Formula.satisfies (((ρ.push G).push y).push w) φ.matrix.body) :
    ∃ T, M.mem T C ∧ Rc_cert_d φ ρ A F T := by
  obtain ⟨T, hTC, ht, bt, hL⟩ := rd_finite_enclosed_l hKP hC hBC hb [A, F] (by
    intro X hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx.elim (fun h => h ▸ hA) (fun h => h ▸ hF))
  have fn := fn0_function_l hKP hf
  have fnT : Fn0_d A T F := fn0_of_function_l hKP ⟨fn.1, fn.2.1, fun a ha =>
    (hf.2.1 a ha).elim fun y hy => ⟨y, bt y hy.1, hy.2⟩⟩
  refine ⟨T, hTC, ht, hL A (by simp), hL F (by simp), ha, fnT, fun a ha => ?_⟩
  obtain ⟨y, hyB, hyF⟩ := hf.2.1 a ha
  obtain ⟨G, hGB, w, hwB, hg, hw⟩ := hs a ha y hyF
  refine ⟨G, bt G hGB, res0_of_restriction_l hKP fnT hg, fun z _ hz => ?_⟩
  have he := hf.2.2 a ha y hyB z (hf.bound_l hz).2 hyF hz
  exact ⟨w, bt w hwB, he ▸ hw⟩

theorem Rc_cert_d.in_value_l (hE : Extensional M) {n} {φ : S1_binary n} {ρ : Env M n}
    {C A F T a y : M.Domain} (h : Rc_cert_d φ ρ A F T) (hTC : M.mem T C)
    (ha : M.mem a A) (hy : Rd_entry_d a y F) : Si_cert_d C (rc_value_s φ) ρ a y :=
  ⟨T, hTC, h.trans, (h.function.bound_l hy).2, (rc_matrix_sat_l hE φ ρ a y T).mpr ⟨A, F, h, ha, hy⟩⟩

end YesMetaZFC.SetTheory.InnerModel
