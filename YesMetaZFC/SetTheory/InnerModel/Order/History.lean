import YesMetaZFC.SetTheory.InnerModel.Order.Limit
import YesMetaZFC.SetTheory.InnerModel.Order.OperatorWitness
import YesMetaZFC.SetTheory.InnerModel.Recursion.LocalCover

/-! # 从真实层级证书读取精确短历史

限制图只含当前索引之前的全部状态；其条目由既有递归唯一性识别。
限制图和当前算子的见证均留在原证书的传递界内。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_witness_prefix_l (hM : M.Models KPi) (ρ : Env M 0) {a p T : M.Domain}
    (h : Formula.satisfies (((ρ.push a).push p).push T) (rc_value_s rw_op_s).matrix.body) :
    ∃ G, M.mem G T ∧ ∃ w, M.mem w T ∧ Fn0_d a T G ∧
      (∀ b q, Rd_entry_d b q G ↔ M.mem b a ∧ Js_state_d b q) ∧
      Formula.satisfies (((ρ.push G).push p).push w) rw_op_s.matrix.body := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨A, F, hf, ha, hap⟩ := (rc_matrix_sat_l hKP.1 rw_op_s ρ a p T).mp h
  obtain ⟨G, hGT, hg, hs⟩ := hf.step a ha
  obtain ⟨w, hwT, hw⟩ := hs p (hf.function.bound_l hap).2 hap
  have res := res0_restriction_l hKP hf.function hg
  have value b q : Rc_value_d rw_op_s ρ b q ↔ Js_state_d b q :=
    (rc_value_sat_l hKP.1 ..).symm.trans (js_state_env_l ρ b q)
  have fn : Fn0_d a T G := by
    refine ⟨hg.2.1, fun b hb => ?_, fun b hb q hq r hr hqr hrr => ?_⟩
    · obtain ⟨q, hq, he⟩ := hf.function.2.1 b (hf.hereditary a ha b hb)
      exact ⟨q, hq, (res.2 b q).mpr ⟨hb, he⟩⟩
    · exact hf.function.2.2 b (hf.hereditary a ha b hb) q hq r hr ((res.2 b q).mp hqr).2 ((res.2 b r).mp hrr).2
  refine ⟨G, hGT, w, hwT, fn, fun b q => (res.2 b q).trans ?_, hw⟩
  constructor
  · exact fun ⟨hb, hq⟩ => ⟨hb, (value b q).mp (hf.value_l hq)⟩
  · rintro ⟨hb, hq⟩
    obtain ⟨r, _, hr⟩ := hf.function.2.1 b (hf.hereditary a ha b hb)
    have he := js_state_unique_l hM ((value b r).mp (hf.value_l hr)) hq
    exact ⟨hb, he ▸ hr⟩

theorem js_prefix_op_l (hM : M.Models KPi) (ρ : Env M 0) {a p F B : M.Domain}
    (hp : Js_state_d a p) (hf : Fn0_d a B F)
    (he : ∀ b q, Rd_entry_d b q F ↔ M.mem b a ∧ Js_state_d b q) : rw_op_s.schema.denote ρ F p := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨G, hg, hop, hG⟩ := rc_value_equation_l hM rw_op_s ρ (rw_op_unique_l hKP ρ)
    ((rc_value_sat_l hKP.1 ..).mp ((js_state_env_l ρ a p).mpr hp))
  have eq : F = G := Structure.IsSetRelation.eq_of_pairMember_iff hKP.1 (fn0_function_l hKP hf).1.1 hg (by
    intro b q
    exact (he b q).trans ((hG b q).trans (and_congr_right fun _ =>
      (rc_value_sat_l hKP.1 ..).symm.trans (js_state_env_l ρ b q))).symm)
  exact eq.symm ▸ hop

end YesMetaZFC.SetTheory.InnerModel
