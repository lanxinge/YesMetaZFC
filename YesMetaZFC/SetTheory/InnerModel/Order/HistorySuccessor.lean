import YesMetaZFC.SetTheory.InnerModel.Order.History
import YesMetaZFC.SetTheory.InnerModel.Order.OperatorInsert
import YesMetaZFC.SetTheory.InnerModel.Recursion.LocalRestrict

/-! # 后继索引的短历史留在同一个层内

先限制旧证书至所需前段，再用已经验证的规范微后继更新算子证书，最后追加
新状态。全部限制、计算和见证都在同一传递 rud 闭包中完成。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem js_successor_in_l (hM : M.Models KPi) {C a b p q : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (ρ : Env M 0) (ha : M.IsOrdinal a) (hs : M.SuccessorOf a b)
    (hp : Si_cert_d C (rc_value_s rw_op_s) ρ b p) (hq : Js_state_d a q) :
    Si_cert_d C (rc_value_s rw_op_s) ρ a q := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have hpState := (js_state_env_l ρ b p).mp hp.sound_l
  obtain ⟨U, R, hpUR⟩ := js_state_pair_l hM hpState
  obtain ⟨V, S, hqVS⟩ := js_state_pair_l hM hq
  have hU : Js_value_d b U R := ⟨p, hpState, hpUR⟩
  have hV : Js_value_d a V S := ⟨q, hq, hqVS⟩
  have hb := ha.mem hs.predecessor_mem
  have good := js_coherence_l hM hb hU
  obtain ⟨T, hTC, _, _, hpMat⟩ := hp
  obtain ⟨A, F, cert, hbA, hbpF⟩ := (rc_matrix_sat_l hKP.1 rw_op_s ρ b p T).mp hpMat
  have hbT := cert.trans A cert.domain b hbA
  have haC := rd_succ_closed_l hKP hC (hc T hTC b hbT) hs
  have aA : M.MemberSubset a A := fun x hx => ((hs x).mp hx).elim
    (fun hx => cert.hereditary b hbA x hx) (fun hx => (hKP.1.eq_of_same_members x b hx).symm ▸ hbA)
  obtain ⟨G, B, hBC, hPrefix, gRes⟩ := rc_local_restrict_l hKP hC hc cert hTC ha.transitive aA
    (rd_transitive_enclosed_l hKP hC haC ha.transitive)
  obtain ⟨G₀, hG₀T, g₀, step⟩ := cert.step b hbA
  obtain ⟨w, hwT, hw⟩ := step p (cert.function.bound_l hbpF).2 hbpF
  have old := res0_restriction_l hKP cert.function g₀
  obtain ⟨r, hr, hrF⟩ := hbpF
  have root : Rd_entry_d b p F := ⟨r, hr, hrF⟩
  obtain ⟨H, hH⟩ := KP.exists_insert hKP G₀ r
  have hRes : M.IsRestrictionOf (kp_pair_l hKP) H F a := by
    refine ⟨fun z hz => ?_, fun x y => (rd_entry_insert_l hH hr x y).trans ?_⟩
    · rcases (hH z).mp hz with hz | he
      · exact old.1 z hz
      · exact he.symm ▸ ⟨b, p, hr⟩
    · constructor
      · rintro (h | ⟨he, he'⟩)
        · have h := (old.2 x y).mp h
          exact ⟨(hs x).mpr (Or.inl h.1), h.2⟩
        · subst x; subst y; exact ⟨hs.predecessor_mem, root⟩
      · rintro ⟨hxa, hxy⟩
        rcases (hs x).mp hxa with hxb | hxb
        · exact Or.inl ((old.2 x y).mpr ⟨hxb, hxy⟩)
        · have he := hKP.1.eq_of_same_members x b hxb; subst x
          exact Or.inr ⟨rfl, cert.function.2.2 b hbA y (cert.function.bound_l hxy).2 p
            (cert.function.bound_l root).2 hxy root⟩
  have eq := gRes.eq hKP.1 hRes
  subst G
  have op := rw_op_insert_in_l hKP hC hc hTC cert.trans ρ (rw_op_read_l hKP ρ cert.trans hwT hw)
    hpUR hqVS good.1 good.2.1 (js_value_bounded_l hM hU) (js_successor_l hM hb hs hU hV) hr hH
  exact rc_local_extend_l hKP hC hc hPrefix hBC op

end YesMetaZFC.SetTheory.InnerModel
