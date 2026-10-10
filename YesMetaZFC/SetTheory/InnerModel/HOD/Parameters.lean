import YesMetaZFC.SetTheory.InnerModel.HOD.BracketChoice
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # 两种相对 HOD 的公开陈述与参数包含关系 -/
namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem ha_tc_l (hZF : M.Models ZF) (k : Bool) {A x : M.Domain} : Ha_d k A x ↔
    ∃ T, Tc_d x T ∧ ∀ y, M.mem y T → Oa_d k A y := by
  constructor
  · rintro ⟨S, hs, hx, ho⟩
    obtain ⟨T, ht⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF x
    exact ⟨T, ht, fun y hy => ho y (ht.2.2 S hs hx y hy)⟩
  · exact fun ⟨T, ht, ho⟩ => ⟨T, ht.1, ht.2.1, ho⟩

theorem hb_statement_l (hZF : M.Models ZF) {A x : M.Domain} : Hb_d A x ↔
    ∃ T, Tc_d x T ∧ ∀ y, M.mem y T → Ob_d A y := by
  change Ha_d false A x ↔ _
  rw [ha_tc_l hZF false]
  exact exists_congr fun T => and_congr_right fun _ => forall_congr' fun y => imp_congr_right fun _ => oa_bracket_l

theorem hp_statement_l (hZF : M.Models ZF) {A x : M.Domain} : Hp_d A x ↔
    ∃ T, Tc_d x T ∧ ∀ y, M.mem y T → Op_d A y := ha_tc_l hZF true

theorem hb_subset_hp_l (hZF : M.Models ZF) {A x : M.Domain} (h : Hb_d A x) : Hp_d A x := by
  obtain ⟨T, ht, hx, ho⟩ := h
  exact ⟨T, ht, hx, fun y hy => oa_of_ob_l hZF true (oa_bracket_l.mp (ho y hy))⟩

/-- 传递参数 A 连同其全部成员属于 HOD(A)；一般 A 不附加这一断言。 -/
theorem hp_transitive_parameter_l (hZF : M.Models ZF) {A : M.Domain} (hA : M.TransitiveSet A) : Hp_d A A := by
  obtain ⟨S, hS⟩ := KP.exists_insert (ZF.modelsKP hZF) A A
  refine ⟨S, ?_, (hS A).mpr (Or.inr rfl), fun x hx => ?_⟩
  · intro x hx y hy
    exact (hS y).mpr (Or.inl (((hS x).mp hx).elim (fun hx => hA x hx y hy) (fun he => he ▸ hy)))
  · exact ((hS x).mp hx).elim (fun hx => op_member_l hZF hx) (fun he => he.symm ▸ oa_parameter_l hZF true A)

end YesMetaZFC.SetTheory.InnerModel
