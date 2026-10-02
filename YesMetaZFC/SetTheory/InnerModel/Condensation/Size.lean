import YesMetaZFC.SetTheory.InnerModel.Condensation.Collapse
import YesMetaZFC.SetTheory.Collapse.Cardinality

/-! # 凝聚高度的基数界与 GCH 所需的子集保持 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

/-- γ↦Jγ 是从原层索引到该层的实际集合编码单射。 -/
theorem jh_index_injection_l (hM : M.Models KPi) {a B : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a B) :
    ∃ G, M.IsSetInjectionFromTo (kp_pair_l (KPi.models_iff_l.mp hM).1) G a B := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have sat x Y : (rc_value_s jh_op_s).schema.denote (jh_env_l a) x Y ↔ Jh_value_d x Y :=
    Formula.closed_env_l _ (rc_value_s jh_op_s).schema.freeClosed rfl
  obtain ⟨G, hf, he⟩ := s1_function_l hKP (rc_value_s jh_op_s) (jh_env_l a) a B
    (fun x _ => (jh_value_exists_l hM x).imp fun Y hy => (sat x Y).mpr hy)
    (fun x _ Y Z hy hz => jh_value_unique_l hM ((sat x Y).mp hy) ((sat x Z).mp hz))
    (fun x hx Y hy => jh_value_mem_l hM hx ((sat x Y).mp hy) h)
  refine ⟨G, fn0_function_l hKP hf, fun x y Z hx hy => ?_⟩
  obtain ⟨hxa, hx⟩ := (he x Z).mp hx
  obtain ⟨hya, hy⟩ := (he y Z).mp hy
  rcases ha.wellOrder.linear.compare x hxa y hya with eq | hxy | hyx
  · exact hKP.1.eq_of_same_members x y eq
  · exact (KP.mem_irrefl_d hKP Z (jh_value_mem_l hM hxy ((sat x Z).mp hx) ((sat y Z).mp hy))).elim
  · exact (KP.mem_irrefl_d hKP Z (jh_value_mem_l hM hyx ((sat y Z).mp hy) ((sat x Z).mp hx))).elim

theorem jc_size_l (hM : M.Models KPi) {b B X F : M.Domain} (hb : J_d b B) (hf : Mc_iso_d X B F) :
    M.CardinalLessOrEqual (kp_pair_l (KPi.models_iff_l.mp hM).1) b X := by
  obtain ⟨G, hg⟩ := jh_index_injection_l hM hb.1 hb.2
  exact hf.pull_injection_l (KPi.models_iff_l.mp hM).1 hg

/-- 任意大小的 Σ₁ 子结构均凝聚，且返回实际高度单射和传递参数的子集固定。 -/
theorem jc_bounded_condensation_l (hM : M.Models KPi) {a U X : M.Domain} (ha : M.IsOrdinal a)
    (hU : Jh_value_d a U) (s : S1_sub_d X U) : ∃ b B F, J_d b B ∧ Mc_iso_d X B F ∧
      M.CardinalLessOrEqual (kp_pair_l (KPi.models_iff_l.mp hM).1) b X ∧
      ∀ A, M.TransitiveSet A → M.MemberSubset A X → ∀ x, M.mem x X → M.MemberSubset x A → Rd_entry_d x x F := by
  obtain ⟨b, B, F, hb, hf, he⟩ := jc_condensation_l hM ha hU s
  refine ⟨b, B, F, hb, hf, jc_size_l hM hb hf, fun A ht hAX x hx hxa => ?_⟩
  obtain ⟨y, hy⟩ := mc_value_exists_l hM X x
  have eq := mc_fixed_subset_l hM ht hAX hxa hy; subst y
  exact (he x x).mpr ⟨hx, hy⟩

end YesMetaZFC.SetTheory.InnerModel
