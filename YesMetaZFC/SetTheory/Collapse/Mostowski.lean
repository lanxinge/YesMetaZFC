import YesMetaZFC.SetTheory.Collapse.Injectivity
import YesMetaZFC.SetTheory.InnerModel.Recursion.FunctionGraph

/-! # 成员同余结构的内部传递坍塌

成员同余先给出保持并反映隶属关系的满射图；外延性只用于进一步证明单射。
两种情形共用同一递归图和传递值域，不把坍塌映射的存在作为输入。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Mc_map_d (X B F : M.Domain) : Prop where
  function : Fn0_d X B F
  onto : ∀ y, M.mem y B → ∃ a, Rd_entry_d a y F
  member : ∀ a b x y, Rd_entry_d a x F → Rd_entry_d b y F → (M.mem a b ↔ M.mem x y)

structure Mc_iso_d (X B F : M.Domain) : Prop extends Mc_map_d X B F where
  injective : ∀ a b y, Rd_entry_d a y F → Rd_entry_d b y F → a = b

theorem Mc_iso_d.bijection_l (hKP : M.Models KP) {X B F : M.Domain} (h : Mc_iso_d X B F) :
    M.IsSetBijectionFromTo (kp_pair_l hKP) F X B :=
  ⟨⟨fn0_function_l hKP h.function, h.injective⟩,
    fun y hy => (h.onto y hy).imp fun _ ha => ⟨(h.function.bound_l ha).1, ha⟩⟩

theorem mc_quotient_l (hM : M.Models KPi) {X : M.Domain} (hc : Mc_congr_d X) :
    ∃ B F, M.TransitiveSet B ∧ Mc_map_d X B F ∧
      ∀ a b, Rd_entry_d a b F ↔ M.mem a X ∧ Mc_value_d X a b := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨B, hb⟩ := mc_value_exists_l hM X X
  have range y : M.mem y B ↔ ∃ a, M.mem a X ∧ Mc_value_d X a y :=
    (mc_value_equation_l hM hb y).trans ⟨fun ⟨a, ha, _, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, ha, h⟩⟩
  obtain ⟨F, fn, hf⟩ := s1_function_l hKP (rc_value_s mc_op_s) (mc_env_l X) X B
    (fun a _ => (mc_value_exists_l hM X a).imp fun b hb => (rc_value_sat_l hKP.1 ..).mpr hb)
    (fun _ _ _ _ h g => mc_value_unique_l hM ((rc_value_sat_l hKP.1 ..).mp h) ((rc_value_sat_l hKP.1 ..).mp g))
    (fun a ha y hy => (range y).mpr ⟨a, ha, (rc_value_sat_l hKP.1 ..).mp hy⟩)
  have entry a b : Rd_entry_d a b F ↔ M.mem a X ∧ Mc_value_d X a b :=
    (hf a b).trans (and_congr_right fun _ => rc_value_sat_l hKP.1 mc_op_s (mc_env_l X) a b)
  have trans : M.TransitiveSet B := by
    intro y hy z hz
    obtain ⟨a, _, ha⟩ := (range y).mp hy
    obtain ⟨b, _, hb, h⟩ := (mc_value_equation_l hM ha z).mp hz
    exact (range z).mpr ⟨b, hb, h⟩
  refine ⟨B, F, trans, ⟨fn, ?_, ?_⟩, entry⟩
  · intro y hy
    obtain ⟨a, ha, h⟩ := (range y).mp hy
    exact ⟨a, (entry a y).mpr ⟨ha, h⟩⟩
  · intro a b x y ha hb
    obtain ⟨haX, hx⟩ := (entry a x).mp ha
    obtain ⟨hbX, hy⟩ := (entry b y).mp hb
    rw [mc_value_equation_l hM hy x]
    refine ⟨fun hab => ⟨a, hab, haX, hx⟩, fun ⟨c, hcb, hcX, hz⟩ => ?_⟩
    exact (hc a haX c hcX (mc_value_kernel_l hM hc haX hcX hx hz) b hbX).mpr hcb

/-- 外延情形直接收回同一满坍塌的单射性。 -/
theorem mc_collapse_l (hM : M.Models KPi) {X : M.Domain} (he : Mc_ext_d X) :
    ∃ B F, M.TransitiveSet B ∧ Mc_iso_d X B F ∧
      ∀ a b, Rd_entry_d a b F ↔ M.mem a X ∧ Mc_value_d X a b := by
  obtain ⟨B,F,ht,hf,entry⟩ := mc_quotient_l hM he.congr_l
  exact ⟨B,F,ht,⟨hf,fun a b y h g =>
    mc_value_injective_l hM he ((entry a y).mp h).1 ((entry b y).mp g).1
      ((entry a y).mp h).2 ((entry b y).mp g).2⟩,entry⟩

end YesMetaZFC.SetTheory
