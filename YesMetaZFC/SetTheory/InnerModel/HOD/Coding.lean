import YesMetaZFC.SetTheory.InnerModel.HOD.Relative
import YesMetaZFC.SetTheory.InnerModel.OD.Separation
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 遗传可定义集合的有界序数码

对集合中的每个对象收集一个定义码的序数界，再在并集内保留全部有效代码。
解码器满射到原集合；允许重复代码，故不需要背景模型中的选择公理。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 同一集合内的 OD[A] 对象，其定义码可以同时限制在一个内部序数中。 -/
theorem ob_code_bound_l {A T} (h : ∀ y, M.mem y T → Ob_d A y) :
    ∃ κ, M.IsOrdinal κ ∧ ∀ y, M.mem y T → ∃ q, M.mem q κ ∧ Ob_eval_d I q A y := by
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let φ : BinarySchema 1 := {
    body := .conj (Formula.isOrdinal .newest)
      (Formula.existsMem .newest (ob_eval_m .newest (.bound 3) (.bound 2))) }
  have sat y α : φ.denote ρ y α ↔ M.IsOrdinal α ∧ ∃ q, M.mem q α ∧ Ob_eval_d I q A y := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff,
      Formula.satisfies_isOrdinal_iff, Formula.satisfies_existsMem_iff, ob_eval_sat_l I hZF.1]; rfl
  obtain ⟨C, hC⟩ := ZF.collection_exists_d hZF φ ρ T (fun y hy => by
    obtain ⟨q, hq⟩ := (ob_code_l I hZF).mp (h y hy)
    obtain ⟨α, hα, hs⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF)
      (hq.elim fun _ h => od_eval_ordinal_l I hZF h.1)
    exact ⟨α, (sat y α).mpr ⟨hα, q, hs.predecessor_mem, hq⟩⟩)
  let ψ : UnarySchema 0 := { body := Formula.isOrdinal .newest }
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF ψ ⟨Fin.elim0, fun _ => A⟩ C
  have hD α : M.mem α D ↔ M.mem α C ∧ M.IsOrdinal α := by
    simpa only [ψ, Formula.satisfies_isOrdinal_iff] using! hd α
  obtain ⟨κ, hκ⟩ := KP.exists_union (ZF.modelsKP hZF) D
  refine ⟨κ, Structure.IsOrdinal.of_union (ZF.modelsKP hZF) hκ (fun α ha => ((hD α).mp ha).2), ?_⟩
  intro y hy
  obtain ⟨α, hαC, hh⟩ := hC y hy
  obtain ⟨hα, q, hqα, hq⟩ := (sat y α).mp hh
  exact ⟨q, (hκ q).mpr ⟨α, (hD α).mpr ⟨hαC, hα⟩, hqα⟩, hq⟩

/-- 实际集合解码图：源域可定义且由序数组成，值域精确覆盖给定集合。 -/
theorem ob_code_graph_l {A T} (hT : Ob_d A T) (h : ∀ y, M.mem y T → Ob_d A y) :
    ∃ κ C F, M.IsOrdinal κ ∧ M.MemberSubset C κ ∧ Ob_d A C ∧ Fn0_d C T F ∧
      (∀ q y, Rd_entry_d q y F ↔ M.mem q C ∧ Ob_eval_d I q A y) ∧
      (∀ y, M.mem y T → ∃ q, Rd_entry_d q y F) := by
  obtain ⟨κ, hκ, cover⟩ := ob_code_bound_l hZF h
  let ρ : Env M 2 := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push T
  let φ : UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (ob_eval_m (.bound 1) (.bound 3) .newest) }
  have sat q : φ.denote ρ q ↔ ∃ y, M.mem y T ∧ Ob_eval_d I q A y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, ob_eval_sat_l I hZF.1]; rfl
  obtain ⟨C, hCo, hc⟩ := oa_separation_l hZF false A φ ρ
    (Fin.cases (oa_bracket_l.mpr hT) (fun _ => oa_bracket_l.mpr (ob_parameter_l hZF A)))
    (oa_bracket_l.mpr (ob_ordinal_l hZF A hκ))
  have hC q : M.mem q C ↔ M.mem q κ ∧ ∃ y, M.mem y T ∧ Ob_eval_d I q A y :=
    (hc q).trans (and_congr_right fun _ => sat q)
  let η : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let ψ : BinarySchema 1 := { body := ob_eval_m (.bound 1) (.bound 2) .newest }
  have hs q y : ψ.denote η q y ↔ Ob_eval_d I q A y := ob_eval_sat_l I hZF.1 _ _ _ _
  obtain ⟨F, hf, entry⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η
    (fun q hq => ((hC q).mp hq).2.imp fun y hy => (hs q y).mpr hy.2)
    (fun q _ y z hy hz => ob_eval_unique_l I hZF ((hs q y).mp hy) ((hs q z).mp hz))
    (fun q y hq hy => by
      obtain ⟨z, hz, hqz⟩ := ((hC q).mp hq).2
      exact (ob_eval_unique_l I hZF hqz ((hs q y).mp hy)) ▸ hz)
  have eqn q y : Rd_entry_d q y F ↔ M.mem q C ∧ Ob_eval_d I q A y :=
    (entry q y).trans (and_congr_right fun _ => hs q y)
  refine ⟨κ, C, F, hκ, fun q hq => ((hC q).mp hq).1, oa_bracket_l.mp hCo,
    fn0_of_function_l (ZF.modelsKP hZF) hf, eqn, ?_⟩
  intro y hy
  obtain ⟨q, hqκ, hq⟩ := cover y hy
  exact ⟨q, (eqn q y).mpr ⟨(hC q).mpr ⟨hqκ, y, hy, hq⟩, hq⟩⟩

end YesMetaZFC.SetTheory.InnerModel
