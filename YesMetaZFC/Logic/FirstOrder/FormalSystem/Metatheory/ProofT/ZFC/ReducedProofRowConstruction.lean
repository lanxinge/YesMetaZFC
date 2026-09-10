import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofLocalConstruction

/-! # 实际节点检查到证明轨迹行的内部装配 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofRowConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity PureSourceNumerals
open PureSourceHorn PureSourceHornConstruction PureSourceProjection ReducedProofLocalConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem node_row (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {input : 𝒩.Carrier .set}
    (hInput : mem 𝒩 input (w 𝒩)) (hTest : Holds ReducedProofPresentation.nodeTest.condition input) :
    Holds ReducedProofPresentation.rowTest.condition (node 𝒩 0 (input :: [])) := by
  have hFields : ∀ value ∈ ((input :: []) : List (𝒩.Carrier .set)), mem 𝒩 value (w 𝒩) := by
    intro value hv
    obtain rfl := List.mem_singleton.mp hv
    exact hInput
  have hRow := node_natural h𝒩 0 hFields
  have hPayload := fields_natural h𝒩 hFields
  have hPayloadBound : mem 𝒩 (fieldsCode 𝒩 (input :: [])) (suc 𝒩 (node 𝒩 0 (input :: []))) := by
    apply bound_trans h𝒩 hRow (pair_bounds h𝒩 (numeral_natural h𝒩 0) hPayload).2
    exact (successor_spec h𝒩 _ _).mpr (Or.inl ((successor_spec h𝒩 _ _).mpr (Or.inr rfl)))
  have hInputBound : mem 𝒩 input (suc 𝒩 (node 𝒩 0 (input :: []))) := by
    have h := expr_bound h𝒩 (values := fun _ : Fin 1 => input) (fun _ => hInput)
      (.node (.literal 0) [.var 0]) (index := 0) (by decide +kernel)
    simpa [expr_node, exprValue] using! h
  change Holds (ObjectLocalDecision.template
    (ObjectProofRow.rules (queryTest .projection) ReducedProofPresentation.nodeTest)) _
  apply (ObjectLocalDecision.template_satisfies _ _).mpr
  refine ⟨ObjectProofRow.zeroTagRule (queryTest .projection) ReducedProofPresentation.nodeTest,
    (by simp [ObjectProofRow.rules]), (local_rule_satisfies _ _).mpr
      ⟨(fun i : Fin 2 => [fieldsCode 𝒩 (input :: []), input][i]), ?_, rfl, ?_⟩⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact hPayloadBound
    | succ i =>
      cases i using Fin.cases with
      | zero => exact hInputBound
      | succ i => exact Fin.elim0 i
  · intro query hQuery
    simp only [ObjectProofRow.zeroTagRule, List.mem_cons, List.not_mem_nil, or_false] at hQuery
    rcases hQuery with rfl | rfl
    · simpa [expr_node, exprValue, node] using!
        projection_of_witness (field_node h𝒩 0 (input :: []) hFields 0 (by simp))
    · exact hTest

theorem root_row (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input conclusion : 𝒩.Carrier .set}
    (hInput : mem 𝒩 input (w 𝒩)) (hConclusion : mem 𝒩 conclusion (w 𝒩)) :
    Holds ReducedProofPresentation.rowTest.condition (node 𝒩 1 [input, conclusion]) := by
  let values : Fin 2 → 𝒩.Carrier .set := fun i => [z 𝒩, fieldsCode 𝒩 [input, conclusion]][i]
  have hValues : ∀ i, mem 𝒩 (values i) (w 𝒩) := values_natural
    (fields := [z 𝒩, fieldsCode 𝒩 [input, conclusion]]) (by
      intro value hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact (omega_closed h𝒩).1
      · apply fields_natural h𝒩
        intro value hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hInput
        · exact hConclusion)
  have hHead : node 𝒩 1 [input, conclusion] =
      exprValue 𝒩 values (ObjectProofRow.otherTagRule intrinsic_zfc_theory).head := rfl
  change Holds (ObjectLocalDecision.template
    (ObjectProofRow.rules (queryTest .projection) ReducedProofPresentation.nodeTest)) _
  apply (ObjectLocalDecision.template_satisfies _ _).mpr
  refine ⟨ObjectProofRow.otherTagRule intrinsic_zfc_theory, (by simp [ObjectProofRow.rules]),
    (local_rule_satisfies _ _).mpr ⟨values, ?_, hHead, ?_⟩⟩
  · intro i
    rw [hHead]
    exact expr_bound h𝒩 hValues (ObjectProofRow.otherTagRule intrinsic_zfc_theory).head
      ((by decide +kernel : ∀ j : Fin 2, j ∈ (ObjectProofRow.otherTagRule intrinsic_zfc_theory).head.variables) i)
  · intro query hQuery
    cases hQuery

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofRowConstruction
