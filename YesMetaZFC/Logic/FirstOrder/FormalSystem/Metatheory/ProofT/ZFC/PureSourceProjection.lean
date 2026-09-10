import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceHornConstruction

/-! # 固定字段位置的内部投影轨迹

字段位置是宿主语法参数，输入字段可以是任意内部自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceProjection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceHornConstruction PureSourceTraceComposition
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem values_natural
    {fields : List (𝒩.Carrier .set)} (hFields : ∀ value ∈ fields, mem 𝒩 value (w 𝒩))
    (i : Fin fields.length) : mem 𝒩 fields[i] (w 𝒩) :=
  hFields _ (List.getElem_mem _)

theorem get_list (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (fields : List (𝒩.Carrier .set)) (hFields : ∀ value ∈ fields, mem 𝒩 value (w 𝒩))
    (index : Nat) (hIndex : index < fields.length) :
    Witness (ObjectHorn.step ObjectProjection.rules)
      (node 𝒩 1 [fieldsCode 𝒩 fields, numeral 𝒩 index, fields[index]]) := by
  induction fields generalizing index with
  | nil => cases hIndex
  | cons head tail ih =>
    have hHead := hFields head List.mem_cons_self
    have hTail := fun value hv => hFields value (List.mem_cons_of_mem head hv)
    have hTailCode := fields_natural h𝒩 hTail
    cases index with
    | zero =>
      have h := rule_intro h𝒩 ObjectProjection.rules ObjectProjection.getHead
        (by simp [ObjectProjection.rules])
        (fun i : Fin 3 => [numeral 𝒩 1, head, fieldsCode 𝒩 tail][i])
        (values_natural (fields := [numeral 𝒩 1, head, fieldsCode 𝒩 tail]) (by
          intro value hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl
          · exact numeral_natural h𝒩 1
          · exact hHead
          · exact hTailCode))
        (ObjectProjection.head_variables _ (by simp [ObjectProjection.rules]))
        (by intro guard hg; cases hg) (by intro premise hp; cases hp)
      simpa [ObjectProjection.getHead, expr_node, List.map_cons, List.map_nil,
        exprValue, List.getElem_cons_zero, List.getElem_cons_succ, fieldsCode] using! h
    | succ index =>
      have hIndexTail : index < tail.length := Nat.lt_of_succ_lt_succ hIndex
      have hOutput := hTail tail[index] (List.getElem_mem hIndexTail)
      have h := rule_intro h𝒩 ObjectProjection.rules ObjectProjection.getTail
        (by simp [ObjectProjection.rules])
        (fun i : Fin 5 => [numeral 𝒩 1, head, fieldsCode 𝒩 tail, numeral 𝒩 index, tail[index]][i])
        (values_natural (fields := [numeral 𝒩 1, head, fieldsCode 𝒩 tail, numeral 𝒩 index, tail[index]]) (by
          intro value hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl
          · exact numeral_natural h𝒩 1
          · exact hHead
          · exact hTailCode
          · exact numeral_natural h𝒩 index
          · exact hOutput))
        (ObjectProjection.head_variables _ (by simp [ObjectProjection.rules]))
        (by intro guard hg; cases hg) (by
          intro premise hp
          have hpEq := List.mem_singleton.mp hp
          subst premise
          simpa [ObjectProjection.getTail, expr_node, List.map_cons, List.map_nil,
            exprValue, List.getElem_cons_zero, List.getElem_cons_succ] using! ih hTail index hIndexTail)
      simpa [ObjectProjection.getTail, expr_node, List.map_cons, List.map_nil,
        exprValue, List.getElem_cons_zero, List.getElem_cons_succ, fieldsCode] using! h

/-- 任意自然数字段列表的合法位置都有实际投影轨迹。 -/
theorem field_node (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (tag : Nat)
    (fields : List (𝒩.Carrier .set)) (hFields : ∀ value ∈ fields, mem 𝒩 value (w 𝒩))
    (index : Nat) (hIndex : index < fields.length) :
    Witness (ObjectHorn.step ObjectProjection.rules)
      (node 𝒩 2 [node 𝒩 tag fields, numeral 𝒩 index, fields[index]]) := by
  have h := rule_intro h𝒩 ObjectProjection.rules ObjectProjection.fieldPositive
    (by simp [ObjectProjection.rules])
    (fun i : Fin 4 => [numeral 𝒩 tag, fieldsCode 𝒩 fields, numeral 𝒩 index, fields[index]][i])
    (values_natural (fields := [numeral 𝒩 tag, fieldsCode 𝒩 fields, numeral 𝒩 index, fields[index]]) (by
      intro value hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact numeral_natural h𝒩 tag
      · exact fields_natural h𝒩 hFields
      · exact numeral_natural h𝒩 index
      · exact hFields _ (List.getElem_mem hIndex)))
    (ObjectProjection.head_variables _ (by simp [ObjectProjection.rules]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      have hpEq := List.mem_singleton.mp hp
      subst premise
      simpa [ObjectProjection.fieldPositive, expr_node, List.map_cons, List.map_nil,
        exprValue, List.getElem_cons_zero, List.getElem_cons_succ] using! get_list h𝒩 fields hFields index hIndex)
  simpa [ObjectProjection.fieldPositive, expr_node, List.map_cons, List.map_nil,
    exprValue, List.getElem_cons_zero, List.getElem_cons_succ, node] using! h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceProjection
