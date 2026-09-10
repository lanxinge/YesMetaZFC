import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureGodelPairingInversion

/-! # 任意源模型中的结构码单射性

把内部配对单射性传回当前源模型，逐层恢复固定标签和字段列表。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceCodingInversion
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem natural_pure (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {a : 𝒩.Carrier .set}
    (ha : mem 𝒩 a (w 𝒩)) :
    PureModel.membership (PureProjectEmbedding.reduct 𝒩) a
      (PureNaturalInduction.omega (PureZFCModels.reduct_models h𝒩)) := by
  change mem 𝒩 a (PureNaturalInduction.omega (PureZFCModels.reduct_models h𝒩))
  rw [omega_agrees h𝒩] at ha
  simpa only [canonical, omega_final] using ha

theorem pair_injective (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {a b c d : 𝒩.Carrier .set}
    (ha : mem 𝒩 a (w 𝒩)) (hb : mem 𝒩 b (w 𝒩))
    (hc : mem 𝒩 c (w 𝒩)) (hd : mem 𝒩 d (w 𝒩))
    (h : pair 𝒩 a b = pair 𝒩 c d) : a = c ∧ b = d := by
  rw [pairing_agrees h𝒩 ha hb, pairing_agrees h𝒩 hc hd] at h
  apply PureGodelPairingInversion.coordinates_unique (PureZFCModels.reduct_models h𝒩)
    (natural_pure h𝒩 ha) (natural_pure h𝒩 hb) (natural_pure h𝒩 hc) (natural_pure h𝒩 hd)
    (((PureCompletedStage.realizes (PureZFCModels.reduct_models h𝒩)).function
      .godelPairing (.cons a (.cons b .nil)) _).mpr rfl)
  exact ((PureCompletedStage.realizes (PureZFCModels.reduct_models h𝒩)).function
    .godelPairing (.cons c (.cons d .nil)) _).mpr h

theorem successor_injective (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {a b : 𝒩.Carrier .set} (ha : mem 𝒩 a (w 𝒩))
    (h : suc 𝒩 a = suc 𝒩 b) : a = b := by
  rw [successor_agrees h𝒩, successor_agrees h𝒩,
    show suc (canonical h𝒩) a = PureNaturalInduction.succ (PureZFCModels.reduct_models h𝒩) a from succ_final _ _,
    show suc (canonical h𝒩) b = PureNaturalInduction.succ (PureZFCModels.reduct_models h𝒩) b from succ_final _ _] at h
  apply _root_.YesMetaZFC.SetTheory.Structure.SuccessorOf.predecessor_eq
    (PureModel.project_models (PureZFCModels.reduct_models h𝒩)).1
    (PureArithmeticBounds.ordinal _ (natural_pure h𝒩 ha))
    (PureNaturalInduction.succ_project (PureZFCModels.reduct_models h𝒩) a)
  rw [h]
  exact PureNaturalInduction.succ_project (PureZFCModels.reduct_models h𝒩) b

theorem numeral_injective (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {a b : Nat} (h : numeral 𝒩 a = numeral 𝒩 b) : a = b := by
  classical
  by_cases hEq : a = b
  · exact hEq
  · exact False.elim ((intrinsic_zfc_certificate_core.numeral_ne hEq).semantically_entails 𝒩 h𝒩 h)

theorem fields_injective (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : List (𝒩.Carrier .set)}
    (hLeft : ∀ a ∈ left, mem 𝒩 a (w 𝒩)) (hRight : ∀ a ∈ right, mem 𝒩 a (w 𝒩))
    (h : fieldsCode 𝒩 left = fieldsCode 𝒩 right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons b bs =>
      have hB := hRight b List.mem_cons_self
      have hBs := fields_natural h𝒩 (fun a ha => hRight a (List.mem_cons_of_mem b ha))
      have hPair := successor_injective h𝒩 (pairing_spec h𝒩 (numeral_natural h𝒩 0) (omega_closed h𝒩).1).1 h
      have hTag := (pair_injective h𝒩 (numeral_natural h𝒩 0) (omega_closed h𝒩).1
        (numeral_natural h𝒩 1) (pairing_spec h𝒩 hB hBs).1 hPair).1
      exact False.elim (Nat.zero_ne_one (numeral_injective h𝒩 hTag))
  | cons a as ih =>
    have hA := hLeft a List.mem_cons_self
    have hAs := fun value hv => hLeft value (List.mem_cons_of_mem a hv)
    cases right with
    | nil =>
      have hPair := successor_injective h𝒩
        (pairing_spec h𝒩 (numeral_natural h𝒩 1) (pairing_spec h𝒩 hA (fields_natural h𝒩 hAs)).1).1 h
      have hTag := (pair_injective h𝒩 (numeral_natural h𝒩 1)
        (pairing_spec h𝒩 hA (fields_natural h𝒩 hAs)).1 (numeral_natural h𝒩 0) (omega_closed h𝒩).1 hPair).1
      exact False.elim (Nat.zero_ne_one (numeral_injective h𝒩 hTag).symm)
    | cons b bs =>
      have hB := hRight b List.mem_cons_self
      have hBs := fun value hv => hRight value (List.mem_cons_of_mem b hv)
      have hPair := successor_injective h𝒩
        (pairing_spec h𝒩 (numeral_natural h𝒩 1) (pairing_spec h𝒩 hA (fields_natural h𝒩 hAs)).1).1 h
      have hInner := (pair_injective h𝒩 (numeral_natural h𝒩 1)
        (pairing_spec h𝒩 hA (fields_natural h𝒩 hAs)).1 (numeral_natural h𝒩 1)
        (pairing_spec h𝒩 hB (fields_natural h𝒩 hBs)).1 hPair).2
      have hFields := pair_injective h𝒩 hA (fields_natural h𝒩 hAs) hB (fields_natural h𝒩 hBs) hInner
      rw [hFields.1, ih hAs hBs hFields.2]

theorem node_injective (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {tag other : Nat} {left right : List (𝒩.Carrier .set)}
    (hLeft : ∀ a ∈ left, mem 𝒩 a (w 𝒩)) (hRight : ∀ a ∈ right, mem 𝒩 a (w 𝒩))
    (h : node 𝒩 tag left = node 𝒩 other right) : tag = other ∧ left = right := by
  have hPair := successor_injective h𝒩
    (pairing_spec h𝒩 (numeral_natural h𝒩 tag) (fields_natural h𝒩 hLeft)).1 h
  have hParts := pair_injective h𝒩 (numeral_natural h𝒩 tag) (fields_natural h𝒩 hLeft)
    (numeral_natural h𝒩 other) (fields_natural h𝒩 hRight) hPair
  exact ⟨numeral_injective h𝒩 hParts.1, fields_injective h𝒩 hLeft hRight hParts.2⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceCodingInversion
