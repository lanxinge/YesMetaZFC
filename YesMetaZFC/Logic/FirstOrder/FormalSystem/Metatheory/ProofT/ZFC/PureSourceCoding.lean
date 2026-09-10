import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceArithmetic

/-! # 内部自然数上的配对、字段列与节点编码对应

字段列表是有限的语法参数列；每个字段值可以是模型的非标准自然数。
实际 quotation 通过既有 numeral 求值定理连接，不展开巨大编码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceCoding
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceArithmetic
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def numeral (𝒩 : Structure.{0,0,0,x} signature) (number : Nat) : 𝒩.Carrier .set :=
  (numₘ(number) : SetTerm [] []).eval (Env.empty : Env 𝒩 [] [])

theorem numeral_eval {bound free : SetContext} (env : Env 𝒩 bound free) (number : Nat) :
    (numₘ(number) : SetTerm bound free).eval env = numeral 𝒩 number := by
  induction number with
  | zero => rfl
  | succ number ih => exact congrArg (suc 𝒩) ih

theorem numeral_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (number : Nat) :
    mem 𝒩 (numeral 𝒩 number) (w 𝒩) :=
  (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega (free := []) (Γ := []) number).semantically_entails 𝒩 h𝒩

/-- 外部有限序号的严格次序在任意原模型中保持。 -/
theorem numeral_lt (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : Nat} (h : left < right) : mem 𝒩 (numeral 𝒩 left) (numeral 𝒩 right) := by
  induction right with
  | zero => omega
  | succ right ih =>
    apply (successor_spec h𝒩 _ _).mpr
    by_cases hEqual : left = right
    · exact Or.inr (congrArg (numeral 𝒩) hEqual)
    · exact Or.inl (ih (by omega))

theorem pairing_spec (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : 𝒩.Carrier .set} (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩)) :
    mem 𝒩 (pair 𝒩 left right) (w 𝒩) ∧
      (mem 𝒩 left right → pair 𝒩 left right = sum 𝒩 (power 𝒩 right (numeral 𝒩 2)) left) ∧
      ((right = left ∨ mem 𝒩 right left) → pair 𝒩 left right =
        sum 𝒩 (sum 𝒩 (power 𝒩 left (numeral 𝒩 2)) left) right) := by
  have h := (intrinsic_zfc_arithmetic_support.pairing_definition_instance_derives
    (Γ := []) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar .here : SetOpenTerm [.set,.set,.set])).sound h𝒩
      (templateEnv (.cons (pair 𝒩 left right) (.cons left (.cons right .nil)))) (by intro φ h; cases h)
  exact (h ⟨hLeft,hRight⟩).mp rfl

theorem pairing_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {left right : 𝒩.Carrier .set} (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩)) :
    pair 𝒩 left right = pair (canonical h𝒩) left right := by
  have hSource := pairing_spec h𝒩 hLeft hRight
  have hLeft' : mem (canonical h𝒩) left (w (canonical h𝒩)) := omega_agrees h𝒩 ▸ hLeft
  have hRight' : mem (canonical h𝒩) right (w (canonical h𝒩)) := omega_agrees h𝒩 ▸ hRight
  have hTarget := pairing_spec (PureZFCModels.models (PureZFCModels.reduct_models h𝒩))
    hLeft' hRight'
  have hTwo := numeral_natural h𝒩 2
  have hSquare (input : 𝒩.Carrier .set) (hInput : mem 𝒩 input (w 𝒩)) :
      power 𝒩 input (numeral 𝒩 2) = power (canonical h𝒩) input (numeral (canonical h𝒩) 2) :=
    (exponentiation_agrees h𝒩 hInput hTwo).trans
      (congrArg (power (canonical h𝒩) input) (numeral_agrees h𝒩 2))
  have hLower : sum 𝒩 (power 𝒩 right (numeral 𝒩 2)) left =
      sum (canonical h𝒩) (power (canonical h𝒩) right (numeral (canonical h𝒩) 2)) left := by
    have hPower : mem 𝒩 (power 𝒩 right (numeral 𝒩 2)) (w 𝒩) :=
      (specification h𝒩 .exponentiation hRight hTwo).1
    rw [addition_agrees h𝒩 hPower hLeft, hSquare right hRight]
  have hUpper : sum 𝒩 (sum 𝒩 (power 𝒩 left (numeral 𝒩 2)) left) right =
      sum (canonical h𝒩) (sum (canonical h𝒩) (power (canonical h𝒩) left (numeral (canonical h𝒩) 2)) left) right := by
    have hPower : mem 𝒩 (power 𝒩 left (numeral 𝒩 2)) (w 𝒩) :=
      (specification h𝒩 .exponentiation hLeft hTwo).1
    have hSum : mem 𝒩 (sum 𝒩 (power 𝒩 left (numeral 𝒩 2)) left) (w 𝒩) :=
      (specification h𝒩 .addition hPower hLeft).1
    rw [addition_agrees h𝒩 hSum hRight, addition_agrees h𝒩 hPower hLeft, hSquare left hLeft]
  rcases natural_compare h𝒩 hLeft hRight with hEqual | hLess | hGreater
  · exact (hSource.2.2 (Or.inl hEqual.symm)).trans (hUpper.trans (hTarget.2.2 (Or.inl hEqual.symm)).symm)
  · exact (hSource.2.1 hLess).trans (hLower.trans (hTarget.2.1 hLess).symm)
  · exact (hSource.2.2 (Or.inr hGreater)).trans (hUpper.trans (hTarget.2.2 (Or.inr hGreater)).symm)

def fieldsCode (𝒩 : Structure.{0,0,0,x} signature) : List (𝒩.Carrier .set) → 𝒩.Carrier .set
  | [] => suc 𝒩 (pair 𝒩 (numeral 𝒩 0) (z 𝒩))
  | head :: tail => suc 𝒩 (pair 𝒩 (numeral 𝒩 1) (pair 𝒩 head (fieldsCode 𝒩 tail)))

def node (𝒩 : Structure.{0,0,0,x} signature) (tag : Nat) (fields : List (𝒩.Carrier .set)) : 𝒩.Carrier .set :=
  suc 𝒩 (pair 𝒩 (numeral 𝒩 tag) (fieldsCode 𝒩 fields))

theorem fields_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {fields : List (𝒩.Carrier .set)} (hFields : ∀ field ∈ fields, mem 𝒩 field (w 𝒩)) :
    mem 𝒩 (fieldsCode 𝒩 fields) (w 𝒩) := by
  induction fields with
  | nil => exact (omega_closed h𝒩).2 _ ((pairing_spec h𝒩 (numeral_natural h𝒩 0) (omega_closed h𝒩).1).1)
  | cons head tail ih =>
    exact (omega_closed h𝒩).2 _ ((pairing_spec h𝒩 (numeral_natural h𝒩 1)
      ((pairing_spec h𝒩 (hFields head List.mem_cons_self)
        (ih (fun field h => hFields field (List.mem_cons_of_mem head h)))).1)).1)

theorem fields_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {fields : List (𝒩.Carrier .set)} (hFields : ∀ field ∈ fields, mem 𝒩 field (w 𝒩)) :
    fieldsCode 𝒩 fields = fieldsCode (canonical h𝒩) fields := by
  induction fields with
  | nil =>
    change suc 𝒩 (pair 𝒩 (numeral 𝒩 0) (z 𝒩)) = _
    rw [successor_agrees h𝒩, pairing_agrees h𝒩 (numeral_natural h𝒩 0) (omega_closed h𝒩).1]
    exact congrArg (fun zero => suc (canonical h𝒩) (pair (canonical h𝒩) zero zero)) (empty_agrees h𝒩)
  | cons head tail ih =>
    have hHead := hFields head List.mem_cons_self
    have hTail := fun field h => hFields field (List.mem_cons_of_mem head h)
    change suc 𝒩 (pair 𝒩 (numeral 𝒩 1) (pair 𝒩 head (fieldsCode 𝒩 tail))) = _
    rw [successor_agrees h𝒩, pairing_agrees h𝒩 (numeral_natural h𝒩 1)
      (pairing_spec h𝒩 hHead (fields_natural h𝒩 hTail)).1,
      pairing_agrees h𝒩 hHead (fields_natural h𝒩 hTail)]
    change suc (canonical h𝒩) (pair (canonical h𝒩) (numeral 𝒩 1)
      (pair (canonical h𝒩) head (fieldsCode 𝒩 tail))) =
        suc (canonical h𝒩) (pair (canonical h𝒩) (numeral (canonical h𝒩) 1)
          (pair (canonical h𝒩) head (fieldsCode (canonical h𝒩) tail)))
    rw [show numeral 𝒩 1 = numeral (canonical h𝒩) 1 from numeral_agrees h𝒩 1, ih hTail]

theorem node_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (tag : Nat)
    {fields : List (𝒩.Carrier .set)} (hFields : ∀ field ∈ fields, mem 𝒩 field (w 𝒩)) :
    mem 𝒩 (node 𝒩 tag fields) (w 𝒩) :=
  (omega_closed h𝒩).2 _ (pairing_spec h𝒩 (numeral_natural h𝒩 tag) (fields_natural h𝒩 hFields)).1

theorem node_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (tag : Nat)
    {fields : List (𝒩.Carrier .set)} (hFields : ∀ field ∈ fields, mem 𝒩 field (w 𝒩)) :
    node 𝒩 tag fields = node (canonical h𝒩) tag fields := by
  unfold node
  rw [successor_agrees h𝒩, pairing_agrees h𝒩 (numeral_natural h𝒩 tag) (fields_natural h𝒩 hFields)]
  rw [show numeral 𝒩 tag = numeral (canonical h𝒩) tag from numeral_agrees h𝒩 tag,
    fields_agrees h𝒩 hFields]

theorem fields_eval {bound free : SetContext} (env : Env 𝒩 bound free) (fields : List (SetTerm bound free)) :
    (structural_list_code_term fields).eval env = fieldsCode 𝒩 (fields.map (fun field => field.eval env)) := by
  induction fields with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun rest => suc 𝒩 (pair 𝒩 (numeral 𝒩 1) (pair 𝒩 (head.eval env) rest))) ih

theorem node_eval {bound free : SetContext} (env : Env 𝒩 bound free) (tag : Nat) (fields : List (SetTerm bound free)) :
    (IntrinsicQuotation.node tag fields).eval env = node 𝒩 tag (fields.map (fun field => field.eval env)) := by
  change suc 𝒩 (pair 𝒩 ((numₘ(tag) : SetTerm bound free).eval env)
    ((structural_list_code_term fields).eval env)) = _
  rw [numeral_eval, fields_eval]
  rfl

theorem quotation_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (formula : SetSentence) :
    mem 𝒩 ((IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] [])) (w 𝒩) := by
  have hValue := (IntrinsicQuotation.quote_evaluate intrinsic_zfc_certificate_core formula).semantically_entails 𝒩 h𝒩
  exact hValue.symm ▸ numeral_natural h𝒩 (IntrinsicQuotation.value formula)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceCoding
