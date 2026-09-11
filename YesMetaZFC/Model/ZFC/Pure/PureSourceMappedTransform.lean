import YesMetaZFC.Model.ZFC.Pure.PureSourceInstantiation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxTransformInstances

/-! # 类型化变量像与内部变换图的组合

源端允许类型化代入，源端与目标端均允许任意内部自由变量码。固定 AST 的递归共用
同一变换规则；跨量词的变量合同显式覆盖全部深度。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceTransformConstruction
open SyntaxTransform (extend boundLift freeLift)
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

mutual
theorem term_mapped_transform (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {sourceValues values : Nat → 𝒩.Carrier .set}
    (hSource : ∀ i, mem 𝒩 (sourceValues i) (w 𝒩)) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {sb sf tb tf : SetContext} (mode depth : Nat) {parameter : 𝒩.Carrier .set}
    (hParameter : mem 𝒩 parameter (w 𝒩)) (hSmall : mem 𝒩 (numeral 𝒩 mode) (numeral 𝒩 4))
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), Graph 1 (numeral 𝒩 mode) (numeral 𝒩 depth) parameter
      (term 𝒩 sourceValues (bs entry)) (node 𝒩 0 [node 𝒩 entry.index []]))
    (hf : ∀ {sort} (entry : Variable sf sort), Graph 1 (numeral 𝒩 mode) (numeral 𝒩 depth) parameter
      (term 𝒩 sourceValues (fs entry)) (values entry.index))
    {sort : SetSort} : (input : Term signature sb sf sort) →
      Graph 1 (numeral 𝒩 mode) (numeral 𝒩 depth) parameter
        (term 𝒩 sourceValues (input.substituteMapped bs fs)) (term 𝒩 values input)
  | .bvar entry => hb entry
  | .fvar entry => hf entry
  | .app symbol args => application h𝒩 1 symbol.ctorIdx (Or.inl rfl)
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 depth) hParameter
      (arguments 𝒩 sourceValues (args.substituteMapped bs fs)) (arguments 𝒩 values args)
      (arguments_natural h𝒩 hSource (args.substituteMapped bs fs)) (arguments_natural h𝒩 hValues args)
      (arguments_mapped_transform h𝒩 hSource hValues mode depth hParameter hSmall bs fs hb hf args)

theorem arguments_mapped_transform (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {sourceValues values : Nat → 𝒩.Carrier .set}
    (hSource : ∀ i, mem 𝒩 (sourceValues i) (w 𝒩)) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {sb sf tb tf : SetContext} (mode depth : Nat) {parameter : 𝒩.Carrier .set}
    (hParameter : mem 𝒩 parameter (w 𝒩)) (hSmall : mem 𝒩 (numeral 𝒩 mode) (numeral 𝒩 4))
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ {sort} (entry : Variable sb sort), Graph 1 (numeral 𝒩 mode) (numeral 𝒩 depth) parameter
      (term 𝒩 sourceValues (bs entry)) (node 𝒩 0 [node 𝒩 entry.index []]))
    (hf : ∀ {sort} (entry : Variable sf sort), Graph 1 (numeral 𝒩 mode) (numeral 𝒩 depth) parameter
      (term 𝒩 sourceValues (fs entry)) (values entry.index))
    {sorts : SetContext} : (input : Arguments signature sb sf sorts) →
      Graph 2 (numeral 𝒩 mode) (numeral 𝒩 depth) parameter
        (fieldsCode 𝒩 (arguments 𝒩 sourceValues (input.substituteMapped bs fs)))
        (fieldsCode 𝒩 (arguments 𝒩 values input))
  | .nil => nil_arguments h𝒩 (numeral_natural h𝒩 mode) (numeral_natural h𝒩 depth) hParameter hSmall
  | .cons head tail => cons_arguments h𝒩
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 depth) hParameter
      (term_natural h𝒩 hSource (head.substituteMapped bs fs))
      (fields_natural h𝒩 (arguments_natural h𝒩 hSource (tail.substituteMapped bs fs)))
      (term_natural h𝒩 hValues head) (fields_natural h𝒩 (arguments_natural h𝒩 hValues tail))
      (term_mapped_transform h𝒩 hSource hValues mode depth hParameter hSmall bs fs hb hf head)
      (arguments_mapped_transform h𝒩 hSource hValues mode depth hParameter hSmall bs fs hb hf tail)
end

theorem formula_mapped_transform (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {sourceValues values : Nat → 𝒩.Carrier .set}
    (hSource : ∀ i, mem 𝒩 (sourceValues i) (w 𝒩)) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {sb sf tb tf : SetContext} (mode offset : Nat) {parameter : 𝒩.Carrier .set}
    (hParameter : mem 𝒩 parameter (w 𝒩)) (hSmall : mem 𝒩 (numeral 𝒩 mode) (numeral 𝒩 4))
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf)
    (hb : ∀ depth {sort} (entry : Variable (extend sb depth) sort), Graph 1 (numeral 𝒩 mode) (numeral 𝒩 (offset + depth)) parameter
      (term 𝒩 sourceValues (boundLift bs depth entry)) (node 𝒩 0 [node 𝒩 entry.index []]))
    (hf : ∀ depth {sort} (entry : Variable sf sort), Graph 1 (numeral 𝒩 mode) (numeral 𝒩 (offset + depth)) parameter
      (term 𝒩 sourceValues (freeLift fs depth entry)) (values entry.index))
    (depth : Nat) (input : SetFormula (extend sb depth) sf) :
    Graph 3 (numeral 𝒩 mode) (numeral 𝒩 (offset + depth)) parameter
      (formula 𝒩 sourceValues (input.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula 𝒩 values input) := by
  cases hInput : input with
  | falsum => exact constant h𝒩 0 (Or.inl rfl) (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter hSmall
  | truth => exact constant h𝒩 1 (Or.inr rfl) (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter hSmall
  | rel symbol args =>
    exact application h𝒩 3 symbol.ctorIdx (Or.inr rfl)
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (arguments 𝒩 sourceValues (args.substituteMapped (boundLift bs depth) (freeLift fs depth))) (arguments 𝒩 values args)
      (arguments_natural h𝒩 hSource (args.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (arguments_natural h𝒩 hValues args)
      (arguments_mapped_transform h𝒩 hSource hValues mode (offset + depth) hParameter hSmall _ _ (hb depth) (hf depth) args)
  | equal left right =>
    exact binary h𝒩 3 1 (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (term_natural h𝒩 hSource (left.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (term_natural h𝒩 hSource (right.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (term_natural h𝒩 hValues left) (term_natural h𝒩 hValues right)
      (term_mapped_transform h𝒩 hSource hValues mode (offset + depth) hParameter hSmall _ _ (hb depth) (hf depth) left)
      (term_mapped_transform h𝒩 hSource hValues mode (offset + depth) hParameter hSmall _ _ (hb depth) (hf depth) right)
  | neg body =>
    exact unary h𝒩 4 false (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (formula_natural h𝒩 hSource (body.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hValues body)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth body)
  | conj left right =>
    exact binary h𝒩 5 3 (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (formula_natural h𝒩 hSource (left.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hSource (right.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hValues left)
      (formula_natural h𝒩 hValues right)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth left)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth right)
  | disj left right =>
    exact binary h𝒩 6 3 (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (formula_natural h𝒩 hSource (left.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hSource (right.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hValues left)
      (formula_natural h𝒩 hValues right)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth left)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth right)
  | imp left right =>
    exact binary h𝒩 7 3 (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (formula_natural h𝒩 hSource (left.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hSource (right.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hValues left)
      (formula_natural h𝒩 hValues right)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth left)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth right)
  | iff left right =>
    exact binary h𝒩 8 3 (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (formula_natural h𝒩 hSource (left.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hSource (right.substituteMapped (boundLift bs depth) (freeLift fs depth)))
      (formula_natural h𝒩 hValues left)
      (formula_natural h𝒩 hValues right)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth left)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf depth right)
  | forallE sort body =>
    cases sort
    exact unary h𝒩 9 true (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (formula_natural h𝒩 hSource (body.substituteMapped (boundLift bs (depth + 1)) (freeLift fs (depth + 1))))
      (formula_natural h𝒩 hValues body)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf (depth + 1) body)
  | existsE sort body =>
    cases sort
    exact unary h𝒩 10 true (by simp [ObjectSyntaxTransform.rules])
      (numeral_natural h𝒩 mode) (numeral_natural h𝒩 (offset + depth)) hParameter
      (formula_natural h𝒩 hSource (body.substituteMapped (boundLift bs (depth + 1)) (freeLift fs (depth + 1))))
      (formula_natural h𝒩 hValues body)
      (formula_mapped_transform h𝒩 hSource hValues mode offset hParameter hSmall bs fs hb hf (depth + 1) body)

termination_by sizeOf (SyntaxEncode.formula input)
decreasing_by all_goals simp_all [SyntaxEncode.formula]; all_goals omega

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
