import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceMappedTransform

/-! # 固定完整 AST 上的非标准参数代入轨迹

量词深度沿固定语法递增，自由变量查表使用内部码值。
所有节点均接入既有模式 3 变换图，不只给出一个外部递归算法。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceTransformConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem term_substitution (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} {table : 𝒩.Carrier .set} (hTable : mem 𝒩 table (w 𝒩))
    (hLookup : ∀ index, index < free.length → Lookup table (numeral 𝒩 index) (values index))
    {sort : SetSort} (input : Term signature bound free sort) (depth : Nat) :
      Graph 1 (numeral 𝒩 3) (numeral 𝒩 depth) table
        (term 𝒩 (originalValues 𝒩) input) (term 𝒩 values input) := by
  have h := term_mapped_transform h𝒩 (original_natural h𝒩) hValues 3 depth hTable (numeral_lt h𝒩 (by decide))
    VariableSubstitution.boundId VariableSubstitution.freeId (by
      intro sort entry
      change Graph 1 _ _ _ (node 𝒩 0 [node 𝒩 entry.index []]) _
      exact bound_identity h𝒩 3 false (by simp [ObjectSyntaxTransform.rules])
        (numeral_natural h𝒩 depth) hTable (numeral_natural h𝒩 entry.index) (by intro h; cases h)) (by
      intro sort entry
      change Graph 1 _ _ _ (originalValues 𝒩 entry.index) _
      exact free_replace h𝒩 (numeral_natural h𝒩 depth) hTable (numeral_natural h𝒩 entry.index)
        (hValues entry.index) (hLookup entry.index (SyntaxDecode.variable_lt entry))) input
  simpa only [Term.substituteMapped_id] using! h

theorem arguments_substitution (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free sorts : SetContext} {table : 𝒩.Carrier .set} (hTable : mem 𝒩 table (w 𝒩))
    (hLookup : ∀ index, index < free.length → Lookup table (numeral 𝒩 index) (values index))
    (input : Arguments signature bound free sorts) (depth : Nat) :
      Graph 2 (numeral 𝒩 3) (numeral 𝒩 depth) table
        (fieldsCode 𝒩 (arguments 𝒩 (originalValues 𝒩) input)) (fieldsCode 𝒩 (arguments 𝒩 values input)) := by
  have h := arguments_mapped_transform h𝒩 (original_natural h𝒩) hValues 3 depth hTable (numeral_lt h𝒩 (by decide))
    VariableSubstitution.boundId VariableSubstitution.freeId (by
      intro sort entry
      change Graph 1 _ _ _ (node 𝒩 0 [node 𝒩 entry.index []]) _
      exact bound_identity h𝒩 3 false (by simp [ObjectSyntaxTransform.rules])
        (numeral_natural h𝒩 depth) hTable (numeral_natural h𝒩 entry.index) (by intro h; cases h)) (by
      intro sort entry
      change Graph 1 _ _ _ (originalValues 𝒩 entry.index) _
      exact free_replace h𝒩 (numeral_natural h𝒩 depth) hTable (numeral_natural h𝒩 entry.index)
        (hValues entry.index) (hLookup entry.index (SyntaxDecode.variable_lt entry))) input
  simpa only [Arguments.substituteMapped_id] using! h

theorem formula_substitution (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} {table : 𝒩.Carrier .set} (hTable : mem 𝒩 table (w 𝒩))
    (hLookup : ∀ index, index < free.length → Lookup table (numeral 𝒩 index) (values index))
    (input : SetFormula bound free) (depth : Nat) :
    Graph 3 (numeral 𝒩 3) (numeral 𝒩 depth) table
      (formula 𝒩 (originalValues 𝒩) input) (formula 𝒩 values input) := by
  have h := formula_mapped_transform h𝒩 (original_natural h𝒩) hValues 3 depth hTable (numeral_lt h𝒩 (by decide))
    VariableSubstitution.boundId VariableSubstitution.freeId (by
      intro relative sort entry
      simp only [SyntaxTransform.boundLift_id]
      exact bound_identity h𝒩 3 false (by simp [ObjectSyntaxTransform.rules])
        (numeral_natural h𝒩 (depth + relative)) hTable (numeral_natural h𝒩 entry.index) (by intro h; cases h)) (by
      intro relative sort entry
      simp only [SyntaxTransform.freeLift_id]
      exact free_replace h𝒩 (numeral_natural h𝒩 (depth + relative)) hTable (numeral_natural h𝒩 entry.index)
        (hValues entry.index) (hLookup entry.index (SyntaxDecode.variable_lt entry))) 0 input
  simpa only [SyntaxTransform.boundLift, SyntaxTransform.freeLift, Formula.substituteMapped_id, Nat.add_zero] using! h

/-- 单槽数码代入直接连接当前 quotation 与实际变换图。 -/
theorem unary_substitution (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (input : SetOpenFormula [.set]) {value : 𝒩.Carrier .set} (hValue : mem 𝒩 value (w 𝒩)) :
    Graph 3 (numeral 𝒩 3) (z 𝒩) (fieldsCode 𝒩 [value])
      ((IntrinsicQuotation.quote input).eval (Env.empty : Env 𝒩 [] [])) (formula 𝒩 (fun _ => value) input) := by
  rw [← original_quote]
  refine formula_substitution h𝒩 (fun _ => hValue)
    (fields_natural h𝒩 (fields := [value]) (by simp [hValue])) ?_ input 0
  intro index hIndex
  have hZero : index = 0 := by
    have h : index < 1 := hIndex
    omega
  subst index
  exact lookup_list h𝒩 [value] (by simp [hValue]) 0 (by simp)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
