import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceMappedTransform

/-! # 单槽自由代入与实际点实例化的连接

抽象出的变量在每个量词深度恰好落在点实例化槽位。替换码只要求属于内部 ω，
不要求它是某个外部有限项的编码；目标沿用自由代入的同一个码构造。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceTransformConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem unary_point (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (input : SetOpenFormula [.set]) {value : 𝒩.Carrier .set} (hValue : mem 𝒩 value (w 𝒩)) :
    Graph 3 (numeral 𝒩 2) (z 𝒩) value
      ((IntrinsicQuotation.quote input.abstractFreeTop).eval (Env.empty : Env 𝒩 [] []))
      (formula 𝒩 (fun _ => value) input) := by
  rw [← original_quote]
  exact formula_mapped_transform h𝒩 (original_natural h𝒩) (fun _ => hValue) 2 0 hValue (numeral_lt h𝒩 (by decide))
    (fun {sort} (entry : Variable [] sort) =>
      VariableSubstitution.abstractBound (σ := signature) (free := []) SetSort.set entry)
    (VariableSubstitution.abstractFreeTop (σ := signature) (bound := []) (free := [])) (by
      intro depth sort entry
      have hIndex : entry.index < depth := by
        have h := SyntaxDecode.variable_lt entry
        have hLength : (SyntaxTransform.extend [] depth).length = depth := by
          rw [SyntaxTransform.extend_length]; rfl
        rw [hLength] at h
        exact h
      have h := bound_identity h𝒩 2 true (by simp [ObjectSyntaxTransform.rules])
        (numeral_natural h𝒩 depth) hValue (numeral_natural h𝒩 entry.index)
        (fun _ => numeral_lt h𝒩 hIndex)
      simp only [term_original_tree, SyntaxTransform.boundLift_empty, Nat.zero_add]
      exact h) (by
      intro depth sort entry
      have h := bound_point h𝒩 (numeral_natural h𝒩 depth) hValue
      cases entry with
      | here =>
        rw [term_original_tree]
        have hCode := SyntaxTransform.freeLift_abstract (free := []) depth Variable.here
        change SyntaxEncode.term (SyntaxTransform.freeLift
          (VariableSubstitution.abstractFreeTop (σ := signature) (bound := []) (free := [])) depth Variable.here) =
          SyntaxSubstitution.bvar depth at hCode
        rw [hCode]
        simpa only [Nat.zero_add] using! h
      | there previous => cases previous) 0 input

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
