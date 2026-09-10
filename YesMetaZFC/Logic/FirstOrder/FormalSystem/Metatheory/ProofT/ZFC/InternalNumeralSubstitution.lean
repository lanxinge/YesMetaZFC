import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceSubstitution

/-! # 内部数码命名与固定公式代入的实际连接

同一个合法数码作为代入表唯一条目，输出由完整 AST 的节点代数直接构造。
总性闭句在原理论中推导；它不把验证图的真值替换为内部可证明性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralSubstitution
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem exists_substitution (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula [.set]) {input : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) :
    ∃ named output, mem 𝒩 named (w 𝒩) ∧ mem 𝒩 output (w 𝒩) ∧
      PureSourceNumeralSyntax.Graph 𝒩 input named ∧ PureSourceNumeralSyntax.ClosedTerm 𝒩 named ∧
      PureSourceTransformConstruction.Graph 3 (numeral 𝒩 3) (z 𝒩) (fieldsCode 𝒩 [named])
        ((IntrinsicQuotation.quote body).eval (Env.empty : Env 𝒩 [] [])) output := by
  obtain ⟨named, hNamed, hGraph, hTerm, _⟩ := PureSourceNumeralSyntax.quotation_exists_unique h𝒩 hInput
  exact ⟨named, PureSourceInstantiation.formula 𝒩 (fun _ => named) body, hNamed,
    PureSourceInstantiation.formula_natural h𝒩 (fun _ => hNamed) body,
    hGraph, hTerm, PureSourceInstantiation.unary_substitution h𝒩 body hNamed⟩

theorem total_satisfies (body : SetOpenFormula [.set]) :
    (ObjectNumeralSyntax.substitutionTotal body).TrueIn 𝒩 ↔
      ∀ input, mem 𝒩 input (w 𝒩) → ∃ named output,
        mem 𝒩 named (w 𝒩) ∧ mem 𝒩 output (w 𝒩) ∧
        PureSourceNumeralSyntax.Graph 𝒩 input named ∧ PureSourceNumeralSyntax.ClosedTerm 𝒩 named ∧
        PureSourceTransformConstruction.Graph 3 (numeral 𝒩 3) (z 𝒩) (fieldsCode 𝒩 [named])
          ((IntrinsicQuotation.quote body).eval (Env.empty : Env 𝒩 [] [])) output := by
  simp only [ObjectNumeralSyntax.substitutionTotal, Formula.TrueIn, Formula.satisfies_forallFreeTop,
    Formula.satisfies_existsFreeTop, Formula.satisfies, PureSourceNumeralSyntax.satisfies,
    PureSourceNumeralSyntax.closedTerm_satisfies, PureSourceTransformConstruction.satisfies,
    Term.eval_weakenFree, fields_eval, List.map_cons, List.map_nil, numeral_eval]
  rfl

/-- 原理论内对整个内部 ω 的数码代入总性，不假设输入标准。 -/
theorem total_derives (body : SetOpenFormula [.set]) :
    Derives intrinsic_zfc_theory [] (ObjectNumeralSyntax.substitutionTotal body) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  exact (total_satisfies body).mpr (fun _ hInput => exists_substitution h𝒩 body hInput)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralSubstitution
