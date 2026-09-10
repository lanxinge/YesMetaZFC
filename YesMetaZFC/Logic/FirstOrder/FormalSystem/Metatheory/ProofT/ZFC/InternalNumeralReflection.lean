import YesMetaZFC.Automation.ObjectNumeralReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralSpecialization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceLocalTests

/-! # 数码实例的可分离反射归纳

归纳的对象性质包含实际数码图和实际可证明性图。零与后继必须分别给出
内部证明码；最终阶段对应保证没有使用外部任意谓词归纳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity PureSourceNumerals
open PureSourceInstantiation ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem atNumber_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (body : SetOpenFormula [.set]) (input : SetTerm bound free) :
    (ObjectNumeralReflection.atNumber ReducedProofPresentation.presentation.graph body input).satisfies env ↔
      ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (input.eval env) named →
        ProvableCode 𝒩 (formula 𝒩 (fun _ => named) body) := by
  simp only [ObjectNumeralReflection.atNumber, Formula.satisfies_forallFreeTop, Formula.satisfies,
    PureSourceNumeralSyntax.satisfies, provableCode_satisfies, ObjectNumeralReflection.instanceCode,
    formula_eval, Term.eval_weakenFree, and_imp]
  rfl

theorem atNumber_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula [.set]) {input : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) :
    (ObjectNumeralReflection.atNumber ReducedProofPresentation.presentation.graph body (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectNumeralReflection.atNumber ReducedProofPresentation.presentation.graph body (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [atNumber_satisfies, atNumber_satisfies]
  apply forall_congr'
  intro named
  change (mem 𝒩 named (w 𝒩) → _) ↔ (mem 𝒩 named (w (canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right
  intro hNamed
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hInput hNamed)
  rw [← formula_agrees h𝒩 (fun _ => hNamed) body]
  exact PureSourceLocalTests.provableCode_agreement h𝒩 (formula_natural h𝒩 (fun _ => hNamed) body)

/-- 已给出证明码构造的零／后继步骤可推广到所有内部自然数。 -/
theorem numeral_induction (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (body : SetOpenFormula [.set])
    (hZero : ProvableCode 𝒩 (formula 𝒩 (fun _ => numeral 𝒩 ObjectNumeralSyntax.zeroCode) body))
    (hStep : ∀ input named, mem 𝒩 input (w 𝒩) → mem 𝒩 named (w 𝒩) →
      PureSourceNumeralSyntax.Graph 𝒩 input named → ProvableCode 𝒩 (formula 𝒩 (fun _ => named) body) →
      ProvableCode 𝒩 (formula 𝒩 (fun _ => PureSourceNumeralSyntax.next 𝒩 named) body))
    {input named : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) body) := by
  have hAll := PureSourceInduction.induction h𝒩
    (ObjectNumeralReflection.atNumber ReducedProofPresentation.presentation.graph body (.fvar .here)) .nil
    (fun _ h => atNumber_agrees h𝒩 body h) (by
      apply (atNumber_satisfies _ _ _).mpr
      intro named hNamed hGraph
      rw [(PureSourceNumeralSyntax.zero_iff h𝒩 hNamed).mp hGraph]
      exact hZero) (by
      intro input hInput hProperty
      apply (atNumber_satisfies _ _ _).mpr
      intro named hNamed hGraph
      obtain ⟨previous, hp, hPrevious, rfl⟩ := (PureSourceNumeralSyntax.successor_iff h𝒩 hInput hNamed).mp hGraph
      exact hStep input previous hInput hp hPrevious ((atNumber_satisfies _ _ _).mp hProperty previous hp hPrevious))
  exact (atNumber_satisfies _ _ _).mp (hAll input hInput) named hNamed hGraph

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
