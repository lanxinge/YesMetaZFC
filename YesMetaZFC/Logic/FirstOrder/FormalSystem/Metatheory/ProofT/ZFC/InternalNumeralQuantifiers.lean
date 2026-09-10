import YesMetaZFC.Automation.ObjectNumeralQuantifiers
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralEqualityReflection

/-! # 数码量词语义与开放源定理的公共入口 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic
open _root_.YesMetaZFC.Automation RelationalTranslation ModelClosure
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem membership_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (left right : SetTerm bound free) :
    (Formula.rel RelationSymbol.membership (.cons left (.cons right .nil))).satisfies env ↔ mem 𝒩 (left.eval env) (right.eval env) := Iff.rfl

theorem signed_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (truth : SetFormula bound free) (code : SetTerm bound free) :
    (ObjectNumeralReflection.signed ReducedProofPresentation.presentation.graph truth code).satisfies env ↔
      (truth.satisfies env → ReducedProofCodeSemantics.ProvableCode 𝒩 (code.eval env)) ∧
      (¬ truth.satisfies env → ReducedProofCodeSemantics.ProvableCode 𝒩 (PureSourceCoding.node 𝒩 4 [code.eval env])) := by
  simp only [ObjectNumeralReflection.signed, Formula.satisfies, ReducedProofCodeSemantics.provableCode_satisfies,
    PureSourceCoding.node_eval, List.map_cons, List.map_nil]

theorem forallNumeral_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (input : SetTerm bound free) (body : SetFormula bound (.set :: free)) :
    (ObjectNumeralReflection.forallNumeral input body).satisfies env ↔
      ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (input.eval env) named →
        body.satisfies (env.pushFree named) := by
  simp only [ObjectNumeralReflection.forallNumeral, Formula.satisfies_forallFreeTop,
    Formula.satisfies, PureSourceNumeralSyntax.satisfies, Term.eval_weakenFree, and_imp]
  rfl

theorem forallNatural_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (body : SetFormula bound (.set :: free)) :
    (ObjectNumeralReflection.forallNatural body).satisfies env ↔
      ∀ input, mem 𝒩 input (w 𝒩) → body.satisfies (env.pushFree input) := by
  simp only [ObjectNumeralReflection.forallNatural, Formula.satisfies_forallFreeTop, Formula.satisfies]
  rfl

/-- 对任意有限自由上下文统一关闭并重新开放，不按元数重复全称消去。 -/
theorem source_complete {free : SetContext} (body : SetOpenFormula free)
    (h : ∀ (𝒩 : Structure.{0,0,0,0} signature), Theory.Models 𝒩 intrinsic_zfc_theory →
      ∀ env : Env 𝒩 [] free, body.satisfies env) : Derives intrinsic_zfc_theory [] body := by
  apply Metatheory.Derives.forall_close_open
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  exact (forall_close_iff body).mpr (h 𝒩 h𝒩)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
