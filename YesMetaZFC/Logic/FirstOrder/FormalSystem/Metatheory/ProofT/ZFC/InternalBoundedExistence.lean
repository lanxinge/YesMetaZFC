import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBoundedReflection

/-! # 有界存在保留原存在／合取正文的正负反射 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInstantiation
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

theorem bounded_exists_duality (body : SetOpenFormula (.set :: free)) :
    Derives intrinsic_zfc_theory [] (.iff (.neg (ObjectBoundedReflection.allBody (.neg body)))
      (ObjectBoundedReflection.existsBody body)) := by
  classical
  apply source_complete
  intro 𝒩 _ env
  change (¬ ∀ input, _ → ¬ _) ↔ ∃ input, _ ∧ _
  constructor
  · intro h
    exact Classical.byContradiction (fun hn => h (fun input hm hb => hn ⟨input, hm, hb⟩))
  · intro h hn
    obtain ⟨input, hm, hb⟩ := h
    exact hn input hm hb

/-- 有界存在也覆盖任意内部自然数界；否定方向消费有界全称组合。 -/
theorem bounded_exists_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (body : SetOpenFormula (.set :: free))
    (hBody : ∀ input, mem 𝒩 input (w 𝒩) → ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 input named →
      FormulaReflects (env.pushFree input) (ObjectCodeInstantiation.prepend named values) body)
    {limit named : 𝒩.Carrier .set} (hl : mem 𝒩 limit (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 limit named) :
    FormulaReflects (env.pushFree limit) (ObjectCodeInstantiation.prepend named values) (ObjectBoundedReflection.existsBody body) := by
  have he := numeralValues_prepend hv hl hn hg
  apply reflection_of_iff h𝒩 _ _ he (bounded_exists_duality body)
  apply negation_reflection h𝒩 _ _ he
  apply bounded_forall_reflection h𝒩 env values hv (.neg body) ?_ hl hn hg
  intro input hi code hc hg
  exact negation_reflection h𝒩 _ _ (numeralValues_prepend hv hi hc hg) (hBody input hi code hc hg)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
