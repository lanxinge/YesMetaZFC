import YesMetaZFC.Automation.ObjectBoundedReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalQuantifierReflection

/-! # 有界全称证明的零点与后继组合 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceNumerals PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

theorem boundedAt_satisfies (env : Env 𝒩 [] free) (body : SetFormula [.set] free) (limit : SetOpenTerm free) :
    (ObjectBoundedReflection.allAt body limit).satisfies env ↔
      ∀ input, mem 𝒩 input (limit.eval env) → body.satisfies (env.pushBound input) := by
  simp only [ObjectBoundedReflection.allAt, Formula.satisfies, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem boundedBody_satisfies (env : Env 𝒩 [] free) (body : SetOpenFormula (.set :: free)) (limit : 𝒩.Carrier .set) :
    (ObjectBoundedReflection.allBody body).satisfies (env.pushFree limit) ↔
      ∀ input, mem 𝒩 input limit → body.satisfies (env.pushFree input) := by
  rw [ObjectBoundedReflection.allBody, boundedAt_satisfies]
  apply forall_congr'; intro input
  apply imp_congr_right; intro _
  change (body.abstractFreeTop.weakenFree SetSort.set).satisfies ((env.pushBound input).pushFree limit) ↔ _
  rw [Formula.satisfies_weakenFree, Formula.satisfies_abstractFreeTop]

theorem boundedNext_satisfies (env : Env 𝒩 [] free) (body : SetOpenFormula (.set :: free)) (limit : 𝒩.Carrier .set) :
    (ObjectBoundedReflection.nextBody body).satisfies (env.pushFree limit) ↔
      ∀ input, mem 𝒩 input (suc 𝒩 limit) → body.satisfies (env.pushFree input) := by
  rw [ObjectBoundedReflection.nextBody, boundedAt_satisfies]
  apply forall_congr'; intro input
  apply imp_congr_right; intro _
  change (body.abstractFreeTop.weakenFree SetSort.set).satisfies ((env.pushBound input).pushFree limit) ↔ _
  rw [Formula.satisfies_weakenFree, Formula.satisfies_abstractFreeTop]

theorem bounded_zero_derives (body : SetOpenFormula (.set :: free)) :
    Derives intrinsic_zfc_theory [] (ObjectBoundedReflection.zeroBody body) := by
  apply source_complete
  intro 𝒩 h𝒩 env
  apply (boundedAt_satisfies _ _ _).mpr
  intro input hi
  exact False.elim (empty_spec h𝒩 input hi)

theorem bounded_step_derives (body : SetOpenFormula (.set :: free)) :
    Derives intrinsic_zfc_theory [] (.imp (ObjectBoundedReflection.allBody body)
      (.imp body (ObjectBoundedReflection.nextBody body))) := by
  apply source_complete
  intro 𝒩 h𝒩 env
  let tail : Env 𝒩 [] free := ⟨env.boundVal, fun entry => env.freeVal (.there entry)⟩
  have he : tail.pushFree (env.freeVal .here) = env := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry; cases entry <;> rfl
  rw [← he]
  simp only [Formula.satisfies, boundedBody_satisfies, boundedNext_satisfies]
  intro hAll hBody input hi
  rcases (successor_spec h𝒩 _ input).mp hi with hi | rfl
  · exact hAll input hi
  · exact hBody

theorem boundedBody_code (body : SetOpenFormula (.set :: free)) (values : Nat → 𝒩.Carrier .set) (named : 𝒩.Carrier .set) :
    formula 𝒩 (ObjectCodeInstantiation.prepend named values) (ObjectBoundedReflection.allBody body) =
      ObjectBoundedReflection.allCode (node 𝒩) (formula 𝒩 values body.abstractFreeTop) named := by
  change ObjectBoundedReflection.allCode (node 𝒩)
    (ObjectCodeInstantiation.formula _ _ (body.abstractFreeTop.weakenFree SetSort.set)) named = _
  rw [ObjectCodeInstantiation.formula_weakenFree]

theorem boundedNext_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula (.set :: free)) (values : Nat → 𝒩.Carrier .set) (named : 𝒩.Carrier .set) :
    formula 𝒩 (ObjectCodeInstantiation.prepend named values) (ObjectBoundedReflection.nextBody body) =
      formula 𝒩 (ObjectCodeInstantiation.prepend (PureSourceNumeralSyntax.next 𝒩 named) values) (ObjectBoundedReflection.allBody body) := by
  rw [boundedBody_code]
  change ObjectBoundedReflection.allCode (node 𝒩)
    (ObjectCodeInstantiation.formula _ _ (body.abstractFreeTop.weakenFree SetSort.set))
    (node 𝒩 2 [(node 𝒩 FunctionSymbol.successor.ctorIdx []), named]) = _
  rw [ObjectCodeInstantiation.formula_weakenFree, successor_symbol h𝒩]
  rfl

theorem bounded_zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula (.set :: free)) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {named : 𝒩.Carrier .set} (hn : mem 𝒩 named (w 𝒩)) (hg : PureSourceNumeralSyntax.Graph 𝒩 (z 𝒩) named) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) (ObjectBoundedReflection.allBody body)) := by
  have he := (PureSourceNumeralSyntax.zero_iff h𝒩 hn).mp hg
  rw [he, boundedBody_code]
  have hp := specialize_values h𝒩 _ (bounded_zero_derives body) hv
  have hc : formula 𝒩 values (ObjectBoundedReflection.zeroBody body) =
      ObjectBoundedReflection.allCode (node 𝒩) (formula 𝒩 values body.abstractFreeTop) (numeral 𝒩 ObjectNumeralSyntax.zeroCode) := by
    change ObjectBoundedReflection.allCode (node 𝒩) (formula 𝒩 values body.abstractFreeTop)
      (node 𝒩 2 [node 𝒩 FunctionSymbol.emptySet.ctorIdx []]) = _
    have hz := zero_term_code h𝒩
    rw [hz]
  rwa [hc] at hp

theorem bounded_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula (.set :: free)) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hAll : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) (ObjectBoundedReflection.allBody body)))
    (hBody : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) body)) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend (PureSourceNumeralSyntax.next 𝒩 named) values)
      (ObjectBoundedReflection.allBody body)) := by
  have he := numeralValues_prepend hv hi hn hg
  have hp := values_modus_ponens (values := ObjectCodeInstantiation.prepend named values) h𝒩 body _ he hBody
    (reflection_rule h𝒩 _ he (bounded_step_derives body) hAll)
  rwa [boundedNext_code h𝒩] at hp

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
