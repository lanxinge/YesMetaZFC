import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalCodeParameters

/-! # 自然数有界全称的正负反射

正方向通过实际公式归纳组合整个内部区间的证明，负方向使用内部反例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceNumerals PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

theorem boundedCounter_satisfies (env : Env 𝒩 [] free) (body : SetOpenFormula (.set :: free))
    (input limit : 𝒩.Carrier .set) :
    (ObjectBoundedReflection.counterResult body).satisfies ((env.pushFree input).pushFree limit) ↔
      ∀ value, mem 𝒩 value limit → body.satisfies (env.pushFree value) := by
  rw [ObjectBoundedReflection.counterResult, boundedAt_satisfies]
  apply forall_congr'; intro value
  apply imp_congr_right; intro _
  change ((body.abstractFreeTop.weakenFree SetSort.set).weakenFree SetSort.set).satisfies
    (((env.pushBound value).pushFree input).pushFree limit) ↔ _
  rw [Formula.satisfies_weakenFree, Formula.satisfies_weakenFree, Formula.satisfies_abstractFreeTop]

theorem bounded_counter_derives (body : SetOpenFormula (.set :: free)) :
    Derives intrinsic_zfc_theory [] (.imp ObjectBoundedReflection.counterGuard
      (.imp (.neg (body.weakenFree SetSort.set)) (.neg (ObjectBoundedReflection.counterResult body)))) := by
  apply source_complete
  intro 𝒩 _ env
  let tail : Env 𝒩 [] free := ⟨env.boundVal, fun entry => env.freeVal (.there (.there entry))⟩
  have he : (tail.pushFree (env.freeVal (.there .here))).pushFree (env.freeVal .here) = env := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry; cases entry with
      | here => rfl
      | there entry => cases entry <;> rfl
  rw [← he]
  change mem 𝒩 _ _ → ¬ (body.weakenFree SetSort.set).satisfies _ → ¬ (ObjectBoundedReflection.counterResult body).satisfies _
  rw [Formula.satisfies_weakenFree, boundedCounter_satisfies]
  intro hm hn hAll
  exact hn (hAll _ hm)

theorem bounded_counterexample (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula (.set :: free)) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input limit first second : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hl : mem 𝒩 limit (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 input first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 limit second)
    (hm : mem 𝒩 input limit)
    (hp : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first values) (.neg body))) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend second values) (.neg (ObjectBoundedReflection.allBody body))) := by
  let extended := ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values)
  have he := numeralValues_prepend (numeralValues_prepend hv hi hf hFirst) hl hs hSecond
  have hGuard : ProvableCode 𝒩 (formula 𝒩 extended (ObjectBoundedReflection.counterGuard (free := free))) :=
    (order h𝒩 hi hl hf hs hFirst hSecond).1 hm
  have hBody : formula 𝒩 extended (.neg (body.weakenFree SetSort.set)) =
      formula 𝒩 (ObjectCodeInstantiation.prepend first values) (.neg body) := by
    change node 𝒩 4 [ObjectCodeInstantiation.formula _ extended (body.weakenFree SetSort.set)] = _
    rw [ObjectCodeInstantiation.formula_weakenFree]
    rfl
  have hResult : formula 𝒩 extended (.neg (ObjectBoundedReflection.counterResult body)) =
      formula 𝒩 (ObjectCodeInstantiation.prepend second values) (.neg (ObjectBoundedReflection.allBody body)) := by
    change node 𝒩 4 [ObjectBoundedReflection.allCode (node 𝒩)
      (ObjectCodeInstantiation.formula _ extended ((body.abstractFreeTop.weakenFree SetSort.set).weakenFree SetSort.set)) second] = _
    simp only [extended, ObjectCodeInstantiation.formula_weakenFree]
    change node 𝒩 4 [_] = node 𝒩 4 [formula 𝒩 _ (ObjectBoundedReflection.allBody body)]
    rw [boundedBody_code]
  have h := values_modus_ponens (values := extended) h𝒩 (.neg (body.weakenFree SetSort.set)) _ he (hBody.symm ▸ hp)
    (reflection_rule h𝒩 extended he (bounded_counter_derives body) hGuard)
  rwa [hResult] at h

/-- 有界全称保持双向反射；仅子公式的递归反射作为输入。 -/
theorem bounded_forall_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (body : SetOpenFormula (.set :: free))
    (hBody : ∀ input, mem 𝒩 input (w 𝒩) → ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 input named →
      FormulaReflects (env.pushFree input) (ObjectCodeInstantiation.prepend named values) body)
    {limit named : 𝒩.Carrier .set} (hl : mem 𝒩 limit (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 limit named) :
    FormulaReflects (env.pushFree limit) (ObjectCodeInstantiation.prepend named values) (ObjectBoundedReflection.allBody body) := by
  classical
  constructor
  · intro hAll
    have ht := (boundedBody_satisfies env body limit).mp hAll
    exact bounded_bundle h𝒩 body values hv hl hn hg
      (fun input hi hm code hc hg => (hBody input hi code hc hg).1 (ht input hm))
  · intro hNot
    have ht : ¬ ∀ input, mem 𝒩 input limit → body.satisfies (env.pushFree input) :=
      fun h => hNot ((boundedBody_satisfies env body limit).mpr h)
    have hWitness : ∃ input, mem 𝒩 input limit ∧ ¬ body.satisfies (env.pushFree input) := by
      exact Classical.byContradiction (fun hn => ht (fun input hm =>
        Classical.byContradiction (fun hb => hn ⟨input, hm, hb⟩)))
    obtain ⟨input, hm, hb⟩ := hWitness
    have hi := member_natural h𝒩 hl hm
    obtain ⟨code, hc, hCode⟩ := PureSourceNumeralSyntax.total h𝒩 hi
    exact bounded_counterexample h𝒩 body values hv hi hl hc hn hCode hg hm ((hBody input hi code hc hCode).2 hb)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
