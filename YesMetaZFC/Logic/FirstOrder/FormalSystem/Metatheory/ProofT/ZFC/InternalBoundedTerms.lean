import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBoundedExistence

/-! # 从界项求值到原有界量词正文的反射 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

def boundedAt (universal : Bool) (body : SetFormula [.set] free) (limit : SetOpenTerm free) : SetOpenFormula free :=
  if universal then ObjectBoundedReflection.allAt body limit else ObjectBoundedReflection.existsAt body limit

def boundedBody (universal : Bool) (body : SetOpenFormula (.set :: free)) : SetOpenFormula (.set :: free) :=
  boundedAt universal (body.abstractFreeTop.weakenFree SetSort.set) (.fvar .here)

def boundedResult (universal : Bool) (body : SetOpenFormula (.set :: free)) (limit : SetOpenTerm free) : SetOpenFormula (.set :: free) :=
  boundedAt universal (body.abstractFreeTop.weakenFree SetSort.set) (limit.weakenFree SetSort.set)

def boundedEquality (limit : SetOpenTerm free) : SetOpenFormula (.set :: free) :=
  limit.weakenFree SetSort.set ≐ₘ .fvar .here

theorem boundedAt_code (values : Nat → 𝒩.Carrier .set) (universal : Bool)
    (body : SetFormula [.set] free) (limit : SetOpenTerm free) :
    formula 𝒩 values (boundedAt universal body limit) =
      node 𝒩 (if universal then 9 else 10) [node 𝒩 (if universal then 7 else 5)
        [(node 𝒩 2 [(node 𝒩 RelationSymbol.membership.ctorIdx []), (node 𝒩 0 [node 𝒩 0 []]), term 𝒩 values limit]),
          formula 𝒩 values body]] := by
  cases universal <;>
    change node 𝒩 _ [node 𝒩 _ [(node 𝒩 2 [_, _, ObjectCodeInstantiation.term _ _ (limit.weakenBound SetSort.set)]), _]] = _
  all_goals rw [ObjectCodeInstantiation.term_weakenBound]; rfl

theorem boundedResult_code (values : Nat → 𝒩.Carrier .set) (named : 𝒩.Carrier .set)
    (universal positive : Bool) (body : SetOpenFormula (.set :: free)) (limit : SetOpenTerm free) :
    formula 𝒩 (ObjectCodeInstantiation.prepend named values) (polarity positive (boundedResult universal body limit)) =
      formula 𝒩 values (polarity positive (boundedAt universal body.abstractFreeTop limit)) := by
  have h : formula 𝒩 (ObjectCodeInstantiation.prepend named values) (boundedResult universal body limit) =
      formula 𝒩 values (boundedAt universal body.abstractFreeTop limit) := by
    simp only [boundedResult, boundedAt_code, term, ObjectCodeInstantiation.term_weakenFree,
      formula, ObjectCodeInstantiation.formula_weakenFree]
  cases positive with
  | true => exact h
  | false => exact congrArg (fun code => node 𝒩 4 [code]) h

theorem bounded_transport_derives (universal positive : Bool)
    (body : SetOpenFormula (.set :: free)) (limit : SetOpenTerm free) :
    Derives intrinsic_zfc_theory [] (.imp (boundedEquality limit)
      (.imp (polarity positive (boundedBody universal body)) (polarity positive (boundedResult universal body limit)))) := by
  apply source_complete
  intro 𝒩 _ env
  change (limit.weakenFree SetSort.set).eval env = (.fvar .here : SetOpenTerm (.set :: free)).eval env → _
  intro he
  have ht : (boundedBody universal body).satisfies env ↔ (boundedResult universal body limit).satisfies env := by
    cases universal <;> simp only [boundedBody, boundedResult, boundedAt, Bool.false_eq_true, if_false, if_true,
      ObjectBoundedReflection.allAt, ObjectBoundedReflection.existsAt, Formula.satisfies, Arguments.eval, Term.eval_weakenBound]
    all_goals rw [he]
  cases positive with
  | true => exact ht.mp
  | false => exact fun h hr => h (ht.mpr hr)

/-- 算术与编码复合界项均保留原量词 AST，正负方向共用等式替换。 -/
theorem bounded_term_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (universal : Bool) (body : SetOpenFormula (.set :: free))
    (hBody : ∀ input, mem 𝒩 input (w 𝒩) → ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 input named →
      FormulaReflects (env.pushFree input) (ObjectCodeInstantiation.prepend named values) body)
    {limit : SetOpenTerm free} (hl : TermEvaluates env values limit) :
    FormulaReflects env values (boundedAt universal body.abstractFreeTop limit) := by
  obtain ⟨named, hn, hg⟩ := PureSourceNumeralSyntax.total h𝒩 hl.1
  have he := numeralValues_prepend hv hl.1 hn hg
  have hBound : FormulaReflects (env.pushFree (limit.eval env)) (ObjectCodeInstantiation.prepend named values) (boundedBody universal body) := by
    cases universal with
    | true => exact bounded_forall_reflection h𝒩 env values hv body hBody hl.1 hn hg
    | false => exact bounded_exists_reflection h𝒩 env values hv body hBody hl.1 hn hg
  obtain ⟨positive, ht, hp⟩ := reflection_choice hBound
  have hEq : formula 𝒩 (ObjectCodeInstantiation.prepend named values) (boundedEquality limit) =
      termEqualityCode 𝒩 values limit named := by
    change node 𝒩 3 [ObjectCodeInstantiation.term _ _ (limit.weakenFree SetSort.set), named] = _
    rw [ObjectCodeInstantiation.term_weakenFree]
    rfl
  have hProof := values_modus_ponens (values := ObjectCodeInstantiation.prepend named values) h𝒩
    (polarity positive (boundedBody universal body)) _ he hp
      (reflection_rule h𝒩 _ he (bounded_transport_derives universal positive body limit) (hEq.symm ▸ hl.2 named hn hg))
  rw [boundedResult_code] at hProof
  apply reflects_of_signed positive ?_ hProof
  have hs : (boundedBody universal body).satisfies (env.pushFree (limit.eval env)) ↔
      (boundedAt universal body.abstractFreeTop limit).satisfies env := by
    cases universal <;> simp only [boundedBody, boundedAt, Bool.false_eq_true, if_false, if_true,
      ObjectBoundedReflection.allAt, ObjectBoundedReflection.existsAt, Formula.satisfies, Arguments.eval, Term.eval_weakenBound]
    all_goals
      first | apply forall_congr' | apply exists_congr
      intro input
      first | apply imp_congr_right; intro _ | apply and_congr_right; intro _
      change (body.abstractFreeTop.weakenFree SetSort.set).satisfies ((env.pushBound input).pushFree (limit.eval env)) ↔ _
      exact Formula.satisfies_weakenFree _ _ _
  cases positive with
  | true => exact hs.mp ht
  | false => exact fun h => ht (hs.mpr h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
