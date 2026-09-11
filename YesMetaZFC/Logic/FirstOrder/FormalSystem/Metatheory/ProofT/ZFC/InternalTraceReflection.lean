import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBoundedTerms

/-! # 固定有限轨迹骨架的内部证明装配

行项及其数码可以非标准。由各行的实际检查证明，构造原幂集量词正文的证明。
此入口要求给出有限骨架，不把任意内部轨迹假定为外部有限。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

theorem allOf_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (bodies : List (SetOpenFormula free))
    (hp : ∀ body ∈ bodies, ProvableCode 𝒩 (formula 𝒩 values body)) :
    ProvableCode 𝒩 (formula 𝒩 values (ObjectHorn.allOf bodies)) := by
  induction bodies with
  | nil => exact specialize_values h𝒩 .truth Derives.truth_intro hv
  | cons body bodies ih =>
    have ht := ih (fun φ hφ => hp φ (List.mem_cons_of_mem body hφ))
    exact values_modus_ponens (values := values) h𝒩 (ObjectHorn.allOf bodies) _ hv ht
      (reflection_rule h𝒩 values hv (source_complete (.imp body (.imp (ObjectHorn.allOf bodies) (.conj body (ObjectHorn.allOf bodies))))
        (fun _ _ _ h ht => ⟨h, ht⟩)) (hp body List.mem_cons_self))

theorem natural_term_proof (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input : SetOpenTerm free} (hi : TermEvaluates env values input) :
    ProvableCode 𝒩 (formula 𝒩 values (input ∈ₘ ωₘ)) := by
  obtain ⟨named, hn, hg⟩ := PureSourceNumeralSyntax.total h𝒩 hi.1
  have he := numeralValues_prepend hv hi.1 hn hg
  let namedNatural : SetOpenFormula (.set :: free) := .fvar .here ∈ₘ ωₘ
  let result : SetOpenFormula (.set :: free) := input.weakenFree SetSort.set ∈ₘ ωₘ
  have hEq : formula 𝒩 (ObjectCodeInstantiation.prepend named values) (boundedEquality input) = termEqualityCode 𝒩 values input named := by
    change node 𝒩 3 [ObjectCodeInstantiation.term _ _ (input.weakenFree SetSort.set), named] = _
    rw [ObjectCodeInstantiation.term_weakenFree]
    rfl
  have hRule : Derives intrinsic_zfc_theory [] (.imp (boundedEquality input) (.imp namedNatural result)) := by
    apply source_complete
    intro 𝒩 _ env
    change (input.weakenFree SetSort.set).eval env = env.freeVal .here → mem 𝒩 (env.freeVal .here) (w 𝒩) →
      mem 𝒩 ((input.weakenFree SetSort.set).eval env) (w 𝒩)
    intro he hn
    exact he.symm ▸ hn
  have hNatural : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) namedNatural) := natural h𝒩 hi.1 hn hg
  have h := values_modus_ponens (values := ObjectCodeInstantiation.prepend named values) h𝒩 namedNatural result he hNatural
    (reflection_rule h𝒩 _ he hRule (hEq.symm ▸ hi.2 named hn hg))
  have hc : formula 𝒩 (ObjectCodeInstantiation.prepend named values) result = formula 𝒩 values (input ∈ₘ ωₘ) := by
    exact ObjectCodeInstantiation.formula_weakenFree (node 𝒩) values named (input ∈ₘ ωₘ)
  rwa [hc] at h

theorem finite_trace_derives (step : FormulaTemplate.Binary) (root : SetOpenTerm free)
    (rows : List (SetOpenTerm free)) (hRoot : root ∈ rows) :
    Derives intrinsic_zfc_theory []
      (.imp (ObjectHorn.allOf (rows.map (fun row => row ∈ₘ ωₘ)))
        (.imp (ObjectHorn.allOf (rows.map (fun row => step row (ObjectFiniteSet.term rows))))
          (ObjectTrace.condition step ωₘ root))) := by
  apply Derives.imp_intro
  apply Derives.imp_intro
  apply ObjectTrace.positive intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport intrinsic_zfc_contains_power step ωₘ root rows hRoot
  · intro row hr
    exact ObjectHorn.allOf_elim (formulas := rows.map (fun row => row ∈ₘ ωₘ)) (Derives.assumption (by simp)) (List.mem_map.mpr ⟨row, hr, rfl⟩)
  · intro row hr
    exact ObjectHorn.allOf_elim (Derives.assumption List.mem_cons_self) (List.mem_map.mpr ⟨row, hr, rfl⟩)

/-- 原轨迹正文的内部证明，局部条件保持给定检查器本身。 -/
theorem finite_trace_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (step : FormulaTemplate.Binary) (root : SetOpenTerm free)
    (rows : List (SetOpenTerm free)) (hRoot : root ∈ rows)
    (hRows : ∀ row ∈ rows, TermEvaluates env values row)
    (hSteps : ∀ row ∈ rows, ProvableCode 𝒩 (formula 𝒩 values (step row (ObjectFiniteSet.term rows)))) :
    ProvableCode 𝒩 (formula 𝒩 values (ObjectTrace.condition step ωₘ root)) := by
  have hBound := allOf_values h𝒩 values hv (rows.map (fun row => row ∈ₘ ωₘ)) (by
    intro body hb
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hb
    exact natural_term_proof h𝒩 env values hv (hRows row hr))
  have hStep := allOf_values h𝒩 values hv (rows.map (fun row => step row (ObjectFiniteSet.term rows))) (by
    intro body hb
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hb
    exact hSteps row hr)
  exact values_modus_ponens (values := values) h𝒩 _ _ hv hStep
    (reflection_rule h𝒩 values hv (finite_trace_derives step root rows hRoot) hBound)

theorem checked_trace_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (root : SetOpenTerm free) (rows : List (SetOpenTerm free)) (hRoot : root ∈ rows)
    (hRows : ∀ row ∈ rows, TermEvaluates env values row)
    (hSteps : ∀ row ∈ rows, ProvableCode 𝒩 (formula 𝒩 values
      (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition row (ObjectFiniteSet.term rows)))) :
    ProvableCode 𝒩 (formula 𝒩 values
      (ObjectTrace.condition (ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition) ωₘ root)) :=
  finite_trace_values h𝒩 env values hv _ root rows hRoot hRows hSteps

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
