import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBoundedRules

/-! # 内部自然数界下逐点证明的组合

归纳性质是实际数码图和证明图组成的公式。前提中的逐点证明可随界增长，
因此不假设模型内部区间在外部有限，也不对任意外部谓词作归纳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceNumerals PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 300000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free parameters : SetContext}

theorem implication_satisfies {bound : SetContext} (env : Env 𝒩 bound parameters) (left right : SetFormula bound parameters) :
    (Formula.imp left right).satisfies env ↔ (left.satisfies env → right.satisfies env) := Iff.rfl

theorem bundleAt_satisfies (env : Env 𝒩 [] parameters) (body : SetOpenFormula (.set :: free))
    (names : Nat → SetOpenTerm parameters) (limit : SetOpenTerm parameters) :
    (ObjectBoundedReflection.bundleAt ReducedProofPresentation.presentation.graph body names limit).satisfies env ↔
      ((∀ input, mem 𝒩 input (w 𝒩) → mem 𝒩 input (limit.eval env) →
        ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 input named →
          ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named (fun i => (names i).eval env)) body)) →
        ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (limit.eval env) named →
          ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named (fun i => (names i).eval env))
            (ObjectBoundedReflection.allBody body))) := by
  simp only [ObjectBoundedReflection.bundleAt, implication_satisfies, membership_satisfies, forallNatural_satisfies, forallNumeral_satisfies,
    provableCode_satisfies, formula_eval, Term.eval_weakenFree, ObjectNumeralReflection.map_prepend]
  rfl

theorem instance_provability_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {source target : Nat → 𝒩.Carrier .set} (hs : ∀ i, mem 𝒩 (source i) (w 𝒩)) (he : source = target)
    (body : SetOpenFormula free) :
    ProvableCode 𝒩 (formula 𝒩 source body) ↔ ProvableCode (canonical h𝒩) (formula (canonical h𝒩) target body) := by
  subst target
  exact (PureSourceLocalTests.provableCode_agreement h𝒩 (formula_natural h𝒩 hs body)).trans
    (iff_of_eq (congrArg (fun code : 𝒩.Carrier .set => ProvableCode (canonical h𝒩) code) (formula_agrees h𝒩 hs body)))

theorem weakened_parameter_eval (args : Values 𝒩.Carrier parameters) (value : 𝒩.Carrier .set)
    (input : SetOpenTerm parameters) :
    (input.weakenFree SetSort.set).eval (templateEnv (.cons value args) : Env 𝒩 [] _) = input.eval (templateEnv args) := by
  rw [ModelClosure.templateEnv_cons, Term.eval_weakenFree]

theorem bundleAt_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (args : Values 𝒩.Carrier parameters) (body : SetOpenFormula (.set :: free))
    (names : Nat → SetOpenTerm parameters)
    (hv : ∀ i, mem 𝒩 ((names i).eval (templateEnv args)) (w 𝒩))
    (he : ∀ i, (names i).eval (templateEnv args : Env 𝒩 [] parameters) =
      (names i).eval (templateEnv args : Env (canonical h𝒩) [] parameters))
    {limit : 𝒩.Carrier .set} (hl : mem 𝒩 limit (w 𝒩)) :
    (ObjectBoundedReflection.bundleAt ReducedProofPresentation.presentation.graph body
      (fun i => (names i).weakenFree SetSort.set) (.fvar .here)).satisfies (templateEnv (.cons limit args) : Env 𝒩 [] _) ↔
    (ObjectBoundedReflection.bundleAt ReducedProofPresentation.presentation.graph body
      (fun i => (names i).weakenFree SetSort.set) (.fvar .here)).satisfies (templateEnv (.cons limit args) : Env (canonical h𝒩) [] _) := by
  rw [bundleAt_satisfies, bundleAt_satisfies]
  apply imp_congr
  · apply forall_congr'; intro input
    change (mem 𝒩 input (w 𝒩) → _) ↔ (mem 𝒩 input (w (canonical h𝒩)) → _)
    rw [← omega_agrees h𝒩]
    apply imp_congr_right; intro hi
    apply imp_congr_right; intro _
    apply forall_congr'; intro named
    apply imp_congr_right; intro hn
    apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hi hn)
    apply instance_provability_agrees h𝒩
    · intro i; cases i with
      | zero => exact hn
      | succ i => exact Eq.mpr (congrArg (fun value => mem 𝒩 value (w 𝒩))
          (weakened_parameter_eval (𝒩 := 𝒩) args limit (names i))) (hv i)
    · apply congrArg (ObjectCodeInstantiation.prepend named)
      funext i
      exact (weakened_parameter_eval (𝒩 := 𝒩) args limit (names i)).trans
        ((he i).trans (weakened_parameter_eval (𝒩 := canonical h𝒩) args limit (names i)).symm)
  · apply forall_congr'; intro named
    change (mem 𝒩 named (w 𝒩) → _) ↔ (mem 𝒩 named (w (canonical h𝒩)) → _)
    rw [← omega_agrees h𝒩]
    apply imp_congr_right; intro hn
    apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hl hn)
    apply instance_provability_agrees h𝒩
    · intro i; cases i with
      | zero => exact hn
      | succ i => exact Eq.mpr (congrArg (fun value => mem 𝒩 value (w 𝒩))
          (weakened_parameter_eval (𝒩 := 𝒩) args limit (names i))) (hv i)
    · apply congrArg (ObjectCodeInstantiation.prepend named)
      funext i
      exact (weakened_parameter_eval (𝒩 := 𝒩) args limit (names i)).trans
        ((he i).trans (weakened_parameter_eval (𝒩 := canonical h𝒩) args limit (names i)).symm)

attribute [local irreducible] ObjectBoundedReflection.bundleAt Formula.satisfies

/-- 所有内部输入实例的证明，组合为任意内部自然数界的全称证明。 -/
theorem bounded_bundle_parameters (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (args : Values 𝒩.Carrier parameters) (body : SetOpenFormula (.set :: free))
    (names : Nat → SetOpenTerm parameters)
    (hv : NumeralValues 𝒩 (fun i => (names i).eval (templateEnv args)))
    (he : ∀ i, (names i).eval (templateEnv args : Env 𝒩 [] parameters) =
      (names i).eval (templateEnv args : Env (canonical h𝒩) [] parameters))
    {limit named : 𝒩.Carrier .set} (hl : mem 𝒩 limit (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 limit named)
    (hp : ∀ input, mem 𝒩 input (w 𝒩) → mem 𝒩 input limit →
      ∀ code, mem 𝒩 code (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 input code →
        ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend code (fun i => (names i).eval (templateEnv args))) body)) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named (fun i => (names i).eval (templateEnv args)))
      (ObjectBoundedReflection.allBody body)) := by
  have hNames (value : 𝒩.Carrier .set) :
      (fun i => ((names i).weakenFree SetSort.set).eval (templateEnv (.cons value args) : Env 𝒩 [] _)) =
        (fun i => (names i).eval (templateEnv args : Env 𝒩 [] parameters)) :=
    funext (fun i => weakened_parameter_eval (𝒩 := 𝒩) args value (names i))
  let property : SetOpenFormula (.set :: parameters) :=
    ObjectBoundedReflection.bundleAt ReducedProofPresentation.presentation.graph body
      (fun i => (names i).weakenFree SetSort.set) (.fvar .here)
  have hAll : ∀ input, mem 𝒩 input (w 𝒩) →
      property.satisfies (templateEnv (.cons input args) : Env 𝒩 [] _) := by
    apply PureSourceInduction.induction h𝒩 property args
    · intro input hi
      exact bundleAt_agrees h𝒩 args body names (numeralValues_natural hv) he hi
    · apply (bundleAt_satisfies (templateEnv (.cons (z 𝒩) args) : Env 𝒩 [] _) body
        (fun i => (names i).weakenFree SetSort.set) (.fvar .here)).mpr
      intro _ named hn hg
      rw [hNames]
      exact bounded_zero h𝒩 body _ hv hn hg
    · intro limit hl hProperty
      apply (bundleAt_satisfies (templateEnv (.cons (suc 𝒩 limit) args) : Env 𝒩 [] _) body
        (fun i => (names i).weakenFree SetSort.set) (.fvar .here)).mpr
      intro hInputs named hn hg
      obtain ⟨prior, hp, hPrior, rfl⟩ := (PureSourceNumeralSyntax.successor_iff h𝒩 hl hn).mp hg
      have hPrevious := (bundleAt_satisfies (templateEnv (.cons limit args) : Env 𝒩 [] _) body
        (fun i => (names i).weakenFree SetSort.set) (.fvar .here)).mp hProperty
      rw [hNames] at hInputs hPrevious ⊢
      apply bounded_step h𝒩 body _ hv hl hp hPrior
      · exact hPrevious
          (fun input hi hm code hc hg => hInputs input hi ((successor_spec h𝒩 limit input).mpr (Or.inl hm)) code hc hg)
          prior hp hPrior
      · exact hInputs limit hl ((successor_spec h𝒩 limit limit).mpr (Or.inr rfl)) prior hp hPrior
  have h := (bundleAt_satisfies (templateEnv (.cons limit args) : Env 𝒩 [] _) body
    (fun i => (names i).weakenFree SetSort.set) (.fvar .here)).mp (hAll limit hl)
  rw [hNames] at h
  exact h hp named hn hg

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
