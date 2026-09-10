import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralTraceRules
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBoundedInduction

/-! # 任意内部数码递归轨迹的正反射

归纳变量是模型内部输入，归纳性质是实际对象公式，并已证明最终阶段对应。
前驱来自原图的任意内部集合轨迹；不抽取外部有限列表，也不归纳 Lean 自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceNumerals PureSourceInfinity
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
open ObjectNumeralTraceReflection (template)
set_option autoImplicit false
set_option maxHeartbeats 300000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem numeralTraceAt_satisfies {bound free : SetContext} (env : Env 𝒩 bound free) (input : SetTerm bound free) :
    (ObjectNumeralTraceReflection.atInput ReducedProofPresentation.presentation.graph input).satisfies env ↔
      ∀ output, mem 𝒩 output (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (input.eval env) output →
        ∀ first, mem 𝒩 first (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 (input.eval env) first →
        ∀ second, mem 𝒩 second (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 output second →
          ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) template.body) := by
  simp only [ObjectNumeralTraceReflection.atInput, forallNatural_satisfies, forallNumeral_satisfies,
    implication_satisfies, PureSourceNumeralSyntax.satisfies, provableCode_satisfies,
    formula_eval, Term.eval_weakenFree, ObjectNumeralReflection.map_prepend]
  rfl

theorem numeralTraceAt_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) :
    (ObjectNumeralTraceReflection.atInput ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectNumeralTraceReflection.atInput ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [numeralTraceAt_satisfies, numeralTraceAt_satisfies]
  apply forall_congr'; intro output
  change (mem 𝒩 output (w 𝒩) → _) ↔ (mem 𝒩 output (w (canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro ho
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hi ho)
  apply forall_congr'; intro first
  apply imp_congr_right; intro hf
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hi hf)
  apply forall_congr'; intro second
  apply imp_congr_right; intro hs
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 ho hs)
  exact instance_provability_agrees h𝒩 (fun i => by cases i <;> assumption) rfl template.body

/-- 原数码图的真值产生原证明谓词接受的数码实例证明，输入允许非标准。 -/
theorem numeral_trace_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output first second : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 input first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 output second)
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input output) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) template.body) := by
  let property : SetOpenFormula [.set] :=
    ObjectNumeralTraceReflection.atInput ReducedProofPresentation.presentation.graph (.fvar .here)
  have hAll : ∀ input, mem 𝒩 input (w 𝒩) → property.satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) := by
    apply PureSourceInduction.induction h𝒩 property .nil
    · exact fun _ hi => numeralTraceAt_agrees h𝒩 hi
    · apply (numeralTraceAt_satisfies _ _).mpr
      intro output ho hg first hf hFirst second hs hSecond
      obtain rfl := (PureSourceNumeralSyntax.zero_iff h𝒩 ho).mp hg
      exact numeral_trace_zero h𝒩 hf hs hFirst hSecond
    · intro input hi hProperty
      apply (numeralTraceAt_satisfies _ _).mpr
      intro output ho hg result hr hResult named hn hNamed
      obtain ⟨previous, hp, hPrevious, rfl⟩ := (PureSourceNumeralSyntax.successor_iff h𝒩 hi ho).mp hg
      obtain ⟨first, hf, hFirst⟩ := PureSourceNumeralSyntax.total h𝒩 hi
      obtain ⟨second, hs, hSecond⟩ := PureSourceNumeralSyntax.total h𝒩 hp
      exact numeral_trace_step h𝒩 hi hp hf hs hFirst hSecond hr hn hResult hNamed
        ((numeralTraceAt_satisfies _ _).mp hProperty previous hp hPrevious first hf hFirst second hs hSecond)
  exact (numeralTraceAt_satisfies _ _).mp (hAll input hi) output ho hg first hf hFirst second hs hSecond

theorem numeral_trace_positive_derives : Derives intrinsic_zfc_theory []
    (ObjectNumeralReflection.forallNatural
      (ObjectNumeralTraceReflection.atInput ReducedProofPresentation.presentation.graph (.fvar .here)) : SetSentence) := by
  apply source_complete
  intro 𝒩 h𝒩 env
  apply (forallNatural_satisfies _ _).mpr
  intro input hi
  apply (numeralTraceAt_satisfies _ _).mpr
  intro output ho hg first hf hFirst second hs hSecond
  exact numeral_trace_positive h𝒩 hi ho hf hs hFirst hSecond hg

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
