import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornRanking
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalCheckedReflection

/-! # 原已检查轨迹的分层内部强归纳

归纳实际公式同时包含原轨迹及其数码实例的可证明性，
并显式核验最终规范解释对应。内部 ω 无外部良基假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceNumerals PureSourceInfinity
open PureSourceTraceComposition PureSourceHornConstruction ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics ObjectHornRanking
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
attribute [local irreducible] InternalPositiveFormula.Positive InternalPositiveFormula.Evaluates
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem checked_step_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (hAgreement : PureSourceHorn.UnaryAgreement h𝒩 localCondition)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩)) (trace : 𝒩.Carrier .set) :
    (ObjectCheckedTrace.step rules localCondition).body.satisfies
      (templateEnv (.cons root (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) ↔
    (ObjectCheckedTrace.step rules localCondition).body.satisfies
      (templateEnv (.cons root (.cons trace .nil)) : Env (canonical h𝒩) [] [.set,.set]) := by
  rw [PureSourceCheckedConstruction.step_satisfies, PureSourceCheckedConstruction.step_satisfies]
  exact and_congr (PureSourceHorn.step_agrees h𝒩 rules hr trace) (hAgreement root hr)

def CheckedRankedAt (𝒩 : Structure.{0,0,0,x} signature) (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (plan : Plan) (phase : Nat) (input : 𝒩.Carrier .set) : Prop :=
  ∀ tag ∈ plan.tags, plan.phase tag = phase → ∀ values : Fin (plan.width tag) → 𝒩.Carrier .set,
    (∀ i, mem 𝒩 (values i) (w 𝒩)) → values (plan.slot tag) = input →
      Witness (ObjectCheckedTrace.step rules localCondition) (node 𝒩 tag (List.ofFn values)) →
        CheckedProv 𝒩 rules localCondition (node 𝒩 tag (List.ofFn values))

theorem checkedRankedAt_satisfies (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary) (plan : Plan) (phase : Nat)
    (input : 𝒩.Carrier .set) :
    (ObjectCheckedReflection.atPhase ReducedProofPresentation.presentation.graph rules localCondition plan phase).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔ CheckedRankedAt 𝒩 rules localCondition plan phase input := by
  simp only [ObjectCheckedReflection.atPhase, allOf_satisfies, List.forall_mem_map, List.mem_filter,
    beq_iff_eq, and_imp, ObjectCheckedReflection.atTag, allNatural_satisfies,
    implication_satisfies, checked_satisfies, checkedAt_satisfies, node_eval, List.map_ofFn,
    Function.comp_def, Term.eval, boundEnv_variable]
  simp only [Formula.satisfies, Term.eval, boundEnv_variable, boundEnv_free]
  rfl

theorem checkedRankedAt_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (hAgreement : PureSourceHorn.UnaryAgreement h𝒩 localCondition)
    (plan : Plan) (phase : Nat) (input : 𝒩.Carrier .set) :
    (ObjectCheckedReflection.atPhase ReducedProofPresentation.presentation.graph rules localCondition plan phase).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectCheckedReflection.atPhase ReducedProofPresentation.presentation.graph rules localCondition plan phase).satisfies
      (templateEnv (.cons input .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [checkedRankedAt_satisfies, checkedRankedAt_satisfies]
  unfold CheckedRankedAt
  apply forall_congr'; intro tag
  apply imp_congr_right; intro _
  apply imp_congr_right; intro _
  apply forall_congr'; intro values
  change ((∀ i, mem 𝒩 (values i) (w 𝒩)) → _) ↔
    ((∀ i, mem 𝒩 (values i) (w (canonical h𝒩))) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro hv
  apply imp_congr_right; intro _
  have hn : ∀ v ∈ List.ofFn values, mem 𝒩 v (w 𝒩) := by
    intro v h; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h; exact hv i
  have he := node_agrees h𝒩 tag hn
  have ht := witness_agrees h𝒩 (ObjectCheckedTrace.step rules localCondition) (node 𝒩 tag (List.ofFn values))
    (fun root hr trace => checked_step_agrees h𝒩 rules localCondition hAgreement hr trace)
  have hp := checkedProv_agrees h𝒩 rules localCondition (node_natural h𝒩 tag hn)
  exact imp_congr
    (ht.trans (iff_of_eq (congrArg (fun root => @Witness (canonical h𝒩) (ObjectCheckedTrace.step rules localCondition) root) he)))
    (hp.trans (iff_of_eq (congrArg (CheckedProv (canonical h𝒩) rules localCondition) he)))

/-- 阶段归纳只遍历固定规则标签；每阶段的输入秩覆盖模型整个内部 ω。 -/
theorem checked_valid_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (hPositive : InternalPositiveFormula.Positive 𝒩 localCondition.body)
    (hAgreement : PureSourceHorn.UnaryAgreement h𝒩 localCondition) (plan : Plan)
    (hValid : Valid plan rules)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectCheckedTrace.step rules localCondition) root) : CheckedProv 𝒩 rules localCondition root := by
  have hShapes : Shapes plan rules := fun rule hr =>
    ⟨(hValid rule hr).1, fun premise hp => ((hValid rule hr).2 premise hp).1⟩
  have hPhases (phase : Nat) : ∀ input, mem 𝒩 input (w 𝒩) → CheckedRankedAt 𝒩 rules localCondition plan phase input := by
    induction phase using Nat.strongRecOn with
    | ind phase ih =>
      let property : SetOpenFormula [.set] :=
        ObjectCheckedReflection.atPhase ReducedProofPresentation.presentation.graph rules localCondition plan phase
      have hAll : ∀ input, mem 𝒩 input (w 𝒩) → property.satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) := by
        apply PureSourceInduction.strong_induction h𝒩 property .nil
        · exact fun input _ => checkedRankedAt_agrees h𝒩 rules localCondition hAgreement plan phase input
        · intro input hi hLower
          apply (checkedRankedAt_satisfies rules localCondition plan phase input).mpr
          intro tag ht hPhase fields hf hInput hGraph
          have hFields : ∀ v ∈ List.ofFn fields, mem 𝒩 v (w 𝒩) := by
            intro v hv; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv; exact hf i
          obtain ⟨rule, hRule, values, hv, hHead, hBounds, hGuards, hLocal, hPremises⟩ :=
            PureSourceCheckedConstruction.rule_cases_bounds h𝒩 rules localCondition (node_natural h𝒩 tag hFields) hGraph
          have hShape := hShapes rule hRule
          obtain ⟨head, hh, hValue, hRank⟩ := ranked_frame_values h𝒩 plan values hv rule.head hShape.1
          have hHeadFields : ∀ v ∈ List.ofFn head, mem 𝒩 v (w 𝒩) := by
            intro v hv; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv; exact hh i
          obtain ⟨hTag, hList⟩ := PureSourceCodingInversion.node_injective h𝒩 hFields hHeadFields (hHead.trans hValue)
          subst tag
          have hRankInput : exprValue 𝒩 values (rankExpr plan rule.head) = input := by
            rw [hRank]
            have hEq : fields = head := by
              funext i
              have h := congrArg (fun xs => xs[i.val]?) hList
              simpa only [List.getElem?_ofFn, i.isLt, dif_pos, Option.some.injEq] using h
            rw [← hEq]; exact hInput
          rw [hHead]
          apply checked_rule_bounded_values h𝒩 rules localCondition hPositive rule hRule values hv hBounds hGuards hLocal
          intro premise hp
          obtain ⟨child, hc, hChild, hChildRank⟩ := ranked_frame_values h𝒩 plan values hv premise (hShape.2 premise hp)
          rw [hChild]
          have hGraphChild := hChild ▸ hPremises premise hp
          rcases ((hValid rule hRule).2 premise hp).2 with hPhaseLess | ⟨hPhaseEq, hBelow⟩
          · exact ih (plan.phase (frame premise).1) (hPhase ▸ hPhaseLess)
              _ (hc (plan.slot (frame premise).1)) (frame premise).1 (hShape.2 premise hp).1 rfl child hc rfl hGraphChild
          · have hLess := PureSourceSyntaxRank.below_value h𝒩 values hv (below_sound hBelow)
            rw [hRankInput, hChildRank] at hLess
            exact (checkedRankedAt_satisfies rules localCondition plan phase _).mp (hLower _ hLess)
              (frame premise).1 (hShape.2 premise hp).1 (hPhaseEq.trans hPhase) child hc rfl hGraphChild
      intro input hi
      exact (checkedRankedAt_satisfies rules localCondition plan phase input).mp (hAll input hi)
  obtain ⟨rule, hRule, values, hv, he, _, _, _, _⟩ := PureSourceCheckedConstruction.rule_cases_bounds h𝒩 rules localCondition hr hg
  obtain ⟨fields, hf, hValue, _⟩ := ranked_frame_values h𝒩 plan values hv rule.head (hShapes rule hRule).1
  rw [he.trans hValue] at hg ⊢
  exact hPhases (plan.phase (frame rule.head).1) _ (hf (plan.slot (frame rule.head).1))
    (frame rule.head).1 (hShapes rule hRule).1.1 rfl fields hf rfl hg

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
