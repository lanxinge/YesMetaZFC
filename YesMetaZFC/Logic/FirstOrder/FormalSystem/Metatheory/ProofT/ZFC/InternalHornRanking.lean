import YesMetaZFC.Automation.ObjectHornRanking
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceStrongInduction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceSyntaxRank

/-! # 原 Horn 图的分层内部强归纳

固定阶段之间使用宿主自然数归纳，每个阶段的秩覆盖模型的整个内部 ω。
归纳正文由实际量词块、原图和数码实例可证明性组成。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceNumerals PureSourceInfinity
open PureSourceTraceComposition PureSourceHornConstruction ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics ObjectHornRanking
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct
universe x u
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem allNatural_satisfies {free : SetContext} (env : Env 𝒩 [] free) (count : Nat)
    (body : SetFormula (QuineEncoding.project_bound_context count) free) :
    (ObjectHornRanking.allNatural count body).satisfies env ↔
      ∀ values : Fin count → 𝒩.Carrier .set, (∀ i, mem 𝒩 (values i) (w 𝒩)) →
        body.satisfies (boundEnv env count values) := by
  change (¬ (ObjectHorn.quantify count ωₘ (.neg body)).satisfies env) ↔ _
  rw [quantify_satisfies]
  change (¬ ∃ values, (∀ i, mem 𝒩 (values i) (w 𝒩)) ∧ ¬ body.satisfies (boundEnv env count values)) ↔ _
  simp only [not_exists, not_and, Classical.not_not]

def RankedAt (𝒩 : Structure.{0,0,0,x} signature) (rules : List ObjectHorn.Rule)
    (plan : Plan) (phase : Nat) (input : 𝒩.Carrier .set) : Prop :=
  ∀ tag ∈ plan.tags, plan.phase tag = phase → ∀ values : Fin (plan.width tag) → 𝒩.Carrier .set,
    (∀ i, mem 𝒩 (values i) (w 𝒩)) → values (plan.slot tag) = input →
      Witness (ObjectHorn.step rules) (node 𝒩 tag (List.ofFn values)) →
        HornProv 𝒩 rules (node 𝒩 tag (List.ofFn values))

theorem rankedAt_satisfies (rules : List ObjectHorn.Rule) (plan : Plan) (phase : Nat)
    (input : 𝒩.Carrier .set) :
    (ObjectHornRanking.atPhase ReducedProofPresentation.presentation.graph rules plan phase).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔ RankedAt 𝒩 rules plan phase input := by
  simp only [ObjectHornRanking.atPhase, allOf_satisfies, List.forall_mem_map, List.mem_filter,
    beq_iff_eq, and_imp, ObjectHornRanking.atTag, allNatural_satisfies,
    implication_satisfies, horn_satisfies, hornAt_satisfies, node_eval, List.map_ofFn,
    Function.comp_def, Term.eval, boundEnv_variable]
  simp only [Formula.satisfies, Term.eval, boundEnv_variable, boundEnv_free]
  rfl

theorem rankedAt_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (plan : Plan) (phase : Nat) (input : 𝒩.Carrier .set) :
    (ObjectHornRanking.atPhase ReducedProofPresentation.presentation.graph rules plan phase).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectHornRanking.atPhase ReducedProofPresentation.presentation.graph rules plan phase).satisfies
      (templateEnv (.cons input .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [rankedAt_satisfies, rankedAt_satisfies]
  unfold RankedAt
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
  have ht := witness_agrees h𝒩 (ObjectHorn.step rules) (node 𝒩 tag (List.ofFn values))
    (fun root hr trace => PureSourceHorn.step_agrees h𝒩 rules hr trace)
  have hp := hornProv_agrees h𝒩 rules (node_natural h𝒩 tag hn)
  exact imp_congr
    (ht.trans (iff_of_eq (congrArg (fun root => @Witness (canonical h𝒩) (ObjectHorn.step rules) root) he)))
    (hp.trans (iff_of_eq (congrArg (HornProv (canonical h𝒩) rules) he)))

theorem list_values_of_length {α : Type u} {n : Nat} (fields : List α) (h : fields.length = n) :
    ∃ values : Fin n → α, List.ofFn values = fields := by
  subst n
  exact ⟨(fun i => fields[i]), List.ofFn_getElem⟩

/-- 将已核验的固定外壳解释为内部字段；不解码内部语法树。 -/
theorem ranked_frame_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (plan : Plan) {n : Nat} (values : Fin n → 𝒩.Carrier .set)
    (hv : ∀ i, mem 𝒩 (values i) (w 𝒩)) (expr : ObjectHorn.Expr n) (hw : WellFormed plan expr) :
    ∃ fields : Fin (plan.width (frame expr).1) → 𝒩.Carrier .set,
      (∀ i, mem 𝒩 (fields i) (w 𝒩)) ∧
      exprValue 𝒩 values expr = node 𝒩 (frame expr).1 (List.ofFn fields) ∧
      exprValue 𝒩 values (rankExpr plan expr) = fields (plan.slot (frame expr).1) := by
  obtain ⟨terms, he⟩ := list_values_of_length (frame expr).2 hw.2.1
  refine ⟨fun i => exprValue 𝒩 values (terms i), fun i => PureSourceHorn.expr_natural h𝒩 hv _, ?_, ?_⟩
  · calc
      exprValue 𝒩 values expr = exprValue 𝒩 values (.node (.literal (frame expr).1) (frame expr).2) := congrArg _ hw.2.2
      _ = node 𝒩 (frame expr).1 (List.ofFn fun i => exprValue 𝒩 values (terms i)) := by
        rw [expr_node, ← he, List.map_ofFn]
        rfl
  · unfold rankExpr
    rw [← he]
    simp only [List.getElem?_ofFn, Fin.isLt, dif_pos, Option.getD_some]

def RankedDecrease (𝒩 : Structure.{0,0,0,x} signature) (rules : List ObjectHorn.Rule) (plan : Plan) : Prop :=
  ∀ rule ∈ rules, ∀ values : Fin rule.arity → 𝒩.Carrier .set,
    (∀ i, mem 𝒩 (values i) (w 𝒩)) →
    (∀ i, mem 𝒩 (values i) (suc 𝒩 (exprValue 𝒩 values rule.head))) →
    (∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2)) →
    (∀ premise ∈ rule.premises, Witness (ObjectHorn.step rules) (exprValue 𝒩 values premise)) →
    ∀ premise ∈ rule.premises,
      plan.phase (frame premise).1 < plan.phase (frame rule.head).1 ∨
      plan.phase (frame premise).1 = plan.phase (frame rule.head).1 ∧
        mem 𝒩 (exprValue 𝒩 values (rankExpr plan premise)) (exprValue 𝒩 values (rankExpr plan rule.head))

theorem ranked_decrease (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (plan : Plan) (hValid : Valid plan rules) : RankedDecrease 𝒩 rules plan := by
  intro rule hr values hv _ _ _ premise hp
  rcases (hValid rule hr).2 premise hp |>.2 with h | ⟨he, hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨he, PureSourceSyntaxRank.below_value h𝒩 values hv (below_sound hb)⟩

/-- 源模型中的实际下降性也可消费先前阶段证明出的图不变量。 -/
theorem horn_ranked_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (plan : Plan)
    (hShapes : ∀ rule ∈ rules, WellFormed plan rule.head ∧ ∀ premise ∈ rule.premises, WellFormed plan premise)
    (hDecrease : RankedDecrease 𝒩 rules plan)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step rules) root) : HornProv 𝒩 rules root := by
  have hPhases (phase : Nat) : ∀ input, mem 𝒩 input (w 𝒩) → RankedAt 𝒩 rules plan phase input := by
    induction phase using Nat.strongRecOn with
    | ind phase ih =>
      let property : SetOpenFormula [.set] := ObjectHornRanking.atPhase ReducedProofPresentation.presentation.graph rules plan phase
      have hAll : ∀ input, mem 𝒩 input (w 𝒩) → property.satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) := by
        apply PureSourceInduction.strong_induction h𝒩 property .nil
        · exact fun input _ => rankedAt_agrees h𝒩 rules plan phase input
        · intro input hi hLower
          apply (rankedAt_satisfies rules plan phase input).mpr
          intro tag ht hPhase fields hf hInput hGraph
          have hFields : ∀ v ∈ List.ofFn fields, mem 𝒩 v (w 𝒩) := by
            intro v hv; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv; exact hf i
          obtain ⟨rule, hRule, values, hv, hHead, hBounds, hGuards, hPremises⟩ :=
            rule_cases_bounds h𝒩 rules (node_natural h𝒩 tag hFields) hGraph
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
          apply horn_rule_bounded_values h𝒩 rules rule hRule values hv hBounds hGuards
          intro premise hp
          obtain ⟨child, hc, hChild, hChildRank⟩ := ranked_frame_values h𝒩 plan values hv premise (hShape.2 premise hp)
          rw [hChild]
          have hGraphChild := hChild ▸ hPremises premise hp
          rcases hDecrease rule hRule values hv hBounds hGuards hPremises premise hp with hPhaseLess | ⟨hPhaseEq, hLess⟩
          · exact ih (plan.phase (frame premise).1) (hPhase ▸ hPhaseLess)
              _ (hc (plan.slot (frame premise).1)) (frame premise).1 (hShape.2 premise hp).1 rfl child hc rfl hGraphChild
          · rw [hRankInput, hChildRank] at hLess
            exact (rankedAt_satisfies rules plan phase _).mp (hLower _ hLess)
              (frame premise).1 (hShape.2 premise hp).1 (hPhaseEq.trans hPhase) child hc rfl hGraphChild
      intro input hi
      exact (rankedAt_satisfies rules plan phase input).mp (hAll input hi)
  obtain ⟨rule, hRule, values, hv, he, _, _, _⟩ := rule_cases_bounds h𝒩 rules hr hg
  obtain ⟨fields, hf, hValue, _⟩ := ranked_frame_values h𝒩 plan values hv rule.head (hShapes rule hRule).1
  rw [he.trans hValue] at hg ⊢
  exact hPhases (plan.phase (frame rule.head).1) _ (hf (plan.slot (frame rule.head).1))
    (frame rule.head).1 (hShapes rule hRule).1.1 rfl fields hf rfl hg

theorem horn_valid_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (plan : Plan) (hValid : Valid plan rules)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩)) (hg : Witness (ObjectHorn.step rules) root) : HornProv 𝒩 rules root :=
  horn_ranked_positive h𝒩 rules plan
    (fun rule hr => ⟨(hValid rule hr).1, fun p hp => ((hValid rule hr).2 p hp).1⟩)
    (ranked_decrease h𝒩 rules plan hValid) hr hg

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
