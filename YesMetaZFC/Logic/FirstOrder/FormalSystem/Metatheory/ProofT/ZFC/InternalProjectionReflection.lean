import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornReflection

/-! # 原投影检查图的内部正反射

取项图按内部索引归纳，归纳性质是实际对象公式并具有最终阶段对应。
标签和字段分支复用同一规则装配；包括非规范外壳，不预设输入来自宿主列表。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity PureSourceNumerals
open PureSourceTraceComposition PureSourceHornConstruction ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
set_option maxHeartbeats 300000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem projectionGet_satisfies {bound free : SetContext} (env : Env 𝒩 bound free) (index : SetTerm bound free) :
    (ObjectHornReflection.getAt ReducedProofPresentation.presentation.graph index).satisfies env ↔
      ∀ input, mem 𝒩 input (w 𝒩) → ∀ output, mem 𝒩 output (w 𝒩) →
        Witness (ObjectHorn.step ObjectProjection.rules) (node 𝒩 1 [input, index.eval env, output]) →
          HornProv 𝒩 ObjectProjection.rules (node 𝒩 1 [input, index.eval env, output]) := by
  simp only [ObjectHornReflection.getAt, forallNatural_satisfies, implication_satisfies,
    horn_satisfies, hornAt_satisfies, node_eval, List.map_cons, List.map_nil, Term.eval_weakenFree]
  rfl

theorem projectionGet_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {index : 𝒩.Carrier .set} (hk : mem 𝒩 index (w 𝒩)) :
    (ObjectHornReflection.getAt ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons index .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectHornReflection.getAt ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons index .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [projectionGet_satisfies, projectionGet_satisfies]
  apply forall_congr'; intro input
  change (mem 𝒩 input (w 𝒩) → _) ↔ (mem 𝒩 input (w (canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro hi
  apply forall_congr'; intro output
  apply imp_congr_right; intro ho
  have hFields : ∀ v, v ∈ [input, index, output] → mem 𝒩 v (w 𝒩) := by simp [hi, hk, ho]
  have he := node_agrees h𝒩 1 hFields
  have hTrace := witness_agrees h𝒩 (ObjectHorn.step ObjectProjection.rules) (node 𝒩 1 [input, index, output])
    (fun row hr trace => PureSourceHorn.step_agrees h𝒩 ObjectProjection.rules hr trace)
  have hProof := hornProv_agrees h𝒩 ObjectProjection.rules (node_natural h𝒩 1 hFields)
  exact imp_congr
    (hTrace.trans (iff_of_eq (congrArg (fun root => @Witness (canonical h𝒩) (ObjectHorn.step ObjectProjection.rules) root) he)))
    (hProof.trans (iff_of_eq (congrArg (HornProv (canonical h𝒩) ObjectProjection.rules) he)))

/-- 仅取尾分支需要较小索引；根行反演保留原内部轨迹。 -/
theorem projection_get_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input index output : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) (hk : mem 𝒩 index (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hLower : ∀ previous, mem 𝒩 previous (w 𝒩) → index = suc 𝒩 previous →
      ∀ tail result, mem 𝒩 tail (w 𝒩) → mem 𝒩 result (w 𝒩) →
        Witness (ObjectHorn.step ObjectProjection.rules) (node 𝒩 1 [tail, previous, result]) →
          HornProv 𝒩 ObjectProjection.rules (node 𝒩 1 [tail, previous, result]))
    (hGraph : Witness (ObjectHorn.step ObjectProjection.rules) (node 𝒩 1 [input, index, output])) :
    HornProv 𝒩 ObjectProjection.rules (node 𝒩 1 [input, index, output]) := by
  have hFields : ∀ v, v ∈ [input, index, output] → mem 𝒩 v (w 𝒩) := by simp [hi, hk, ho]
  obtain ⟨rule, hRule, values, hv, hHead, hGuards, hPremises⟩ :=
    rule_cases h𝒩 ObjectProjection.rules (node_natural h𝒩 1 hFields) hGraph
  rw [hHead]
  apply horn_rule_values h𝒩 ObjectProjection.rules rule hRule (ObjectProjection.head_variables rule hRule) values hv hGuards
  intro premise hp
  simp only [ObjectProjection.rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (List.not_mem_nil hp) | skip
  · obtain rfl := List.mem_singleton.mp hp
    have hParts := node_head_injective h𝒩 values hv hFields hHead
    have hIndex : index = suc 𝒩 (values 3) := by
      have hList := hParts.2
      simp only [List.map_cons, List.map_nil, exprValue, List.cons.injEq, and_true] at hList
      exact hList.2.1
    have hPrevious : Witness (ObjectHorn.step ObjectProjection.rules) (node 𝒩 1 [values 2, values 3, values 4]) := by
      simpa only [ObjectProjection.getTail, expr_node, List.map_cons, List.map_nil, exprValue] using!
        hPremises _ List.mem_cons_self
    simpa only [ObjectProjection.getTail, expr_node, List.map_cons, List.map_nil, exprValue] using!
      hLower (values 3) (hv 3) hIndex (values 2) (values 4) (hv 2) (hv 4) hPrevious
  · have hParts := node_head_injective h𝒩 values hv hFields hHead
    exact False.elim ((by decide : (1 : Nat) ≠ 2) hParts.1)

/-- 索引可为非标准自然数，输入无需满足树或列表规范性。 -/
theorem projection_get_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input index output : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) (hk : mem 𝒩 index (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectProjection.rules) (node 𝒩 1 [input, index, output])) :
    HornProv 𝒩 ObjectProjection.rules (node 𝒩 1 [input, index, output]) := by
  let property : SetOpenFormula [.set] := ObjectHornReflection.getAt ReducedProofPresentation.presentation.graph (.fvar .here)
  have hAll : ∀ index, mem 𝒩 index (w 𝒩) → property.satisfies (templateEnv (.cons index .nil) : Env 𝒩 [] [.set]) := by
    apply PureSourceInduction.induction h𝒩 property .nil
    · exact fun _ hk => projectionGet_agrees h𝒩 hk
    · apply (projectionGet_satisfies _ _).mpr
      intro input hi output ho hg
      exact projection_get_step h𝒩 hi (omega_closed h𝒩).1 ho (fun previous _ he =>
        False.elim (PureSourceNumeralSyntax.successor_ne_zero h𝒩 previous he.symm)) hg
    · intro index hk hProperty
      apply (projectionGet_satisfies _ _).mpr
      intro input hi output ho hg
      apply projection_get_step h𝒩 hi ((omega_closed h𝒩).2 index hk) ho ?_ hg
      intro previous hp he tail result ht hr hPrevious
      have he := PureSourceCodingInversion.successor_injective h𝒩 hk he
      subst previous
      exact (projectionGet_satisfies _ _).mp hProperty tail ht result hr hPrevious
  exact (projectionGet_satisfies _ _).mp (hAll index hk) input hi output ho hg

/-- 原投影局部测试的全部七条规则都具有内部正反射。 -/
theorem projection_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectProjection.rules) root) : HornProv 𝒩 ObjectProjection.rules root := by
  obtain ⟨rule, hRule, values, hv, hHead, hGuards, hPremises⟩ := rule_cases h𝒩 ObjectProjection.rules hr hg
  rw [hHead]
  apply horn_rule_values h𝒩 ObjectProjection.rules rule hRule (ObjectProjection.head_variables rule hRule) values hv hGuards
  intro premise hp
  simp only [ObjectProjection.rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (List.not_mem_nil hp) | skip
  all_goals obtain rfl := List.mem_singleton.mp hp
  · apply projection_get_positive h𝒩 (hv 2) (hv 3) (hv 4)
    simpa only [ObjectProjection.getTail, expr_node, List.map_cons, List.map_nil, exprValue] using! hPremises _ List.mem_cons_self
  · apply projection_get_positive h𝒩 (hv 1) (hv 2) (hv 3)
    simpa only [ObjectProjection.fieldPositive, expr_node, List.map_cons, List.map_nil, exprValue] using! hPremises _ List.mem_cons_self

theorem projection_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (root : SetOpenTerm free) (hr : TermEvaluates env values root)
    (hg : (ObjectHorn.condition ObjectProjection.rules root).satisfies env) :
    ProvableCode 𝒩 (formula 𝒩 values (ObjectHorn.condition ObjectProjection.rules root)) :=
  (horn_term_transfer h𝒩 env values hv ObjectProjection.rules root hr).mpr
    (projection_positive h𝒩 hr.1 ((horn_satisfies env ObjectProjection.rules root).mp hg))

theorem projection_positive_derives : Derives intrinsic_zfc_theory []
    (ObjectHornReflection.onNaturals ReducedProofPresentation.presentation.graph ObjectProjection.rules) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  change (ObjectHornReflection.onNaturals ReducedProofPresentation.presentation.graph ObjectProjection.rules).satisfies (Env.empty : Env 𝒩 [] [])
  unfold ObjectHornReflection.onNaturals
  rw [forallNatural_satisfies]
  intro root hr
  rw [implication_satisfies, horn_satisfies, hornAt_satisfies]
  exact projection_positive h𝒩 hr

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
