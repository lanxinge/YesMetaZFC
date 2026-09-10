import YesMetaZFC.Automation.ObjectPacketRanking
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornRanking

/-! # 原传输包仿射图的内部增长界

按实际尾参数公式归纳，证明 radix 128 的正尾严格小于结果。
此不变量供 token 的递归下降使用，覆盖非标准参数与集合轨迹。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourcePacketBounds
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open PureSourceTraceComposition PureSourceHornConstruction InternalNumeralReflection
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem natural_irrefl (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {input : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) : ¬ mem 𝒩 input input :=
  PureArithmeticOrder.lt_irrefl (PureZFCModels.reduct_models h𝒩) (PureSourceCodingInversion.natural_pure h𝒩 hi)

theorem zero_bound (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {input : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) : mem 𝒩 (z 𝒩) (suc 𝒩 input) := by
  rcases natural_compare h𝒩 (omega_closed h𝒩).1 hi with he | hl | hg
  · exact (successor_spec h𝒩 _ _).mpr (Or.inr he)
  · exact (successor_spec h𝒩 _ _).mpr (Or.inl hl)
  · exact False.elim (empty_spec h𝒩 _ hg)

theorem successor_bound (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {a b : 𝒩.Carrier .set} (ha : mem 𝒩 a (w 𝒩)) (hb : mem 𝒩 b (w 𝒩))
    (h : mem 𝒩 a (suc 𝒩 b)) : mem 𝒩 (suc 𝒩 a) (suc 𝒩 (suc 𝒩 b)) := by
  rcases natural_compare h𝒩 ((omega_closed h𝒩).2 a ha) hb with he | hl | hg
  · rw [he]; exact (successor_spec h𝒩 _ _).mpr (Or.inl ((successor_spec h𝒩 _ _).mpr (Or.inr rfl)))
  · exact (successor_spec h𝒩 _ _).mpr (Or.inl ((successor_spec h𝒩 _ _).mpr (Or.inl hl)))
  · rcases (successor_spec h𝒩 a b).mp hg with hg | he
    · rcases (successor_spec h𝒩 b a).mp h with hl | he
      · have ht := ((omega_project h𝒩).members_areOrdinals
          (PureModel.project_modelsZF (PureZFCModels.reduct_models h𝒩)) a ha).transitive b hg a hl
        exact False.elim (natural_irrefl h𝒩 ha ht)
      · exact False.elim (natural_irrefl h𝒩 ha (he ▸ hg))
    · rw [he]; exact (successor_spec h𝒩 _ _).mpr (Or.inr rfl)

theorem addConst_bound (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {n : Nat}
    (values : Fin n → 𝒩.Carrier .set) (body : ObjectHorn.Expr n)
    {input : 𝒩.Carrier .set} (lower upper : Nat) (hle : lower ≤ upper)
    (h : mem 𝒩 input (exprValue 𝒩 values (ObjectPacket.Expr.addConst lower body))) :
    mem 𝒩 input (exprValue 𝒩 values (ObjectPacket.Expr.addConst upper body)) := by
  induction upper with
  | zero =>
    have he : lower = 0 := by omega
    subst lower
    exact h
  | succ upper ih =>
    by_cases he : lower = upper + 1
    · exact he ▸ h
    · exact (successor_spec h𝒩 _ _).mpr (Or.inl (ih (by omega)))

theorem affineBounds_satisfies {bound free : SetContext} (env : Env 𝒩 bound free) (tail : SetTerm bound free) :
    (ObjectPacketRanking.affineBounds tail).satisfies env ↔
      ∀ digit, mem 𝒩 digit (w 𝒩) → ∀ output, mem 𝒩 output (w 𝒩) →
        Witness (ObjectHorn.step ObjectPacket.rules) (node 𝒩 0 [digit, tail.eval env, output]) →
          mem 𝒩 (tail.eval env) (suc 𝒩 output) ∧ (tail.eval env ≠ z 𝒩 → mem 𝒩 (tail.eval env) output) := by
  simp only [ObjectPacketRanking.affineBounds, forallNatural_satisfies, implication_satisfies,
    horn_satisfies, node_eval, List.map_cons, List.map_nil, Term.eval_weakenFree]
  simp only [Formula.satisfies, Arguments.eval, Term.eval_weakenFree, Term.eval]
  rfl

theorem affineBounds_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {tail : 𝒩.Carrier .set} (ht : mem 𝒩 tail (w 𝒩)) :
    (ObjectPacketRanking.affineBounds (.fvar .here)).satisfies
      (templateEnv (.cons tail .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectPacketRanking.affineBounds (.fvar .here)).satisfies
      (templateEnv (.cons tail .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [affineBounds_satisfies, affineBounds_satisfies]
  apply forall_congr'; intro digit
  change (mem 𝒩 digit (w 𝒩) → _) ↔ (mem 𝒩 digit (w (canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro hd
  apply forall_congr'; intro output
  apply imp_congr_right; intro ho
  have hFields : ∀ v, v ∈ [digit, tail, output] → mem 𝒩 v (w 𝒩) := by simp [hd, ht, ho]
  have he := node_agrees h𝒩 0 hFields
  have hg := witness_agrees h𝒩 (ObjectHorn.step ObjectPacket.rules) (node 𝒩 0 [digit, tail, output])
    (fun row hr trace => PureSourceHorn.step_agrees h𝒩 ObjectPacket.rules hr trace)
  apply imp_congr (hg.trans (iff_of_eq (congrArg (fun root => @Witness (canonical h𝒩) (ObjectHorn.step ObjectPacket.rules) root) he)))
  change (mem 𝒩 tail (suc 𝒩 output) ∧ (tail ≠ z 𝒩 → mem 𝒩 tail output)) ↔
    (mem 𝒩 tail (suc (canonical h𝒩) output) ∧ (tail ≠ z (canonical h𝒩) → mem 𝒩 tail output))
  rw [successor_agrees h𝒩, empty_agrees h𝒩]

theorem affine_bounds (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {digit tail output : 𝒩.Carrier .set} (hd : mem 𝒩 digit (w 𝒩))
    (ht : mem 𝒩 tail (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectPacket.rules) (node 𝒩 0 [digit, tail, output])) :
    mem 𝒩 tail (suc 𝒩 output) ∧ (tail ≠ z 𝒩 → mem 𝒩 tail output) := by
  let property : SetOpenFormula [.set] := ObjectPacketRanking.affineBounds (.fvar .here)
  have hAll : ∀ tail, mem 𝒩 tail (w 𝒩) → property.satisfies (templateEnv (.cons tail .nil) : Env 𝒩 [] [.set]) := by
    apply PureSourceInduction.strong_induction h𝒩 property .nil
    · exact fun _ ht => affineBounds_agrees h𝒩 ht
    · intro tail ht hLower
      apply (affineBounds_satisfies _ _).mpr
      intro digit hd output ho hg
      have hFields : ∀ v, v ∈ [digit, tail, output] → mem 𝒩 v (w 𝒩) := by simp [hd, ht, ho]
      obtain ⟨rule, hRule, values, hv, hHead, _, hPremises⟩ :=
        rule_cases h𝒩 ObjectPacket.rules (node_natural h𝒩 0 hFields) hg
      simp only [ObjectPacket.rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
      rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals have hParts := node_head_injective h𝒩 values hv hFields hHead
      all_goals try exact False.elim ((by decide : (0 : Nat) ≠ 1) hParts.1)
      all_goals try exact False.elim ((by decide : (0 : Nat) ≠ 2) hParts.1)
      all_goals try exact False.elim ((by decide : (0 : Nat) ≠ 3) hParts.1)
      all_goals try exact False.elim ((by decide : (0 : Nat) ≠ 4) hParts.1)
      all_goals try exact False.elim ((by decide : (0 : Nat) ≠ 5) hParts.1)
      · change Fin 1 → 𝒩.Carrier .set at values
        have hz : tail = z 𝒩 := by
          have h := hParts.2
          simp only [ObjectPacket.affineBase, ObjectPacket.node, List.map_cons, List.map_nil, exprValue, List.cons.injEq, and_true] at h
          exact h.2.1
        rw [hz]
        exact ⟨zero_bound h𝒩 ho, fun hn => False.elim (hn rfl)⟩
      · change Fin 3 → 𝒩.Carrier .set at values
        change ∀ i : Fin 3, mem 𝒩 (values i) (w 𝒩) at hv
        have hTail : tail = suc 𝒩 (values 1) := by
          have h := hParts.2
          simp only [ObjectPacket.affineStep, ObjectPacket.node, List.map_cons, List.map_nil, exprValue, List.cons.injEq, and_true] at h
          exact h.2.1
        have hOutput : output = exprValue 𝒩 values (ObjectPacket.Expr.addConst 128 (.var 2)) := by
          have h := hParts.2
          simp only [ObjectPacket.affineStep, ObjectPacket.node, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
          exact h.2.2
        have hl : mem 𝒩 (values 1) tail := hTail.symm ▸ (successor_spec h𝒩 _ _).mpr (Or.inr rfl)
        have hp := (affineBounds_satisfies _ _).mp (hLower (values 1) hl) (values 0) (hv 0) (values 2) (hv 2)
          (by simpa only [ObjectPacket.affineStep, ObjectPacket.node, expr_node, List.map_cons, List.map_nil, exprValue] using! hPremises _ List.mem_cons_self)
        have hStrict : mem 𝒩 tail output := by
          rw [hTail, hOutput]
          exact addConst_bound h𝒩 values (.var 2) 2 128 (by decide) (successor_bound h𝒩 (hv 1) (hv 2) hp.1)
        exact ⟨(successor_spec h𝒩 _ _).mpr (Or.inl hStrict), fun _ => hStrict⟩
  exact (affineBounds_satisfies _ _).mp (hAll tail ht) digit hd output ho hg

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourcePacketBounds
