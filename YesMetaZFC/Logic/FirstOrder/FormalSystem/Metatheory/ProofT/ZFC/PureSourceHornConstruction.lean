import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceHorn
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceTraceComposition

/-! # 内部自然数参数上的 Horn 轨迹构造

自动从头表达式的变量出现证明参数界，再合并前提轨迹并插入结论。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceHornConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open PureSourceHorn PureSourceTraceComposition
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics ObjectTrace
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem bound_trans (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {a b c : 𝒩.Carrier .set} (hc : mem 𝒩 c (w 𝒩))
    (hAB : mem 𝒩 a (suc 𝒩 b)) (hBC : mem 𝒩 b (suc 𝒩 c)) : mem 𝒩 a (suc 𝒩 c) := by
  rcases (successor_spec h𝒩 b a).mp hAB with hAB | rfl
  · rcases (successor_spec h𝒩 c b).mp hBC with hBC | rfl
    · exact (successor_spec h𝒩 c a).mpr (Or.inl
        (((omega_project h𝒩).members_areOrdinals (PureModel.project_modelsZF (PureZFCModels.reduct_models h𝒩)) c hc).transitive b hBC a hAB))
    · exact (successor_spec h𝒩 b a).mpr (Or.inl hAB)
  · exact hBC

theorem pair_bounds (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {a b : 𝒩.Carrier .set} (ha : mem 𝒩 a (w 𝒩)) (hb : mem 𝒩 b (w 𝒩)) :
    mem 𝒩 a (suc 𝒩 (pair 𝒩 a b)) ∧ mem 𝒩 b (suc 𝒩 (pair 𝒩 a b)) := by
  have hProof := Derives.theory_weaken intrinsic_zfc_structural_sequence_support.contains_natural_addition_bound
    (natural_godel_pairing_coordinate_bound_instance_derives
      (.fvar (.there .here) : SetOpenTerm [.set,.set]) (.fvar .here) (Γ := []))
  exact (hProof.sound h𝒩 (templateEnv (.cons b (.cons a .nil)))
    (by intro formula h; cases h)) ⟨ha,hb⟩

theorem expr_bound (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {n : Nat}
    {values : Fin n → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (expr : ObjectHorn.Expr n) {index : Fin n} (hIndex : index ∈ expr.variables) :
    mem 𝒩 (values index) (suc 𝒩 (exprValue 𝒩 values expr)) := by
  induction expr with
  | literal number => cases hIndex
  | var i =>
    have h := List.mem_singleton.mp hIndex
    subst index
    exact (successor_spec h𝒩 _ _).mpr (Or.inr rfl)
  | succ body ih =>
    apply bound_trans h𝒩 (expr_natural h𝒩 hValues (.succ body)) (ih hIndex)
    exact (successor_spec h𝒩 _ _).mpr (Or.inl ((successor_spec h𝒩 _ _).mpr (Or.inr rfl)))
  | pair left right ihLeft ihRight =>
    have hPair := pair_bounds h𝒩 (expr_natural h𝒩 hValues left) (expr_natural h𝒩 hValues right)
    rcases List.mem_append.mp hIndex with h | h
    · exact bound_trans h𝒩 (expr_natural h𝒩 hValues (.pair left right)) (ihLeft h) hPair.1
    · exact bound_trans h𝒩 (expr_natural h𝒩 hValues (.pair left right)) (ihRight h) hPair.2

theorem expr_list {n : Nat} (values : Fin n → 𝒩.Carrier .set) (fields : List (ObjectHorn.Expr n)) :
    exprValue 𝒩 values (.list fields) = fieldsCode 𝒩 (fields.map (exprValue 𝒩 values)) := by
  induction fields with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun rest => suc 𝒩 (pair 𝒩 (numeral 𝒩 1) (pair 𝒩 (exprValue 𝒩 values head) rest))) ih

theorem expr_node {n : Nat} (values : Fin n → 𝒩.Carrier .set) (tag : Nat) (fields : List (ObjectHorn.Expr n)) :
    exprValue 𝒩 values (.node (.literal tag) fields) = node 𝒩 tag (fields.map (exprValue 𝒩 values)) := by
  exact congrArg (fun rest => suc 𝒩 (pair 𝒩 (numeral 𝒩 tag) rest)) (expr_list values fields)

/-- 固定标准字段的节点连接既有数码求值，不展开巨大编码。 -/
theorem node_numerals (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (tag : Nat) (fields : List Nat) :
    node 𝒩 tag (fields.map (numeral 𝒩)) = numeral 𝒩 (ObjectHorn.nodeValue tag fields) := by
  let expression : ObjectHorn.Expr 0 := .node (.literal tag) (fields.map .literal)
  have h := (expression.evaluate intrinsic_zfc_certificate_core Fin.elim0).semantically_entails 𝒩 h𝒩
  change ((expression.term (fun i => numₘ(Fin.elim0 i))).eval (Env.empty : Env 𝒩 [] [])) = _ at h
  rw [expr_eval] at h
  simpa [expression, expr_node, List.map_map, Function.comp_def, exprValue, ObjectHorn.Expr.node_eval,
    ObjectHorn.Expr.eval, numeral] using! h

/-- 每个规则的实例可接到已有的内部前提轨迹。 -/
theorem rule_intro_bounds (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (rule : ObjectHorn.Rule) (hRule : rule ∈ rules)
    (values : Fin rule.arity → 𝒩.Carrier .set)
    (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hBounds : ∀ i, mem 𝒩 (values i) (suc 𝒩 (exprValue 𝒩 values rule.head)))
    (hGuards : ∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2))
    (hPremises : ∀ premise ∈ rule.premises, Witness (ObjectHorn.step rules) (exprValue 𝒩 values premise)) :
    Witness (ObjectHorn.step rules) (exprValue 𝒩 values rule.head) := by
  obtain ⟨trace, hTrace, hMembers, hClosed⟩ := collect h𝒩 _ (horn_monotone rules)
    (rule.premises.map (exprValue 𝒩 values)) (by
      intro root hRoot
      obtain ⟨premise, hp, rfl⟩ := List.mem_map.mp hRoot
      exact hPremises premise hp)
  have hRow := (step_satisfies rules (exprValue 𝒩 values rule.head) trace).mpr
    ⟨rule, hRule, (rule_satisfies rule _ trace).mpr ⟨values,
      hBounds, rfl, hGuards,
      (fun premise hp => hMembers _ (List.mem_map.mpr ⟨premise, hp, rfl⟩))⟩⟩
  obtain ⟨extended, hBound, _, hRoot, hExtended⟩ := insert h𝒩 _ (horn_monotone rules)
    hTrace (expr_natural h𝒩 hValues rule.head) hClosed hRow
  exact ⟨extended, hBound, hRoot, hExtended⟩

/-- 每个规则的实例可接到已有的内部前提轨迹。 -/
theorem rule_intro (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (rule : ObjectHorn.Rule) (hRule : rule ∈ rules)
    (values : Fin rule.arity → 𝒩.Carrier .set)
    (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hVariables : ∀ i, i ∈ rule.head.variables)
    (hGuards : ∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2))
    (hPremises : ∀ premise ∈ rule.premises, Witness (ObjectHorn.step rules) (exprValue 𝒩 values premise)) :
    Witness (ObjectHorn.step rules) (exprValue 𝒩 values rule.head) :=
  rule_intro_bounds h𝒩 rules rule hRule values hValues
    (fun i => expr_bound h𝒩 hValues rule.head (hVariables i)) hGuards hPremises

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceHornConstruction
