import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceProjection

/-! # 内部项码的参数列与函数应用证书

函数元数是固定的外部语法参数；项码、上下文长度和前提轨迹保留为内部对象。
规则表显式包含项与参数列规则，因而同一构造可供项检查和公式检查复用。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceTermConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceHornConstruction PureSourceTraceComposition PureSourceProjection
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def Supports (rules : List ObjectHorn.Rule) : Prop :=
  ∀ rule ∈ ObjectTermSyntax.termRules ++ ObjectTermSyntax.argumentRules, rule ∈ rules

def TermGraph (rules : List ObjectHorn.Rule) (bound free input : 𝒩.Carrier .set) : Prop :=
  Witness (ObjectHorn.step rules) (node 𝒩 0 [bound, free, input])

def ArgumentsGraph (rules : List ObjectHorn.Rule) (bound free count input : 𝒩.Carrier .set) : Prop :=
  Witness (ObjectHorn.step rules) (node 𝒩 1 [bound, free, count, input])

theorem term_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (rules : List ObjectHorn.Rule) (b f input : SetTerm bound free) :
    (ObjectHorn.condition rules (IntrinsicQuotation.node 0 [b, f, input])).satisfies env ↔
      TermGraph rules (b.eval env) (f.eval env) (input.eval env) := by
  simp only [ObjectHorn.condition, ObjectTrace.condition_satisfies, node_eval, List.map_cons, List.map_nil]
  rfl

theorem term_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) {bound free input : 𝒩.Carrier .set}
    (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩)) (hInput : mem 𝒩 input (w 𝒩)) :
    TermGraph rules bound free input ↔ @TermGraph (PureSourceNumerals.canonical h𝒩) rules bound free input := by
  let env : Env 𝒩 [] [.set,.set,.set] := templateEnv (.cons bound (.cons free (.cons input .nil)))
  let other : Env (PureSourceNumerals.canonical h𝒩) [] [.set,.set,.set] :=
    templateEnv (.cons bound (.cons free (.cons input .nil)))
  have h := PureSourceHorn.condition_agrees h𝒩 rules env other
    (IntrinsicQuotation.node 0 [.fvar .here, .fvar (.there .here), .fvar (.there (.there .here))]) (by
      simp only [node_eval, List.map_cons, List.map_nil, Term.eval]
      change node 𝒩 0 [bound, free, input] = node (PureSourceNumerals.canonical h𝒩) 0 [bound, free, input]
      exact node_agrees h𝒩 0 (by simp [hBound, hFree, hInput]))
  exact (term_satisfies env rules _ _ _).symm.trans (h.trans (term_satisfies other rules _ _ _))

private theorem intro_rule (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {rules : List ObjectHorn.Rule} (hRules : Supports rules)
    (rule : ObjectHorn.Rule) (hRule : rule ∈ ObjectTermSyntax.termRules ++ ObjectTermSyntax.argumentRules)
    (values : Fin rule.arity → 𝒩.Carrier .set) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hGuards : ∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2))
    (hPremises : ∀ premise ∈ rule.premises, Witness (ObjectHorn.step rules) (exprValue 𝒩 values premise)) :
    Witness (ObjectHorn.step rules) (exprValue 𝒩 values rule.head) :=
  rule_intro h𝒩 rules rule (hRules rule hRule) values hValues
    (ObjectTermSyntax.head_variables rule (List.mem_append_left _ hRule)) hGuards hPremises

theorem variable_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {rules : List ObjectHorn.Rule} (hRules : Supports rules) (isFree : Bool) (index : Nat)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (hIndex : mem 𝒩 (numeral 𝒩 index) (if isFree then free else bound)) :
    TermGraph rules bound free (node 𝒩 (if isFree then 1 else 0) [node 𝒩 index []]) := by
  have h := intro_rule h𝒩 hRules (ObjectTermSyntax.variableRule isFree)
    (by cases isFree <;> simp [ObjectTermSyntax.termRules])
    (fun i : Fin 3 => [bound, free, numeral 𝒩 index][i])
    (values_natural (fields := [bound, free, numeral 𝒩 index]) (by simp [hBound, hFree, numeral_natural h𝒩]))
    (by intro guard hg; obtain rfl := List.mem_singleton.mp hg; cases isFree <;> exact hIndex)
    (by intro premise hp; cases hp)
  simpa [ObjectTermSyntax.variableRule, ObjectTermSyntax.variableRule.rawNodeVar,
    ObjectTermSyntax.node, expr_node, exprValue, TermGraph, node, fieldsCode] using! h

theorem arguments_nil (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {rules : List ObjectHorn.Rule} (hRules : Supports rules)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩)) :
    ArgumentsGraph rules bound free (z 𝒩) (fieldsCode 𝒩 []) := by
  have h := intro_rule h𝒩 hRules ObjectTermSyntax.nilRule (by simp [ObjectTermSyntax.argumentRules])
    (fun i : Fin 2 => [bound, free][i])
    (values_natural (fields := [bound, free]) (by simp [hBound, hFree]))
    (by intro guard hg; cases hg) (by intro premise hp; cases hp)
  simpa [ObjectTermSyntax.nilRule, ObjectTermSyntax.node, expr_node, expr_list, exprValue,
    ArgumentsGraph] using! h

theorem arguments_cons (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {rules : List ObjectHorn.Rule} (hRules : Supports rules)
    {bound free count head tail : 𝒩.Carrier .set}
    (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (hCount : mem 𝒩 count (w 𝒩)) (hHead : mem 𝒩 head (w 𝒩)) (hTail : mem 𝒩 tail (w 𝒩))
    (hHeadGraph : TermGraph rules bound free head) (hTailGraph : ArgumentsGraph rules bound free count tail) :
    ArgumentsGraph rules bound free (suc 𝒩 count) (suc 𝒩 (pair 𝒩 (numeral 𝒩 1) (pair 𝒩 head tail))) := by
  have h := intro_rule h𝒩 hRules ObjectTermSyntax.consRule (by simp [ObjectTermSyntax.argumentRules])
    (fun i : Fin 5 => [bound, free, count, head, tail][i])
    (values_natural (fields := [bound, free, count, head, tail]) (by simp [hBound, hFree, hCount, hHead, hTail]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa [ObjectTermSyntax.consRule, ObjectTermSyntax.node, expr_node, exprValue,
          TermGraph] using! hHeadGraph
      · obtain rfl := List.mem_singleton.mp hp
        simpa [ObjectTermSyntax.consRule, ObjectTermSyntax.node, expr_node, exprValue,
          ArgumentsGraph] using! hTailGraph)
  simpa [ObjectTermSyntax.consRule, ObjectTermSyntax.node, ObjectTermSyntax.cons, expr_node,
    exprValue, ArgumentsGraph] using! h

/-- 固定元数的项列表可合成为内部参数列证书。 -/
theorem arguments_list (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {rules : List ObjectHorn.Rule} (hRules : Supports rules)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (fields : List (𝒩.Carrier .set)) (hFields : ∀ field ∈ fields, mem 𝒩 field (w 𝒩))
    (hGraphs : ∀ field ∈ fields, TermGraph rules bound free field) :
    ArgumentsGraph rules bound free (numeral 𝒩 fields.length) (fieldsCode 𝒩 fields) := by
  induction fields with
  | nil => exact arguments_nil h𝒩 hRules hBound hFree
  | cons head tail ih =>
    exact arguments_cons h𝒩 hRules hBound hFree (numeral_natural h𝒩 tail.length)
      (hFields head List.mem_cons_self)
      (fields_natural h𝒩 (fun field hf => hFields field (List.mem_cons_of_mem head hf)))
      (hGraphs head List.mem_cons_self)
      (ih (fun field hf => hFields field (List.mem_cons_of_mem head hf))
        (fun field hf => hGraphs field (List.mem_cons_of_mem head hf)))

theorem application (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {rules : List ObjectHorn.Rule} (hRules : Supports rules)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (symbol : FunctionSymbol) (fields : List (𝒩.Carrier .set))
    (hFields : ∀ field ∈ fields, mem 𝒩 field (w 𝒩))
    (hArguments : ArgumentsGraph rules bound free (numeral 𝒩 (signature.funcDomain symbol).length) (fieldsCode 𝒩 fields)) :
    TermGraph rules bound free (node 𝒩 2 (node 𝒩 symbol.ctorIdx [] :: fields)) := by
  have hMem : ObjectTermSyntax.applicationRule symbol ∈ ObjectTermSyntax.termRules :=
    List.mem_append_right _ (List.mem_map.mpr ⟨symbol, ObjectTermSyntax.symbol_mem symbol, rfl⟩)
  have h := intro_rule h𝒩 hRules (ObjectTermSyntax.applicationRule symbol) (List.mem_append_left _ hMem)
    (fun i : Fin 3 => [bound, free, fieldsCode 𝒩 fields][i])
    (values_natural (fields := [bound, free, fieldsCode 𝒩 fields])
      (by simp [hBound, hFree, fields_natural h𝒩 hFields]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      obtain rfl := List.mem_singleton.mp hp
      simpa [ObjectTermSyntax.applicationRule, ObjectTermSyntax.node, expr_node, exprValue,
        ArgumentsGraph] using! hArguments)
  simpa [ObjectTermSyntax.applicationRule, ObjectTermSyntax.node, ObjectTermSyntax.rawNode,
    ObjectTermSyntax.cons, expr_node, exprValue, TermGraph, node, fieldsCode] using! h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceTermConstruction
