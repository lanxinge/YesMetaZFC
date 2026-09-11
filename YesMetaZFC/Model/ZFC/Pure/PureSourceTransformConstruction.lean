import YesMetaZFC.Model.ZFC.Pure.PureSourceProjection
import YesMetaZFC.Automation.ObjectSyntaxTransformAccept

/-! # 当前语法变换图的内部规则构造

参数、输入和输出都可以是非标准自然数。只对固定字段表作宿主递归，
每个实际规则实例仍由内部集合轨迹的合并与插入实现。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceTransformConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceHornConstruction PureSourceTraceComposition PureSourceProjection
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def Graph (kind : Nat) (mode depth parameter input output : 𝒩.Carrier .set) : Prop :=
  Witness (ObjectHorn.step ObjectSyntaxTransform.rules) (node 𝒩 kind [mode, depth, parameter, input, output])

def Lookup (table index output : 𝒩.Carrier .set) : Prop :=
  Witness (ObjectHorn.step ObjectSyntaxTransform.rules) (node 𝒩 0 [table, index, output])

theorem graph_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (kind : Nat)
    {mode depth parameter input output : 𝒩.Carrier .set}
    (hm : mem 𝒩 mode (w 𝒩)) (hd : mem 𝒩 depth (w 𝒩)) (hp : mem 𝒩 parameter (w 𝒩))
    (hi : mem 𝒩 input (w 𝒩)) (ho : mem 𝒩 output (w 𝒩)) :
    Graph kind mode depth parameter input output ↔
      @Graph (PureSourceNumerals.canonical h𝒩) kind mode depth parameter input output := by
  unfold Graph
  rw [node_agrees h𝒩 kind (fields := [mode, depth, parameter, input, output]) (by simp [hm, hd, hp, hi, ho])]
  exact witness_agrees h𝒩 _ _ (fun row hRow trace => PureSourceHorn.step_agrees h𝒩 _ hRow trace)

theorem satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (mode depth parameter input output : SetTerm bound free) :
    (ObjectSyntaxTransform.condition mode depth parameter input output).satisfies env ↔
      Graph 3 (mode.eval env) (depth.eval env) (parameter.eval env) (input.eval env) (output.eval env) := by
  simp only [ObjectSyntaxTransform.condition, ObjectHorn.condition, ObjectTrace.condition_satisfies,
    node_eval, List.map_cons, List.map_nil]
  rfl

def variableCode (𝒩 : Structure.{0,0,0,x} signature) (free : Bool) (index : 𝒩.Carrier .set) : 𝒩.Carrier .set :=
  node 𝒩 (if free then 1 else 0) [suc 𝒩 (pair 𝒩 index (fieldsCode 𝒩 []))]

private theorem intro_rule (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rule : ObjectHorn.Rule) (hRule : rule ∈ ObjectSyntaxTransform.rules)
    (values : Fin rule.arity → 𝒩.Carrier .set) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hGuards : ∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2))
    (hPremises : ∀ premise ∈ rule.premises,
      Witness (ObjectHorn.step ObjectSyntaxTransform.rules) (exprValue 𝒩 values premise)) :
    Witness (ObjectHorn.step ObjectSyntaxTransform.rules) (exprValue 𝒩 values rule.head) :=
  rule_intro h𝒩 _ rule hRule values hValues (ObjectSyntaxTransform.head_variables rule hRule) hGuards hPremises

theorem lookup_list (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (fields : List (𝒩.Carrier .set)) (hFields : ∀ value ∈ fields, mem 𝒩 value (w 𝒩))
    (index : Nat) (hIndex : index < fields.length) :
    Lookup (fieldsCode 𝒩 fields) (numeral 𝒩 index) fields[index] := by
  induction fields generalizing index with
  | nil => cases hIndex
  | cons head tail ih =>
    have hHead := hFields head List.mem_cons_self
    have hTail := fun value hv => hFields value (List.mem_cons_of_mem head hv)
    have hTailCode := fields_natural h𝒩 hTail
    cases index with
    | zero =>
      have h := intro_rule h𝒩 ObjectSyntaxTransform.lookupHead (by simp [ObjectSyntaxTransform.rules])
        (fun i : Fin 2 => [head, fieldsCode 𝒩 tail][i])
        (values_natural (fields := [head, fieldsCode 𝒩 tail]) (by simp [hHead, hTailCode]))
        (by intro guard hg; cases hg) (by intro premise hp; cases hp)
      simpa [ObjectSyntaxTransform.lookupHead, expr_node, exprValue, Lookup, fieldsCode] using! h
    | succ index =>
      have hIndexTail := Nat.lt_of_succ_lt_succ hIndex
      have hOutput := hTail tail[index] (List.getElem_mem hIndexTail)
      have h := intro_rule h𝒩 ObjectSyntaxTransform.lookupTail (by simp [ObjectSyntaxTransform.rules])
        (fun i : Fin 4 => [head, fieldsCode 𝒩 tail, numeral 𝒩 index, tail[index]][i])
        (values_natural (fields := [head, fieldsCode 𝒩 tail, numeral 𝒩 index, tail[index]])
          (by simp [hHead, hTailCode, numeral_natural h𝒩, hOutput]))
        (by intro guard hg; cases hg) (by
          intro premise hp
          obtain rfl := List.mem_singleton.mp hp
          simpa [ObjectSyntaxTransform.lookupTail, expr_node, exprValue, Lookup] using! ih hTail index hIndexTail)
      simpa [ObjectSyntaxTransform.lookupTail, expr_node, exprValue, Lookup, fieldsCode] using! h

theorem bound_identity (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (mode : Nat) (below : Bool) (hRule : ObjectSyntaxTransform.boundIdentity mode below ∈ ObjectSyntaxTransform.rules)
    {depth parameter index : 𝒩.Carrier .set}
    (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩)) (hIndex : mem 𝒩 index (w 𝒩))
    (hBelow : below = true → mem 𝒩 index depth) :
    Graph 1 (numeral 𝒩 mode) depth parameter (variableCode 𝒩 false index) (variableCode 𝒩 false index) := by
  have h := intro_rule h𝒩 (ObjectSyntaxTransform.boundIdentity mode below) hRule
    (fun i : Fin 3 => [depth, parameter, index][i])
    (values_natural (fields := [depth, parameter, index]) (by simp [hDepth, hParameter, hIndex])) (by
      intro guard hg
      cases below with
      | false => cases hg
      | true => obtain rfl := List.mem_singleton.mp hg; exact hBelow rfl)
    (by intro premise hp; cases hp)
  simpa [ObjectSyntaxTransform.boundIdentity, expr_node, exprValue, Graph, variableCode] using! h

theorem bound_point (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {depth parameter : 𝒩.Carrier .set} (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩)) :
    Graph 1 (numeral 𝒩 2) depth parameter (variableCode 𝒩 false depth) parameter := by
  have h := intro_rule h𝒩 ObjectSyntaxTransform.boundPoint (by simp [ObjectSyntaxTransform.rules])
    (fun i : Fin 2 => [depth, parameter][i])
    (values_natural (fields := [depth, parameter]) (by simp [hDepth, hParameter]))
    (by intro guard hg; cases hg) (by intro premise hp; cases hp)
  simpa [ObjectSyntaxTransform.boundPoint, expr_node, exprValue, Graph, variableCode] using! h

theorem free_replace (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {depth parameter index output : 𝒩.Carrier .set}
    (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩))
    (hIndex : mem 𝒩 index (w 𝒩)) (hOutput : mem 𝒩 output (w 𝒩)) (hLookup : Lookup parameter index output) :
    Graph 1 (numeral 𝒩 3) depth parameter (variableCode 𝒩 true index) output := by
  have h := intro_rule h𝒩 ObjectSyntaxTransform.freeReplace (by simp [ObjectSyntaxTransform.rules])
    (fun i : Fin 4 => [depth, parameter, index, output][i])
    (values_natural (fields := [depth, parameter, index, output]) (by simp [hDepth, hParameter, hIndex, hOutput]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      obtain rfl := List.mem_singleton.mp hp
      simpa [ObjectSyntaxTransform.freeReplace, expr_node, exprValue, Lookup] using! hLookup)
  simpa [ObjectSyntaxTransform.freeReplace, expr_node, exprValue, Graph, variableCode] using! h

theorem nil_arguments (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {mode depth parameter : 𝒩.Carrier .set}
    (hMode : mem 𝒩 mode (w 𝒩)) (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩))
    (hSmall : mem 𝒩 mode (numeral 𝒩 4)) :
    Graph 2 mode depth parameter (fieldsCode 𝒩 []) (fieldsCode 𝒩 []) := by
  have h := intro_rule h𝒩 ObjectSyntaxTransform.nilArguments (by simp [ObjectSyntaxTransform.rules])
    (fun i : Fin 3 => [mode, depth, parameter][i])
    (values_natural (fields := [mode, depth, parameter]) (by simp [hMode, hDepth, hParameter]))
    (by intro guard hg; obtain rfl := List.mem_singleton.mp hg; exact hSmall)
    (by intro premise hp; cases hp)
  simpa [ObjectSyntaxTransform.nilArguments, expr_node, expr_list, exprValue, Graph] using! h

theorem cons_arguments (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {mode depth parameter first rest firstOut restOut : 𝒩.Carrier .set}
    (hMode : mem 𝒩 mode (w 𝒩)) (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩))
    (hFirst : mem 𝒩 first (w 𝒩)) (hRest : mem 𝒩 rest (w 𝒩))
    (hFirstOut : mem 𝒩 firstOut (w 𝒩)) (hRestOut : mem 𝒩 restOut (w 𝒩))
    (hHead : Graph 1 mode depth parameter first firstOut) (hTail : Graph 2 mode depth parameter rest restOut) :
    Graph 2 mode depth parameter
      (suc 𝒩 (pair 𝒩 (numeral 𝒩 1) (pair 𝒩 first rest)))
      (suc 𝒩 (pair 𝒩 (numeral 𝒩 1) (pair 𝒩 firstOut restOut))) := by
  have h := intro_rule h𝒩 ObjectSyntaxTransform.consArguments (by simp [ObjectSyntaxTransform.rules])
    (fun i : Fin 7 => [mode, depth, parameter, first, rest, firstOut, restOut][i])
    (values_natural (fields := [mode, depth, parameter, first, rest, firstOut, restOut])
      (by simp [hMode, hDepth, hParameter, hFirst, hRest, hFirstOut, hRestOut]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa [ObjectSyntaxTransform.consArguments, expr_node, exprValue, Graph] using! hHead
      · obtain rfl := List.mem_singleton.mp hp
        simpa [ObjectSyntaxTransform.consArguments, expr_node, exprValue, Graph] using! hTail)
  simpa [ObjectSyntaxTransform.consArguments, expr_node, exprValue, Graph] using! h

theorem application (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (kind symbol : Nat) (hKind : kind = 1 ∨ kind = 3)
    {mode depth parameter : 𝒩.Carrier .set}
    (hMode : mem 𝒩 mode (w 𝒩)) (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩))
    (input output : List (𝒩.Carrier .set))
    (hInput : ∀ value ∈ input, mem 𝒩 value (w 𝒩)) (hOutput : ∀ value ∈ output, mem 𝒩 value (w 𝒩))
    (hArgs : Graph 2 mode depth parameter (fieldsCode 𝒩 input) (fieldsCode 𝒩 output)) :
    Graph kind mode depth parameter (node 𝒩 2 (node 𝒩 symbol [] :: input)) (node 𝒩 2 (node 𝒩 symbol [] :: output)) := by
  have h := intro_rule h𝒩 (ObjectSyntaxTransform.application kind)
    (by rcases hKind with rfl | rfl <;> simp [ObjectSyntaxTransform.rules])
    (fun i : Fin 6 => [mode, depth, parameter, numeral 𝒩 symbol, fieldsCode 𝒩 input, fieldsCode 𝒩 output][i])
    (values_natural (fields := [mode, depth, parameter, numeral 𝒩 symbol, fieldsCode 𝒩 input, fieldsCode 𝒩 output])
      (by simp [hMode, hDepth, hParameter, numeral_natural h𝒩, fields_natural h𝒩 hInput, fields_natural h𝒩 hOutput]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      obtain rfl := List.mem_singleton.mp hp
      simpa [ObjectSyntaxTransform.application, expr_node, exprValue, Graph] using! hArgs)
  simpa [ObjectSyntaxTransform.application, expr_node, exprValue, Graph, node, fieldsCode] using! h

theorem constant (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (tag : Nat) (hTag : tag = 0 ∨ tag = 1)
    {mode depth parameter : 𝒩.Carrier .set}
    (hMode : mem 𝒩 mode (w 𝒩)) (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩))
    (hSmall : mem 𝒩 mode (numeral 𝒩 4)) : Graph 3 mode depth parameter (node 𝒩 tag []) (node 𝒩 tag []) := by
  have h := intro_rule h𝒩 (ObjectSyntaxTransform.constant tag)
    (by rcases hTag with rfl | rfl <;> simp [ObjectSyntaxTransform.rules])
    (fun i : Fin 3 => [mode, depth, parameter][i])
    (values_natural (fields := [mode, depth, parameter]) (by simp [hMode, hDepth, hParameter]))
    (by intro guard hg; obtain rfl := List.mem_singleton.mp hg; exact hSmall)
    (by intro premise hp; cases hp)
  simpa [ObjectSyntaxTransform.constant, expr_node, exprValue, Graph] using! h

theorem binary (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (tag childKind : Nat) (hRule : ObjectSyntaxTransform.binary tag childKind ∈ ObjectSyntaxTransform.rules)
    {mode depth parameter left right leftOut rightOut : 𝒩.Carrier .set}
    (hMode : mem 𝒩 mode (w 𝒩)) (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩))
    (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩))
    (hLeftOut : mem 𝒩 leftOut (w 𝒩)) (hRightOut : mem 𝒩 rightOut (w 𝒩))
    (hFirst : Graph childKind mode depth parameter left leftOut) (hSecond : Graph childKind mode depth parameter right rightOut) :
    Graph 3 mode depth parameter (node 𝒩 tag [left, right]) (node 𝒩 tag [leftOut, rightOut]) := by
  have h := intro_rule h𝒩 (ObjectSyntaxTransform.binary tag childKind) hRule
    (fun i : Fin 7 => [mode, depth, parameter, left, right, leftOut, rightOut][i])
    (values_natural (fields := [mode, depth, parameter, left, right, leftOut, rightOut])
      (by simp [hMode, hDepth, hParameter, hLeft, hRight, hLeftOut, hRightOut]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa [ObjectSyntaxTransform.binary, expr_node, exprValue, Graph] using! hFirst
      · obtain rfl := List.mem_singleton.mp hp
        simpa [ObjectSyntaxTransform.binary, expr_node, exprValue, Graph] using! hSecond)
  simpa [ObjectSyntaxTransform.binary, expr_node, exprValue, Graph] using! h

theorem unary (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (tag : Nat) (binder : Bool) (hRule : ObjectSyntaxTransform.unary tag binder ∈ ObjectSyntaxTransform.rules)
    {mode depth parameter input output : 𝒩.Carrier .set}
    (hMode : mem 𝒩 mode (w 𝒩)) (hDepth : mem 𝒩 depth (w 𝒩)) (hParameter : mem 𝒩 parameter (w 𝒩))
    (hInput : mem 𝒩 input (w 𝒩)) (hOutput : mem 𝒩 output (w 𝒩))
    (hChild : Graph 3 mode (if binder then suc 𝒩 depth else depth) parameter input output) :
    Graph 3 mode depth parameter (node 𝒩 tag [input]) (node 𝒩 tag [output]) := by
  have h := intro_rule h𝒩 (ObjectSyntaxTransform.unary tag binder) hRule
    (fun i : Fin 5 => [mode, depth, parameter, input, output][i])
    (values_natural (fields := [mode, depth, parameter, input, output]) (by simp [hMode, hDepth, hParameter, hInput, hOutput]))
    (by intro guard hg; cases hg) (by
      intro premise hp
      obtain rfl := List.mem_singleton.mp hp
      cases binder <;> simpa [ObjectSyntaxTransform.unary, expr_node, exprValue, Graph] using! hChild)
  simpa [ObjectSyntaxTransform.unary, expr_node, exprValue, Graph] using! h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceTransformConstruction
