import YesMetaZFC.Model.ZFC.Pure.PureSourceTermConstruction

/-! # 任意内部子码上的完整公式语法证书

所有入口均使用当前公式检查器的规则，不要求子码来自外部标准 AST。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceFormulaConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceHornConstruction PureSourceProjection PureSourceTraceComposition PureSourceTermConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def FormulaGraph (bound free input : 𝒩.Carrier .set) : Prop :=
  Witness (ObjectHorn.step ObjectFormulaSyntax.rules) (node 𝒩 4 [bound, free, input])

theorem syntax_support : Supports ObjectFormulaSyntax.rules := fun _ h => List.mem_append_left _ h

theorem constant (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (tag : Nat)
    (hRule : ObjectFormulaSyntax.constantRule tag ∈ ObjectFormulaSyntax.rules)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩)) :
    FormulaGraph bound free (node 𝒩 tag []) := by
  have h := rule_intro h𝒩 ObjectFormulaSyntax.rules (ObjectFormulaSyntax.constantRule tag) hRule
    (fun i : Fin 2 => [bound, free][i])
    (values_natural (fields := [bound, free]) (by simp [hBound, hFree]))
    (ObjectFormulaSyntax.head_variables _ hRule)
    (by intro guard hg; cases hg) (by intro premise hp; cases hp)
  simpa [ObjectFormulaSyntax.constantRule, ObjectTermSyntax.node, expr_node, exprValue, FormulaGraph] using! h

theorem relation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free : 𝒩.Carrier .set} (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (symbol : RelationSymbol) (fields : List (𝒩.Carrier .set))
    (hFields : ∀ field ∈ fields, mem 𝒩 field (w 𝒩))
    (hArguments : ArgumentsGraph ObjectFormulaSyntax.rules bound free
      (numeral 𝒩 (signature.relDomain symbol).length) (fieldsCode 𝒩 fields)) :
    FormulaGraph bound free (node 𝒩 2 (node 𝒩 symbol.ctorIdx [] :: fields)) := by
  have hRule : ObjectFormulaSyntax.relationRule symbol ∈ ObjectFormulaSyntax.rules := by
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨symbol, (by cases symbol <;> simp [SyntaxDecode.relationSymbols]), rfl⟩
  have h := rule_intro h𝒩 ObjectFormulaSyntax.rules (ObjectFormulaSyntax.relationRule symbol) hRule
    (fun i : Fin 3 => [bound, free, fieldsCode 𝒩 fields][i])
    (values_natural (fields := [bound, free, fieldsCode 𝒩 fields])
      (by simp [hBound, hFree, fields_natural h𝒩 hFields]))
    (ObjectFormulaSyntax.head_variables _ hRule) (by intro guard hg; cases hg) (by
      intro premise hp
      obtain rfl := List.mem_singleton.mp hp
      simpa [ObjectFormulaSyntax.relationRule, ObjectTermSyntax.node, expr_node, exprValue,
        ArgumentsGraph] using! hArguments)
  simpa [ObjectFormulaSyntax.relationRule, ObjectTermSyntax.node, ObjectTermSyntax.rawNode,
    ObjectTermSyntax.cons, expr_node, exprValue, FormulaGraph, node, fieldsCode] using! h

theorem equality (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free left right : 𝒩.Carrier .set}
    (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩))
    (hLeftGraph : TermGraph ObjectFormulaSyntax.rules bound free left) (hRightGraph : TermGraph ObjectFormulaSyntax.rules bound free right) :
    FormulaGraph bound free (node 𝒩 3 [left, right]) := by
  have hRule : ObjectFormulaSyntax.equalityRule ∈ ObjectFormulaSyntax.rules := by
    simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]
  have h := rule_intro h𝒩 ObjectFormulaSyntax.rules ObjectFormulaSyntax.equalityRule hRule
    (fun i : Fin 4 => [bound, free, left, right][i])
    (values_natural (fields := [bound, free, left, right]) (by simp [hBound, hFree, hLeft, hRight]))
    (ObjectFormulaSyntax.head_variables _ hRule) (by intro guard hg; cases hg) (by
      intro premise hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa [ObjectFormulaSyntax.equalityRule, ObjectTermSyntax.node, expr_node, exprValue,
          FormulaGraph, TermGraph] using! hLeftGraph
      · obtain rfl := List.mem_singleton.mp hp
        simpa [ObjectFormulaSyntax.equalityRule, ObjectTermSyntax.node, expr_node, exprValue,
          FormulaGraph, TermGraph] using! hRightGraph)
  simpa [ObjectFormulaSyntax.equalityRule, ObjectTermSyntax.node, expr_node, exprValue, FormulaGraph] using! h

theorem binary (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (tag : Nat)
    (hRule : ObjectFormulaSyntax.binaryRule tag ∈ ObjectFormulaSyntax.rules)
    {bound free left right : 𝒩.Carrier .set}
    (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩))
    (hLeft : mem 𝒩 left (w 𝒩)) (hRight : mem 𝒩 right (w 𝒩))
    (hLeftGraph : FormulaGraph bound free left) (hRightGraph : FormulaGraph bound free right) :
    FormulaGraph bound free (node 𝒩 tag [left, right]) := by
  have h := rule_intro h𝒩 ObjectFormulaSyntax.rules (ObjectFormulaSyntax.binaryRule tag) hRule
    (fun i : Fin 4 => [bound, free, left, right][i])
    (values_natural (fields := [bound, free, left, right]) (by simp [hBound, hFree, hLeft, hRight]))
    (ObjectFormulaSyntax.head_variables _ hRule) (by intro guard hg; cases hg) (by
      intro premise hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa [ObjectFormulaSyntax.binaryRule, ObjectTermSyntax.node, expr_node, exprValue,
          FormulaGraph, TermGraph] using! hLeftGraph
      · obtain rfl := List.mem_singleton.mp hp
        simpa [ObjectFormulaSyntax.binaryRule, ObjectTermSyntax.node, expr_node, exprValue,
          FormulaGraph, TermGraph] using! hRightGraph)
  simpa [ObjectFormulaSyntax.binaryRule, ObjectTermSyntax.node, expr_node, exprValue, FormulaGraph] using! h

theorem unary (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (tag : Nat) (binder : Bool) (hRule : ObjectFormulaSyntax.unaryRule tag binder ∈ ObjectFormulaSyntax.rules)
    {bound free body : 𝒩.Carrier .set}
    (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩)) (hBody : mem 𝒩 body (w 𝒩))
    (hBodyGraph : FormulaGraph (if binder then suc 𝒩 bound else bound) free body) :
    FormulaGraph bound free (node 𝒩 tag [body]) := by
  have h := rule_intro h𝒩 ObjectFormulaSyntax.rules (ObjectFormulaSyntax.unaryRule tag binder) hRule
    (fun i : Fin 3 => [bound, free, body][i])
    (values_natural (fields := [bound, free, body]) (by simp [hBound, hFree, hBody]))
    (ObjectFormulaSyntax.head_variables _ hRule) (by intro guard hg; cases hg) (by
      intro premise hp
      obtain rfl := List.mem_singleton.mp hp
      cases binder <;> simpa [ObjectFormulaSyntax.unaryRule, ObjectTermSyntax.node, expr_node, exprValue,
        FormulaGraph] using! hBodyGraph)
  simpa [ObjectFormulaSyntax.unaryRule, ObjectTermSyntax.node, expr_node, exprValue, FormulaGraph] using! h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceFormulaConstruction
