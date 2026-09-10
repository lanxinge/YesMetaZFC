import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceTransformConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceFormulaConstruction

/-! # 内部公式码上的逻辑公理与存在引入

公理模式使用原有局部检查器，证明装配复用六类节点的共同构造。
存在引入保留正文、替换项、实例语法和实际模式 2 变换的全部义务。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofLogicalConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceHorn PureSourceHornConstruction PureSourceProjection PureSourceTraceComposition
open ReducedProofLocalConstruction ReducedProofCodeSemantics ReducedProofComposition
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem syntax_unary (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (tag : Nat) (binder : Bool) (hRule : ObjectFormulaSyntax.unaryRule tag binder ∈ ObjectFormulaSyntax.rules)
    {bound free body : 𝒩.Carrier .set}
    (hBound : mem 𝒩 bound (w 𝒩)) (hFree : mem 𝒩 free (w 𝒩)) (hBody : mem 𝒩 body (w 𝒩))
    (hSyntax : Holds (queryTest .syntax).condition
      (node 𝒩 4 [if binder then suc 𝒩 bound else bound, free, body])) :
    Holds (queryTest .syntax).condition (node 𝒩 4 [bound, free, node 𝒩 tag [body]]) :=
  (syntax_satisfies _).mpr (PureSourceFormulaConstruction.unary h𝒩 tag binder hRule
    hBound hFree hBody ((syntax_satisfies _).mp hSyntax))

/-- 二十七类逻辑公理模式共享的内部实例入口。 -/
theorem logical_rule (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (shape : ObjectLogicalAxiom.Shape) (hShape : shape ∈ ObjectLogicalAxiom.shapes)
    (values : Fin shape.arity → 𝒩.Carrier .set) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hQueries : ∀ query ∈ shape.queries,
      Holds (queryTest (if query.1 then .transform else .syntax)).condition (exprValue 𝒩 values query.2)) :
    Holds (queryTest .logical).condition (exprValue 𝒩 values shape.head) := by
  change Holds (ObjectLocalDecision.template (ObjectLogicalAxiom.shapes.map
    (fun shape => shape.compile (queryTest .syntax) (queryTest .transform)))) _
  apply (ObjectLocalDecision.template_satisfies _ _).mpr
  refine ⟨shape.compile (queryTest .syntax) (queryTest .transform), List.mem_map.mpr ⟨shape, hShape, rfl⟩,
    (local_rule_satisfies _ _).mpr ⟨values, ?_, rfl, ?_⟩⟩
  · intro i
    exact expr_bound h𝒩 hValues shape.head (ObjectLogicalAxiom.head_variables shape hShape i)
  · intro query hq
    obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hq
    have h := hQueries original hOriginal
    cases hKind : original.1 <;> simpa [hKind] using! h

def logicalCode (𝒩 : Structure.{0,0,0,x} signature) (conclusion packet : 𝒩.Carrier .set) : 𝒩.Carrier .set :=
  node 𝒩 0 [z 𝒩, conclusion, packet]

theorem of_logical_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {conclusion packet : 𝒩.Carrier .set} (hc : mem 𝒩 conclusion (w 𝒩)) (hp : mem 𝒩 packet (w 𝒩))
    (hLogical : Holds (queryTest .logical).condition (node 𝒩 0 [z 𝒩, packet, conclusion])) :
    mem 𝒩 (logicalCode 𝒩 conclusion packet) (w 𝒩) ∧ CodeProof 𝒩 (logicalCode 𝒩 conclusion packet) conclusion := by
  let values : Fin 3 → 𝒩.Carrier .set := fun i => [z 𝒩, conclusion, packet][i]
  have hValues : ∀ i, mem 𝒩 (values i) (w 𝒩) :=
    values_natural (fields := [z 𝒩, conclusion, packet]) (by simp [(omega_closed h𝒩).1, hc, hp])
  have hLocal : Holds ReducedProofPresentation.nodeTest.condition (logicalCode 𝒩 conclusion packet) := by
    apply (node_local_satisfies _).mpr
    refine ⟨ObjectProofNode.logicalShape, (by simp [ObjectProofNode.shapes]), values, ?_, ?_, ?_⟩
    · intro i
      have h := expr_bound h𝒩 hValues ObjectProofNode.logicalShape.head
        ((by decide +kernel : ∀ i : Fin 3, i ∈ ObjectProofNode.logicalShape.head.variables) i)
      simpa [values, expr_node, exprValue, logicalCode] using! h
    · simp [values, expr_node, exprValue, logicalCode]
    · intro query hq
      obtain rfl := List.mem_singleton.mp hq
      simpa [values, expr_node, exprValue] using! hLogical
  have h := codeProof_of_node h𝒩 ObjectProofTree.logicalShape (by simp [ObjectProofTree.shapes]) values hValues rfl
    (by simpa [values, expr_node, exprValue, logicalCode] using! hLocal) (by intro index hi; cases hi)
  simpa [values, expr_node, exprValue, logicalCode] using! h

theorem forall_axiom (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {body witness instanceCode : 𝒩.Carrier .set}
    (hBody : mem 𝒩 body (w 𝒩)) (hWitness : mem 𝒩 witness (w 𝒩)) (hInstance : mem 𝒩 instanceCode (w 𝒩))
    (hBodySyntax : Holds (queryTest .syntax).condition (node 𝒩 4 [numeral 𝒩 1, z 𝒩, body]))
    (hTermSyntax : Holds (queryTest .syntax).condition (node 𝒩 0 [z 𝒩, z 𝒩, witness]))
    (hTransform : PureSourceTransformConstruction.Graph 3 (numeral 𝒩 2) (z 𝒩) witness body instanceCode) :
    mem 𝒩 (logicalCode 𝒩 (node 𝒩 7 [(node 𝒩 9 [body]), instanceCode]) (node 𝒩 20 [body, witness])) (w 𝒩) ∧
      CodeProof 𝒩 (logicalCode 𝒩 (node 𝒩 7 [(node 𝒩 9 [body]), instanceCode]) (node 𝒩 20 [body, witness]))
        (node 𝒩 7 [(node 𝒩 9 [body]), instanceCode]) := by
  have hExist := node_natural h𝒩 9 (fields := [body]) (by simp [hBody])
  apply of_logical_code h𝒩 (node_natural h𝒩 7 (by simp [hInstance, hExist]))
    (node_natural h𝒩 20 (by simp [hBody, hWitness]))
  let values : Fin 4 → 𝒩.Carrier .set := fun i => [z 𝒩, body, witness, instanceCode][i]
  have h := logical_rule h𝒩 ObjectLogicalAxiom.rule20 (by simp [ObjectLogicalAxiom.shapes]) values
    (values_natural (fields := [z 𝒩, body, witness, instanceCode]) (by simp [(omega_closed h𝒩).1, hBody, hWitness, hInstance])) (by
      intro query hq
      simp only [ObjectLogicalAxiom.rule20, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · simpa [values, expr_node, exprValue] using! hBodySyntax
      · simpa [values, expr_node, exprValue] using! hTermSyntax
      · simpa [values, expr_node, exprValue] using! (transform_satisfies _).mpr hTransform)
  simpa [values, expr_node, exprValue] using! h

theorem exists_axiom (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {body witness instanceCode : 𝒩.Carrier .set}
    (hBody : mem 𝒩 body (w 𝒩)) (hWitness : mem 𝒩 witness (w 𝒩)) (hInstance : mem 𝒩 instanceCode (w 𝒩))
    (hBodySyntax : Holds (queryTest .syntax).condition (node 𝒩 4 [numeral 𝒩 1, z 𝒩, body]))
    (hTermSyntax : Holds (queryTest .syntax).condition (node 𝒩 0 [z 𝒩, z 𝒩, witness]))
    (hTransform : PureSourceTransformConstruction.Graph 3 (numeral 𝒩 2) (z 𝒩) witness body instanceCode) :
    mem 𝒩 (logicalCode 𝒩 (node 𝒩 7 [instanceCode, node 𝒩 10 [body]]) (node 𝒩 23 [body, witness])) (w 𝒩) ∧
      CodeProof 𝒩 (logicalCode 𝒩 (node 𝒩 7 [instanceCode, node 𝒩 10 [body]]) (node 𝒩 23 [body, witness]))
        (node 𝒩 7 [instanceCode, node 𝒩 10 [body]]) := by
  have hExist := node_natural h𝒩 10 (fields := [body]) (by simp [hBody])
  apply of_logical_code h𝒩 (node_natural h𝒩 7 (by simp [hInstance, hExist]))
    (node_natural h𝒩 23 (by simp [hBody, hWitness]))
  let values : Fin 4 → 𝒩.Carrier .set := fun i => [z 𝒩, body, witness, instanceCode][i]
  have h := logical_rule h𝒩 ObjectLogicalAxiom.rule23 (by simp [ObjectLogicalAxiom.shapes]) values
    (values_natural (fields := [z 𝒩, body, witness, instanceCode]) (by simp [(omega_closed h𝒩).1, hBody, hWitness, hInstance])) (by
      intro query hq
      simp only [ObjectLogicalAxiom.rule23, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · simpa [values, expr_node, exprValue] using! hBodySyntax
      · simpa [values, expr_node, exprValue] using! hTermSyntax
      · simpa [values, expr_node, exprValue] using! (transform_satisfies _).mpr hTransform)
  simpa [values, expr_node, exprValue] using! h

/-- 非标准实例的证明可经实际存在公理与 MP 转成存在句子的证明。 -/
theorem exists_introduction (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {body witness instanceCode proof : 𝒩.Carrier .set}
    (hBody : mem 𝒩 body (w 𝒩)) (hWitness : mem 𝒩 witness (w 𝒩)) (hInstance : mem 𝒩 instanceCode (w 𝒩))
    (hBodySyntax : Holds (queryTest .syntax).condition (node 𝒩 4 [numeral 𝒩 1, z 𝒩, body]))
    (hTermSyntax : Holds (queryTest .syntax).condition (node 𝒩 0 [z 𝒩, z 𝒩, witness]))
    (hInstanceSyntax : Holds (queryTest .syntax).condition (node 𝒩 4 [z 𝒩, z 𝒩, instanceCode]))
    (hTransform : PureSourceTransformConstruction.Graph 3 (numeral 𝒩 2) (z 𝒩) witness body instanceCode)
    (hProof : mem 𝒩 proof (w 𝒩)) (hDerives : CodeProof 𝒩 proof instanceCode) :
    ∃ result, mem 𝒩 result (w 𝒩) ∧ CodeProof 𝒩 result (node 𝒩 10 [body]) := by
  have hAxiom := exists_axiom h𝒩 hBody hWitness hInstance hBodySyntax hTermSyntax hTransform
  have hExist := node_natural h𝒩 10 (fields := [body]) (by simp [hBody])
  have hExistSyntax := syntax_unary h𝒩 10 true (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules])
    (omega_closed h𝒩).1 (omega_closed h𝒩).1 hBody hBodySyntax
  exact ⟨_, modus_ponens_code h𝒩 hInstance hExist hInstanceSyntax hExistSyntax hProof hAxiom.1 hDerives hAxiom.2⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofLogicalConstruction
