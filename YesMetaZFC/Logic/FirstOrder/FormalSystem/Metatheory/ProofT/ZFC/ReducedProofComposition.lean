import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofRowConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofCodeSemantics

/-! # 完整对象证明图的内部 modus ponens 闭包

合并两份原轨迹，插入 MP 节点行和结论根行。所有码和轨迹均来自当前模型，
既不要求它们外部标准，也不从内部证明码反推对象句子的真值。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofComposition
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity PureSourceNumerals
open PureSourceHorn PureSourceHornConstruction PureSourceProjection PureSourceTraceComposition
open ReducedProofHeaders ReducedProofLocalConstruction PureNaturalRosserAgreement ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics ObjectTrace
open NaturalRosserSemantics hiding mem
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

abbrev step : FormulaTemplate.Binary :=
  ObjectCheckedTrace.step ObjectProofTree.rules ReducedProofPresentation.rowTest.condition

theorem branch_variables (shape : ObjectProofTree.Shape) (root : Bool) (i : Fin (shape.extra + 2)) :
    i ∈ (ObjectProofTree.branch shape root).head.variables := by
  have h := payload_variables shape i
  cases root <;> simp [ObjectHorn.Expr.node, ObjectHorn.Expr.variables, ObjectHorn.Expr.list_variables, h]

theorem branch_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (shape : ObjectProofTree.Shape) (hShape : shape ∈ ObjectProofTree.shapes) (isRoot : Bool)
    (values : Fin (shape.extra + 2) → 𝒩.Carrier .set) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (row trace : 𝒩.Carrier .set) (hHead : row = exprValue 𝒩 values (ObjectProofTree.branch shape isRoot).head)
    (hGuards : ∀ guard ∈ (ObjectProofTree.branch shape isRoot).guards,
      mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2))
    (hPremises : ∀ premise ∈ (ObjectProofTree.branch shape isRoot).premises,
      mem 𝒩 (exprValue 𝒩 values premise) trace)
    (hLocal : Holds ReducedProofPresentation.rowTest.condition row) : Row 𝒩 row trace := by
  refine ⟨(step_satisfies ObjectProofTree.rules row trace).mpr
    ⟨_, ObjectProofTree.branch_mem shape hShape isRoot,
      (rule_satisfies _ row trace).mpr ⟨values, ?_, hHead, hGuards, hPremises⟩⟩, ?_⟩
  · intro i
    rw [hHead]
    exact expr_bound h𝒩 hValues _ (branch_variables shape isRoot i)
  · exact (unary_satisfies ReducedProofPresentation.rowTest.condition
      (templateEnv (.cons row (.cons trace .nil))) (.fvar .here)).mpr hLocal

/-- 六类节点共用的内部证明装配：收集子节点轨迹，验证局部条件，再连接根行。 -/
theorem codeProof_of_node (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (shape : ObjectProofTree.Shape) (hShape : shape ∈ ObjectProofTree.shapes)
    (values : Fin (shape.extra + 2) → 𝒩.Carrier .set) (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hClosedContext : values 0 = z 𝒩)
    (hLocal : Holds ReducedProofPresentation.nodeTest.condition (exprValue 𝒩 values (ObjectProofTree.payload shape)))
    (hChildren : ∀ index ∈ shape.children, Witness step (node 𝒩 0 [values index])) :
    mem 𝒩 (exprValue 𝒩 values (ObjectProofTree.payload shape)) (w 𝒩) ∧
      CodeProof 𝒩 (exprValue 𝒩 values (ObjectProofTree.payload shape)) (values 1) := by
  let code := exprValue 𝒩 values (ObjectProofTree.payload shape)
  have hCode := expr_natural h𝒩 hValues (ObjectProofTree.payload shape)
  have hMono : Monotone (𝒩 := 𝒩) step :=
    checked_monotone ObjectProofTree.rules ReducedProofPresentation.rowTest.condition
  obtain ⟨trace, hTrace, hMembers, hClosed⟩ := collect h𝒩 step hMono
    (shape.children.map (fun i => node 𝒩 0 [values i])) (by
      intro row hr
      obtain ⟨index, hi, rfl⟩ := List.mem_map.mp hr
      exact hChildren index hi)
  have hNodeNatural := node_natural h𝒩 0 (fields := [code]) (by simp [code, hCode])
  have hNodeStep : Row 𝒩 (node 𝒩 0 [code]) trace := by
    apply branch_step h𝒩 shape hShape false values hValues
    · simp [expr_node, code]
    · intro guard hg; cases hg
    · intro child hc
      obtain ⟨index, hi, rfl⟩ := List.mem_map.mp hc
      simpa [expr_node, exprValue] using! hMembers _ (List.mem_map.mpr ⟨index, hi, rfl⟩)
    · exact ReducedProofRowConstruction.node_row h𝒩 hCode hLocal
  obtain ⟨extended, hExtendedBound, _, hNodeMember, hExtendedClosed⟩ :=
    insert h𝒩 step hMono hTrace hNodeNatural hClosed hNodeStep
  have hRootStep : Row 𝒩 (node 𝒩 1 [code, values 1]) extended := by
    apply branch_step h𝒩 shape hShape true values hValues
    · simp [expr_node, exprValue, code]
    · intro guard hg
      obtain rfl := List.mem_singleton.mp hg
      change mem 𝒩 (values 0) (suc 𝒩 (z 𝒩))
      rw [hClosedContext]
      exact (successor_spec h𝒩 _ _).mpr (Or.inr rfl)
    · intro child hc
      obtain rfl := List.mem_singleton.mp hc
      simpa [expr_node, exprValue, code] using! hNodeMember
    · exact ReducedProofRowConstruction.root_row h𝒩 hCode (hValues 1)
  obtain ⟨finalTrace, hFinalBound, _, hRootMember, hFinalClosed⟩ :=
    insert h𝒩 step hMono hExtendedBound
      (node_natural h𝒩 1 (fields := [code, values 1]) (by simp [code, hCode, hValues 1]))
      hExtendedClosed hRootStep
  exact ⟨hCode, (codeProof_trace _ _).mpr ⟨finalTrace, hFinalBound, hRootMember, hFinalClosed⟩⟩

/-- MP 同时允许非标准证明码与非标准结论码；实际语法检查保留。 -/
theorem modus_ponens_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {φ ψ premise implication : 𝒩.Carrier .set}
    (hφ : mem 𝒩 φ (w 𝒩)) (hψ : mem 𝒩 ψ (w 𝒩))
    (hSyntaxφ : Holds (queryTest .syntax).condition (node 𝒩 4 [z 𝒩, z 𝒩, φ]))
    (hSyntaxψ : Holds (queryTest .syntax).condition (node 𝒩 4 [z 𝒩, z 𝒩, ψ]))
    (hp : mem 𝒩 premise (w 𝒩)) (hi : mem 𝒩 implication (w 𝒩))
    (hPremise : CodeProof 𝒩 premise φ) (hImplication : CodeProof 𝒩 implication (node 𝒩 7 [φ, ψ])) :
    mem 𝒩 (mpCodeOf 𝒩 premise implication ψ) (w 𝒩) ∧
      CodeProof 𝒩 (mpCodeOf 𝒩 premise implication ψ) ψ := by
  obtain ⟨left, hLeftBound, hLeftRoot, hLeftClosed⟩ := (codeProof_trace premise φ).mp hPremise
  obtain ⟨right, hRightBound, hRightRoot, hRightClosed⟩ := (codeProof_trace _ _).mp hImplication
  have hpHeader := root_header_code h𝒩 hp hφ (hLeftClosed _ hLeftRoot)
  have hiHeader := root_header_code h𝒩 hi (node_natural h𝒩 7 (by simp [hφ, hψ])) (hRightClosed _ hRightRoot)
  let values : Fin 4 → 𝒩.Carrier .set := fun i => [z 𝒩, ψ, premise, implication][i]
  have hValues : ∀ i, mem 𝒩 (values i) (w 𝒩) :=
    values_natural (fields := [z 𝒩, ψ, premise, implication]) (by simp [(omega_closed h𝒩).1, hψ, hp, hi])
  have hLocal := mp_local_code h𝒩 hφ hψ hSyntaxφ hSyntaxψ hp hi hpHeader.1 hiHeader.1 hpHeader.2.2
  have h := codeProof_of_node h𝒩 ObjectProofTree.mpShape (by simp [ObjectProofTree.shapes]) values hValues rfl
    (by simpa [values, expr_node, exprValue, mpCodeOf] using! hLocal) (by
      intro index hi
      simp only [ObjectProofTree.mpShape, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ⟨left, hLeftBound, hpHeader.2.1, hLeftClosed⟩
      · exact ⟨right, hRightBound, hiHeader.2.1, hRightClosed⟩)
  simpa [values, expr_node, exprValue, mpCodeOf] using! h

/-- 原 D2 入口保留，标准闭句只是内部公式码构造的特例。 -/
theorem modus_ponens (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (φ ψ : SetSentence)
    {premise implication : 𝒩.Carrier .set}
    (hp : mem 𝒩 premise (w 𝒩)) (hi : mem 𝒩 implication (w 𝒩))
    (hPremise : Proof 𝒩 premise φ) (hImplication : Proof 𝒩 implication (Formula.imp φ ψ)) :
    mem 𝒩 (mpCode 𝒩 premise implication ψ) (w 𝒩) ∧
      Proof 𝒩 (mpCode 𝒩 premise implication ψ) ψ := by
  have hImp : CodeProof 𝒩 implication (node 𝒩 7 [quoteValue 𝒩 φ, quoteValue 𝒩 ψ]) := by
    rw [← quote_imp]
    exact hImplication
  exact modus_ponens_code h𝒩 (quotation_natural h𝒩 φ) (quotation_natural h𝒩 ψ)
    (syntax_query h𝒩 φ) (syntax_query h𝒩 ψ) hp hi hPremise hImp

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofComposition
