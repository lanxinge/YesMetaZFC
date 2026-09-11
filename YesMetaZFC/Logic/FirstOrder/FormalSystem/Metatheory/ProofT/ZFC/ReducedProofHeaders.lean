import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureNaturalRosserAgreement
import YesMetaZFC.Model.ZFC.Pure.PureSourceCodingInversion
import YesMetaZFC.Model.ZFC.Pure.PureSourceHornConstruction

/-! # 完整证明图的内部根行反演

根规则决定证明码的自由变量数和结论字段，并保留指向证明节点行的前提边。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofHeaders
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open PureSourceCodingInversion PureSourceHorn PureSourceHornConstruction PureNaturalRosserAgreement
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem payload_variables (shape : ObjectProofTree.Shape) (i : Fin (shape.extra + 2)) :
    i ∈ (ObjectProofTree.payload shape).variables := by
  simp only [ObjectProofTree.payload, ObjectHorn.Expr.node, ObjectHorn.Expr.variables,
    List.nil_append, ObjectHorn.Expr.list_variables, List.mem_flatMap]
  exact ⟨.var i, List.mem_ofFn.mpr ⟨i,rfl⟩, List.mem_cons_self⟩

theorem payload_value (shape : ObjectProofTree.Shape) (values : Fin (shape.extra + 2) → 𝒩.Carrier .set) :
    exprValue 𝒩 values (ObjectProofTree.payload shape) = node 𝒩 shape.tag (List.ofFn values) := by
  simp [ObjectProofTree.payload, expr_node, List.map_ofFn, Function.comp_def, exprValue]

def Header (code conclusion : 𝒩.Carrier .set) : Prop :=
  ∃ tag : Nat, ∃ tail : List (𝒩.Carrier .set),
    (∀ value ∈ tail, mem 𝒩 value (w 𝒩)) ∧ code = node 𝒩 tag (z 𝒩 :: conclusion :: tail)

/-- 根行同时给出原节点行、真实头字段和结论的编码上界。 -/
theorem root_header_code (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {code trace conclusion : 𝒩.Carrier .set} (hCode : mem 𝒩 code (w 𝒩))
    (hConclusion : mem 𝒩 conclusion (w 𝒩))
    (hRow : Row 𝒩 (node 𝒩 1 [code, conclusion]) trace) :
    Header code conclusion ∧
      mem 𝒩 (node 𝒩 0 [code]) trace ∧
      mem 𝒩 conclusion (suc 𝒩 code) := by
  have hHorn : (ObjectHorn.step ObjectProofTree.rules).body.satisfies
      (templateEnv (.cons (node 𝒩 1 [code, conclusion]) (.cons trace .nil))) := hRow.1
  obtain ⟨rule, hRule, hStep⟩ := (step_satisfies _ _ _).mp hHorn
  obtain ⟨shape, hShape, hBranch⟩ := List.mem_flatMap.mp hRule
  rcases List.mem_cons.mp hBranch with hFalse | hTrue
  · subst rule
    obtain ⟨values, hBound, hHead, _, _⟩ := (rule_satisfies _ _ _).mp hStep
    have hNatural i := member_natural h𝒩 ((omega_closed h𝒩).2 _ (node_natural h𝒩 1 (by simp [hCode, hConclusion]))) (hBound i)
    have hPayload := expr_natural h𝒩 hNatural (ObjectProofTree.payload shape)
    have hHead' : node 𝒩 1 [code, conclusion] =
        node 𝒩 0 [exprValue 𝒩 values (ObjectProofTree.payload shape)] := by
      simpa [expr_node, exprValue] using! hHead
    have hTag := (node_injective h𝒩
      (by intro value hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hCode
          · exact hConclusion)
      (by intro value hv; obtain rfl := List.mem_singleton.mp hv; exact hPayload) hHead').1
    exact False.elim (Nat.zero_ne_one hTag.symm)
  · have hTrue' := List.mem_singleton.mp hTrue
    subst rule
    obtain ⟨values, hBound, hHead, hGuards, hPremises⟩ := (rule_satisfies _ _ _).mp hStep
    have hNatural i := member_natural h𝒩 ((omega_closed h𝒩).2 _ (node_natural h𝒩 1 (by simp [hCode, hConclusion]))) (hBound i)
    have hPayload := expr_natural h𝒩 hNatural (ObjectProofTree.payload shape)
    have hHead' : node 𝒩 1 [code, conclusion] =
        node 𝒩 1 [exprValue 𝒩 values (ObjectProofTree.payload shape), values 1] := by
      simpa [expr_node, exprValue] using! hHead
    have hFields := (node_injective h𝒩
      (by intro value hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hCode
          · exact hConclusion)
      (by intro value hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hPayload
          · exact hNatural 1) hHead').2
    have hParts : code = exprValue 𝒩 values (ObjectProofTree.payload shape) ∧
        conclusion = values 1 := by
      simpa only [List.cons.injEq, and_true] using hFields
    have hZeroGuard := hGuards (.var 0, .literal 1) (by simp)
    change mem 𝒩 (values 0) (suc 𝒩 (z 𝒩)) at hZeroGuard
    have hZero : values 0 = z 𝒩 := by
      rcases (successor_spec h𝒩 _ _).mp hZeroGuard with h | h
      · exact False.elim (empty_spec h𝒩 _ h)
      · exact h
    have hChild := hPremises (.node (.literal 0) [ObjectProofTree.payload shape]) (by simp)
    have hConclusionBound := expr_bound h𝒩 hNatural (ObjectProofTree.payload shape) (payload_variables shape 1)
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨shape.tag, List.ofFn (fun i : Fin shape.extra => values i.succ.succ), ?_, ?_⟩
      · intro value hv
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
        exact hNatural i.succ.succ
      · rw [hParts.1, payload_value]
        simp only [List.ofFn_succ]
        rw [hZero, hParts.2]
        rfl
    · simpa [expr_node, exprValue, ← hParts.1] using! hChild
    · simpa only [← hParts.1, ← hParts.2] using hConclusionBound

/-- 外部闭句入口保留，内部结论由一般根反演处理。 -/
theorem root_header (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {code trace : 𝒩.Carrier .set} (hCode : mem 𝒩 code (w 𝒩)) (formula : SetSentence)
    (hRow : Row 𝒩 (root 𝒩 code formula) trace) :
    Header code ((IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] [])) ∧
      mem 𝒩 (node 𝒩 0 [code]) trace ∧
      mem 𝒩 ((IntrinsicQuotation.quote formula).eval (Env.empty : Env 𝒩 [] [])) (suc 𝒩 code) := by
  rw [root_value] at hRow
  exact root_header_code h𝒩 hCode (quotation_natural h𝒩 formula) hRow

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofHeaders
