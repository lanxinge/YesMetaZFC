import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProofTree
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreeReplay

/-! # 完整证明树检查器的逐节点规格 -/
namespace YesMetaZFC.Automation.ObjectProofTree
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open ObjectHorn ObjectCodeProjection
set_option autoImplicit false

@[simp] theorem payload_free (shape : Shape) (values : Fin (shape.extra + 2) → Nat) :
    field (payloadValue shape values) 0 = values 0 := by
  simp [payloadValue, List.ofFn_succ]

@[simp] theorem payload_formula (shape : Shape) (values : Fin (shape.extra + 2) → Nat) :
    field (payloadValue shape values) 1 = values 1 := by
  simp [payloadValue, List.ofFn_succ]

theorem payload_children (shape : Shape) (h : shape ∈ shapes) (values : Fin (shape.extra + 2) → Nat) :
    ProofTreeCode.childCodes (payloadValue shape values) = shape.children.map values := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [logicalShape, theoryShape, mpShape, forallShape, strengtheningShape,
    substitutionShape, payloadValue, List.ofFn_succ, ProofTreeCode.childCodes]

theorem node_iff (localCheck : Nat → Bool) (code : Nat) :
    nodeChecked localCheck code = true ↔ localCheck code = true ∧
      ∃ shape, shape ∈ shapes ∧ ∃ values : Fin (shape.extra + 2) → Nat,
        code = payloadValue shape values ∧
        ∀ i, i ∈ shape.children → nodeChecked localCheck (values i) = true := by
  rw [nodeChecked, ObjectCheckedTrace.check_eq_true_iff _ _ _ descending]
  simp only [rowCheck, tag_node, field_node, get_zero, if_true]
  constructor
  · rintro ⟨hLocal, rule, hRule, values, hBound, hHead, hGuards, hPremises⟩
    obtain ⟨shape, hShape, hRule⟩ := List.mem_flatMap.mp hRule
    rcases List.mem_cons.mp hRule with rfl | hRule
    · change Fin (shape.extra + 2) → Nat at values
      have hCode : code = payloadValue shape values := by simpa only [Expr.node_eval, List.map_cons, List.map_nil, Expr.eval, payload_eval,
        Bool.false_eq_true, if_false, nodeValue_eq_iff, List.cons.injEq, and_true, true_and] using hHead
      refine ⟨hLocal, shape, hShape, values, hCode, ?_⟩
      intro i hi
      have hp := hPremises (.node (.literal 0) [.var i]) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      simpa only [nodeChecked, Expr.node_eval, List.map_cons, List.map_nil, Expr.eval] using hp
    · have hRule := List.mem_singleton.mp hRule
      subst rule
      change Fin (shape.extra + 2) → Nat at values
      simp only [Expr.node_eval, List.map_cons, List.map_nil, Expr.eval, payload_eval, if_true, nodeValue_eq_iff, Nat.zero_ne_one, false_and] at hHead
  · rintro ⟨hLocal, shape, hShape, values, hCode, hChildren⟩
    have h := node_intro localCheck shape hShape values (hCode ▸ hLocal) hChildren
    have hOriginal : nodeChecked localCheck code = true := by rw [hCode]; exact h
    have hStep := (ObjectCheckedTrace.check_eq_true_iff (rowCheck localCheck) rules rank descending
      (nodeValue 0 [code])).mp hOriginal
    simpa only [rowCheck, tag_node, field_node, get_zero, if_true] using hStep

theorem root_iff (localCheck : Nat → Bool) (code conclusion : Nat) :
    checked localCheck code conclusion = true ↔
      ∃ shape, shape ∈ shapes ∧ ∃ values : Fin (shape.extra + 2) → Nat,
        code = payloadValue shape values ∧ conclusion = values 1 ∧ values 0 = 0 ∧
        nodeChecked localCheck code = true := by
  constructor
  · intro h
    obtain ⟨_, rule, hRule, values, hBound, hHead, hGuards, hPremises⟩ :=
      (ObjectCheckedTrace.check_eq_true_iff _ _ _ descending _).mp h
    obtain ⟨shape, hShape, hRule⟩ := List.mem_flatMap.mp hRule
    rcases List.mem_cons.mp hRule with rfl | hRule
    · change Fin (shape.extra + 2) → Nat at values
      simp only [Expr.node_eval, List.map_cons, List.map_nil, Expr.eval, payload_eval, Bool.false_eq_true, if_false, nodeValue_eq_iff, Nat.one_ne_zero, false_and] at hHead
    · have hRule := List.mem_singleton.mp hRule
      subst rule
      change Fin (shape.extra + 2) → Nat at values
      have hHead' : code = payloadValue shape values ∧ conclusion = values 1 := by
        simpa only [Expr.node_eval, List.map_cons, List.map_nil, Expr.eval, payload_eval, if_true, nodeValue_eq_iff, List.cons.injEq, and_true, true_and] using hHead
      have hZero : values 0 = 0 := by
        have hg : values 0 < 1 := hGuards _ List.mem_cons_self
        omega
      have hNode := hPremises _ List.mem_cons_self
      refine ⟨shape, hShape, values, hHead'.1, hHead'.2, hZero, ?_⟩
      rw [hHead'.1]
      simpa only [nodeChecked, Expr.node_eval, List.map_cons, List.map_nil, Expr.eval, payload_eval] using hNode
  · rintro ⟨shape, hShape, values, hCode, hConclusion, hZero, hNode⟩
    rw [hCode, hConclusion]
    exact root_intro localCheck shape hShape values hZero (hCode ▸ hNode)

/-- 根连接同时检查闭上下文与结论码，不接受仅有形状正确的开证明。 -/
theorem checked_of_node (localCheck : Nat → Bool) (code conclusion : Nat)
    (hClosed : field code 0 = 0) (hConclusion : field code 1 = conclusion)
    (hNode : nodeChecked localCheck code = true) : checked localCheck code conclusion = true := by
  obtain ⟨_, shape, hShape, values, hCode, _⟩ := (node_iff localCheck code).mp hNode
  have hZero : values 0 = 0 := by simpa only [hCode, payload_free] using hClosed
  have hFormula : conclusion = values 1 := by simpa only [hCode, payload_formula] using hConclusion.symm
  exact (root_iff localCheck code conclusion).mpr ⟨shape, hShape, values, hCode, hFormula, hZero, hNode⟩

end YesMetaZFC.Automation.ObjectProofTree
