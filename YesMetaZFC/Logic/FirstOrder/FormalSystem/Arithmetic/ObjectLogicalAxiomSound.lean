import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLogicalAxiom

/-! # 逻辑公理局部模式的类型可靠性

任意被接受的数码都重构为实际 HilbertBaseAxiom 证书，并保留参数码与结论码。
-/
namespace YesMetaZFC.Automation.ObjectLogicalAxiom
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn ObjectCodeProjection
set_option autoImplicit false

abbrev ctx (n : Nat) : SetContext := List.replicate n SetSort.set

inductive Meaning : Nat → Prop where
  | logical (free : Nat) (formula : SetOpenFormula (ctx free)) (certificate : HilbertBaseAxiom signature formula) :
      Meaning (nodeValue 0 [free, treeValue (LogicalAxiomEncode.encode certificate), treeValue (SyntaxEncode.formula formula)])

private theorem formula_query (bound free input : Nat)
    (h : queryChecked false (nodeValue 4 [bound, free, input]) = true) :
    ∃ formula : SetFormula (ctx bound) (ctx free), treeValue (SyntaxEncode.formula formula) = input := by
  exact (ObjectFormulaSyntax.checked_iff (ctx bound) (ctx free) input).mp (by simpa [ctx, queryChecked, ObjectFormulaSyntax.checked] using h)

private theorem term_query (free input : Nat)
    (h : queryChecked false (nodeValue 0 [0, free, input]) = true) :
    ∃ term : SetOpenTerm (ctx free), treeValue (SyntaxEncode.term term) = input := by
  exact (ObjectFormulaSyntax.checked_term_iff [] (ctx free) input).mp (by simpa [ctx, queryChecked] using h)

private theorem abstract_query {free : SetContext} (input : SetOpenFormula (SetSort.set :: free)) (output : Nat)
    (h : queryChecked true (nodeValue 3 [1, 0, 0, treeValue (SyntaxEncode.formula input), output]) = true) :
    treeValue (SyntaxEncode.formula input.abstractFreeTop) = output :=
  (ObjectSyntaxTransform.checked_abstractTop input output).mp h

private theorem instantiate_query {free : SetContext} (input : SetFormula [SetSort.set] free)
    (point : SetOpenTerm free) (output : Nat)
    (h : queryChecked true (nodeValue 3 [2, 0, treeValue (SyntaxEncode.term point), treeValue (SyntaxEncode.formula input), output]) = true) :
    treeValue (SyntaxEncode.formula (input.instantiateTop point)) = output :=
  (ObjectSyntaxTransform.checked_instantiateTop input point output).mp h

attribute [local simp] LogicalAxiomEncode.encode SyntaxEncode.formula Formula.forallFreeTop
  Formula.existsFreeTop SyntaxCodeRenaming.vacuous_body head node imp neg conj disj iffE allE exE eqE
  List.finRange_succ leaf

set_option maxHeartbeats 1000000 in
private theorem rule_sound (shape : Shape) (hShape : shape ∈ shapes) (values : Fin shape.arity → Nat)
    (hQueries : ∀ query, query ∈ shape.queries → queryChecked query.1 (query.2.eval values) = true) :
    Meaning (shape.head.eval values) := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at hShape
  rcases hShape with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [rule0, rule1, rule2, rule3, rule4, rule5, rule6, rule7, rule8, rule9, rule10, rule11, rule12, rule13, rule14, rule15, rule16, rule17, rule18, rule19, rule20, rule21, rule22, rule23, rule24, rule25, rule26, prop] at values hQueries ⊢
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    obtain ⟨a3, h3⟩ := formula_query 0 (values 0) (values 3)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 3)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.implication_distribution a1 a2 a3)
    simpa [Expr.eval, h1, h2, h3] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.self_implication a1)
    simpa [Expr.eval, h1] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.weakening a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.contradiction a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.classical a1)
    simpa [Expr.eval, h1] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.explosion a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.case_analysis a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · have hMeaning := Meaning.logical (values 0) _ (.truth_intro)
    simpa [Expr.eval] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.falsum_elimination a1)
    simpa [Expr.eval, h1] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.negation_intro a1)
    simpa [Expr.eval, h1] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.negation_elimination a1)
    simpa [Expr.eval, h1] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.conjunction_intro a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.conjunction_elim_left a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.conjunction_elim_right a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.disjunction_intro_left a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.disjunction_intro_right a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    obtain ⟨a3, h3⟩ := formula_query 0 (values 0) (values 3)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 3)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.disjunction_elimination a1 a2 a3)
    simpa [Expr.eval, h1, h2, h3] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.biconditional_intro a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.biconditional_elim_left a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨a1, h1⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨a2, h2⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.biconditional_elim_right a1 a2)
    simpa [Expr.eval, h1, h2] using hMeaning
  · obtain ⟨body, hbody⟩ := formula_query 1 (values 0) (values 1)
      (hQueries (grammar false (.literal 1) (.var 0) (.var 1)) (by simp))
    obtain ⟨point, hpoint⟩ := term_query (values 0) (values 2)
      (hQueries (grammar true (.literal 0) (.var 0) (.var 2)) (by simp))
    have hResult3 := instantiate_query body point (values 3) (by
      rw [hbody, hpoint]
      exact hQueries (transform 2 (.var 2) (.var 1) (.var 3)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.forall_specialization SetSort.set body point)
    simpa [Expr.eval, hbody, hpoint, hResult3] using hMeaning
  · obtain ⟨a, ha⟩ := formula_query 0 (values 0 + 1) (values 1)
      (hQueries (grammar false (.literal 0) (.succ (.var 0)) (.var 1)) (by simp))
    obtain ⟨b, hb⟩ := formula_query 0 (values 0 + 1) (values 2)
      (hQueries (grammar false (.literal 0) (.succ (.var 0)) (.var 2)) (by simp))
    have hResult3 := abstract_query a (values 3) (by
      rw [ha]
      exact hQueries (transform 1 (.literal 0) (.var 1) (.var 3)) (by simp))
    have hResult4 := abstract_query b (values 4) (by
      rw [hb]
      exact hQueries (transform 1 (.literal 0) (.var 2) (.var 4)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.forall_distribution SetSort.set a b)
    simpa [Expr.eval, ha, hb, hResult3, hResult4] using hMeaning
  · obtain ⟨body, hbody⟩ := formula_query 0 (values 0) (values 1)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 1)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.vacuous_forall SetSort.set body)
    simpa [Expr.eval, hbody] using hMeaning
  · obtain ⟨body, hbody⟩ := formula_query 1 (values 0) (values 1)
      (hQueries (grammar false (.literal 1) (.var 0) (.var 1)) (by simp))
    obtain ⟨point, hpoint⟩ := term_query (values 0) (values 2)
      (hQueries (grammar true (.literal 0) (.var 0) (.var 2)) (by simp))
    have hResult3 := instantiate_query body point (values 3) (by
      rw [hbody, hpoint]
      exact hQueries (transform 2 (.var 2) (.var 1) (.var 3)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.exists_introduction SetSort.set body point)
    simpa [Expr.eval, hbody, hpoint, hResult3] using hMeaning
  · obtain ⟨body, hbody⟩ := formula_query 0 (values 0 + 1) (values 1)
      (hQueries (grammar false (.literal 0) (.succ (.var 0)) (.var 1)) (by simp))
    obtain ⟨conclusion, hconclusion⟩ := formula_query 0 (values 0) (values 2)
      (hQueries (grammar false (.literal 0) (.var 0) (.var 2)) (by simp))
    have hResult3 := abstract_query body (values 3) (by
      rw [hbody]
      exact hQueries (transform 1 (.literal 0) (.var 1) (.var 3)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.exists_elimination SetSort.set body conclusion)
    simpa [Expr.eval, hbody, hconclusion, hResult3] using hMeaning
  · obtain ⟨left, hleft⟩ := term_query (values 0) (values 1)
      (hQueries (grammar true (.literal 0) (.var 0) (.var 1)) (by simp))
    obtain ⟨right, hright⟩ := term_query (values 0) (values 2)
      (hQueries (grammar true (.literal 0) (.var 0) (.var 2)) (by simp))
    obtain ⟨body, hbody⟩ := formula_query 1 (values 0) (values 3)
      (hQueries (grammar false (.literal 1) (.var 0) (.var 3)) (by simp))
    have hResult4 := instantiate_query body left (values 4) (by
      rw [hbody, hleft]
      exact hQueries (transform 2 (.var 1) (.var 3) (.var 4)) (by simp))
    have hResult5 := instantiate_query body right (values 5) (by
      rw [hbody, hright]
      exact hQueries (transform 2 (.var 2) (.var 3) (.var 5)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.equality_substitution SetSort.set left right body)
    simpa [Expr.eval, hleft, hright, hbody, hResult4, hResult5] using hMeaning
  · obtain ⟨point, hpoint⟩ := term_query (values 0) (values 1)
      (hQueries (grammar true (.literal 0) (.var 0) (.var 1)) (by simp))
    have hMeaning := Meaning.logical (values 0) _ (.equality_reflexivity point)
    simpa [Expr.eval, hpoint] using hMeaning

/-- 全自然数的可靠性；结论确实有当前 Hilbert 核的逻辑公理证书。 -/
theorem checked_sound (root : Nat) (h : checked root = true) : Meaning root := by
  obtain ⟨shape, hShape, values, _, rfl, hQueries⟩ := (checked_iff root).mp h
  exact rule_sound shape hShape values hQueries

end YesMetaZFC.Automation.ObjectLogicalAxiom
