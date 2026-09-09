import YesMetaZFC.Automation.ObjectLogicalAxiom

/-! # 当前 Hilbert 公理证书的局部接受完备性 -/
namespace YesMetaZFC.Automation.ObjectLogicalAxiom
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn
set_option autoImplicit false

private theorem formula_accept {bound free : SetContext} (input : SetFormula bound free) :
    queryChecked false (nodeValue 4 [bound.length, free.length, treeValue (SyntaxEncode.formula input)]) = true :=
  ObjectFormulaSyntax.checked_encode input
private theorem term_accept {free : SetContext} (input : SetOpenTerm free) :
    queryChecked false (nodeValue 0 [0, free.length, treeValue (SyntaxEncode.term input)]) = true :=
  (ObjectFormulaSyntax.checked_term_iff [] free _).mpr ⟨input, rfl⟩
private theorem abstract_accept {free : SetContext} (input : SetOpenFormula (SetSort.set :: free)) :
    queryChecked true (nodeValue 3 [1, 0, 0, treeValue (SyntaxEncode.formula input), treeValue (SyntaxEncode.formula input.abstractFreeTop)]) = true :=
  (ObjectSyntaxTransform.checked_abstractTop input _).mpr rfl
private theorem instantiate_accept {free : SetContext} (input : SetFormula [SetSort.set] free) (point : SetOpenTerm free) :
    queryChecked true (nodeValue 3 [2, 0, treeValue (SyntaxEncode.term point), treeValue (SyntaxEncode.formula input),
      treeValue (SyntaxEncode.formula (input.instantiateTop point))]) = true :=
  (ObjectSyntaxTransform.checked_instantiateTop input point _).mpr rfl

theorem accept_shape (shape : Shape) (hShape : shape ∈ shapes) (values : Fin shape.arity → Nat)
    (hQueries : ∀ query, query ∈ shape.queries → queryChecked query.1 (query.2.eval values) = true) :
    checked (shape.head.eval values) = true :=
  (checked_iff _).mpr ⟨shape, hShape, values,
    (fun i => shape.head.variable_le values (head_variables shape hShape i)), rfl, hQueries⟩

/-- 命题公理的参数列统一满足完整公式语法查询。 -/
private def formulaValues {free : SetContext} {count : Nat}
    (formulas : Fin count → SetOpenFormula free) : Fin (count + 1) → Nat :=
  Fin.cases free.length (fun i => treeValue (SyntaxEncode.formula (formulas i)))

private theorem formula_queries_accept {free : SetContext} {count : Nat}
    (formulas : Fin count → SetOpenFormula free) :
    ∀ query, query ∈ (List.finRange count).map
        (fun i => grammar false (.literal 0) (.var 0) (.var i.succ)) →
      queryChecked query.1 (query.2.eval (formulaValues formulas)) = true := by
  intro query hQuery
  rcases List.mem_map.mp hQuery with ⟨i, _, rfl⟩
  exact formula_accept (formulas i)

attribute [local simp] LogicalAxiomEncode.encode SyntaxEncode.formula Formula.forallFreeTop
  Formula.existsFreeTop SyntaxCodeRenaming.vacuous_body head node imp neg conj disj iffE allE exE eqE leaf

set_option maxHeartbeats 1000000 in
theorem checked_encode {free : SetContext} {formula : SetOpenFormula free}
    (certificate : HilbertBaseAxiom signature formula) :
    checked (nodeValue 0 [free.length, treeValue (LogicalAxiomEncode.encode certificate), treeValue (SyntaxEncode.formula formula)]) = true := by
  cases certificate with
  | implication_distribution a1 a2 a3 =>
    have h := accept_shape rule0 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 3 => [a1, a2, a3][i]))
    exact h
  | self_implication a1 =>
    have h := accept_shape rule1 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 1 => [a1][i]))
    exact h
  | weakening a1 a2 =>
    have h := accept_shape rule2 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | contradiction a1 a2 =>
    have h := accept_shape rule3 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | classical a1 =>
    have h := accept_shape rule4 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 1 => [a1][i]))
    exact h
  | explosion a1 a2 =>
    have h := accept_shape rule5 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | case_analysis a1 a2 =>
    have h := accept_shape rule6 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | truth_intro  =>
    have h := accept_shape rule7 (by simp [shapes]) _
      (formula_queries_accept (free := free) (fun i : Fin 0 => Fin.elim0 i))
    exact h
  | falsum_elimination a1 =>
    have h := accept_shape rule8 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 1 => [a1][i]))
    exact h
  | negation_intro a1 =>
    have h := accept_shape rule9 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 1 => [a1][i]))
    exact h
  | negation_elimination a1 =>
    have h := accept_shape rule10 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 1 => [a1][i]))
    exact h
  | conjunction_intro a1 a2 =>
    have h := accept_shape rule11 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | conjunction_elim_left a1 a2 =>
    have h := accept_shape rule12 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | conjunction_elim_right a1 a2 =>
    have h := accept_shape rule13 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | disjunction_intro_left a1 a2 =>
    have h := accept_shape rule14 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | disjunction_intro_right a1 a2 =>
    have h := accept_shape rule15 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | disjunction_elimination a1 a2 a3 =>
    have h := accept_shape rule16 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 3 => [a1, a2, a3][i]))
    exact h
  | biconditional_intro a1 a2 =>
    have h := accept_shape rule17 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | biconditional_elim_left a1 a2 =>
    have h := accept_shape rule18 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | biconditional_elim_right a1 a2 =>
    have h := accept_shape rule19 (by simp [shapes]) _
      (formula_queries_accept (fun i : Fin 2 => [a1, a2][i]))
    exact h
  | forall_specialization sort body point =>
    cases ‹SetSort›
    have h := accept_shape rule20 (by simp [shapes])
      (fun i : Fin 4 => [free.length, treeValue (SyntaxEncode.formula body), treeValue (SyntaxEncode.term point), treeValue (SyntaxEncode.formula (body.instantiateTop point))][i])
      (by
        intro query hQuery
        dsimp only [rule20] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl
        · exact formula_accept body
        · exact term_accept point
        · exact instantiate_accept body point)
    exact h
  | forall_distribution sort a b =>
    cases ‹SetSort›
    have h := accept_shape rule21 (by simp [shapes])
      (fun i : Fin 5 => [free.length, treeValue (SyntaxEncode.formula a), treeValue (SyntaxEncode.formula b), treeValue (SyntaxEncode.formula a.abstractFreeTop), treeValue (SyntaxEncode.formula b.abstractFreeTop)][i])
      (by
        intro query hQuery
        dsimp only [rule21] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl | rfl
        · exact formula_accept a
        · exact formula_accept b
        · exact abstract_accept a
        · exact abstract_accept b)
    exact h
  | vacuous_forall sort body =>
    cases ‹SetSort›
    have h := accept_shape rule22 (by simp [shapes])
      (fun i : Fin 2 => [free.length, treeValue (SyntaxEncode.formula body)][i])
      (by
        intro query hQuery
        dsimp only [rule22] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        obtain rfl := hQuery
        exact formula_accept body)
    simpa [rule22, Expr.eval] using h
  | exists_introduction sort body point =>
    cases ‹SetSort›
    have h := accept_shape rule23 (by simp [shapes])
      (fun i : Fin 4 => [free.length, treeValue (SyntaxEncode.formula body), treeValue (SyntaxEncode.term point), treeValue (SyntaxEncode.formula (body.instantiateTop point))][i])
      (by
        intro query hQuery
        dsimp only [rule23] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl
        · exact formula_accept body
        · exact term_accept point
        · exact instantiate_accept body point)
    exact h
  | exists_elimination sort body conclusion =>
    cases ‹SetSort›
    have h := accept_shape rule24 (by simp [shapes])
      (fun i : Fin 4 => [free.length, treeValue (SyntaxEncode.formula body), treeValue (SyntaxEncode.formula conclusion), treeValue (SyntaxEncode.formula body.abstractFreeTop)][i])
      (by
        intro query hQuery
        dsimp only [rule24] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl
        · exact formula_accept body
        · exact formula_accept conclusion
        · exact abstract_accept body)
    change checked (nodeValue 0 [free.length,
      nodeValue 24 [treeValue (SyntaxEncode.formula body), treeValue (SyntaxEncode.formula conclusion)] ,
      nodeValue 7 [nodeValue 9 [nodeValue 7 [treeValue (SyntaxEncode.formula body.abstractFreeTop), treeValue (SyntaxEncode.formula conclusion)]] ,
        nodeValue 7 [nodeValue 10 [treeValue (SyntaxEncode.formula body.abstractFreeTop)] , treeValue (SyntaxEncode.formula conclusion)]]]) = true at h
    simpa using h
  | equality_substitution sort left right body =>
    cases ‹SetSort›
    have h := accept_shape rule25 (by simp [shapes])
      (fun i : Fin 6 => [free.length, treeValue (SyntaxEncode.term left), treeValue (SyntaxEncode.term right), treeValue (SyntaxEncode.formula body), treeValue (SyntaxEncode.formula (body.instantiateTop left)), treeValue (SyntaxEncode.formula (body.instantiateTop right))][i])
      (by
        intro query hQuery
        dsimp only [rule25] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        rcases hQuery with rfl | rfl | rfl | rfl | rfl
        · exact term_accept left
        · exact term_accept right
        · exact formula_accept body
        · exact instantiate_accept body left
        · exact instantiate_accept body right)
    exact h
  | equality_reflexivity point =>
    cases ‹SetSort›
    have h := accept_shape rule26 (by simp [shapes])
      (fun i : Fin 2 => [free.length, treeValue (SyntaxEncode.term point)][i])
      (by
        intro query hQuery
        dsimp only [rule26] at query hQuery ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hQuery
        obtain rfl := hQuery
        exact term_accept point)
    exact h

end YesMetaZFC.Automation.ObjectLogicalAxiom
