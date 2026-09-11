import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmetic

/-!
# 对象自然数运算的有限上界

本模块保留算术编码反演所需的可选增长律扩展。它不进入自然算术核心，只提供
独立的内在类型公式与理论入口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

def natural_addition_upper_bound_instance {bound free : SetContext}
    (point left right : SetTerm bound free) : SetFormula bound free :=
  ((point ∈ₘ ωₘ) ∧ₘ
      ((left ∈ₘ ωₘ) ∧ₘ
        ((right ∈ₘ ωₘ) ∧ₘ
          ((point ∈ₘ Sₘ(left)) ∨ₘ (point ∈ₘ Sₘ(right)))))) ⟶ₘ
    (point ∈ₘ Sₘ(left +ₘ right))

def natural_addition_upper_bound_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let point : SetOpenTerm free := .fvar (.there (.there .here))
  let left : SetOpenTerm free := .fvar (.there .here)
  let right : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_addition_upper_bound_instance point left right)

def natural_positive_left_addition_strict_bound_instance
    {bound free : SetContext}
    (point left right : SetTerm bound free) : SetFormula bound free :=
  ((point ∈ₘ ωₘ) ∧ₘ
      ((left ∈ₘ ωₘ) ∧ₘ
        ((right ∈ₘ ωₘ) ∧ₘ
          ((∅ₘ ∈ₘ left) ∧ₘ (point ∈ₘ Sₘ(right)))))) ⟶ₘ
    (point ∈ₘ (left +ₘ right))

def natural_positive_left_addition_strict_bound_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let point : SetOpenTerm free := .fvar (.there (.there .here))
  let left : SetOpenTerm free := .fvar (.there .here)
  let right : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_positive_left_addition_strict_bound_instance point left right)

def natural_le_lt_transitivity_instance {bound free : SetContext}
    (point middle upper : SetTerm bound free) : SetFormula bound free :=
  ((middle ∈ₘ ωₘ) ∧ₘ
      ((upper ∈ₘ ωₘ) ∧ₘ
        ((point ∈ₘ Sₘ(middle)) ∧ₘ (middle ∈ₘ upper)))) ⟶ₘ
    (point ∈ₘ upper)

def natural_le_lt_transitivity_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set]
  let point : SetOpenTerm free := .fvar (.there (.there .here))
  let middle : SetOpenTerm free := .fvar (.there .here)
  let upper : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_le_lt_transitivity_instance point middle upper)

def natural_godel_pairing_coordinate_bound_instance {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  ((left ∈ₘ ωₘ) ∧ₘ (right ∈ₘ ωₘ)) ⟶ₘ
    ((left ∈ₘ Sₘ(godel_pairₘ(left, right))) ∧ₘ
      (right ∈ₘ Sₘ(godel_pairₘ(left, right))))

def natural_godel_pairing_coordinate_bound_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (natural_godel_pairing_coordinate_bound_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def natural_exponentiation_index_bound_instance {bound free : SetContext}
    (base index : SetTerm bound free) : SetFormula bound free :=
  ((base ∈ₘ ωₘ) ∧ₘ
      ((index ∈ₘ ωₘ) ∧ₘ (numₘ(1) ∈ₘ base))) ⟶ₘ
    (index ∈ₘ (base ^ₘ Sₘ(index)))

def natural_exponentiation_index_bound_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (natural_exponentiation_index_bound_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def natural_exponent_product_index_bound_instance {bound free : SetContext}
    (leftBase leftIndex rightBase rightIndex : SetTerm bound free) :
    SetFormula bound free :=
  ((leftBase ∈ₘ ωₘ) ∧ₘ
      ((leftIndex ∈ₘ ωₘ) ∧ₘ
        ((numₘ(1) ∈ₘ leftBase) ∧ₘ
          ((rightBase ∈ₘ ωₘ) ∧ₘ
            ((rightIndex ∈ₘ ωₘ) ∧ₘ (numₘ(1) ∈ₘ rightBase)))))) ⟶ₘ
    ((leftIndex ∈ₘ
        ((leftBase ^ₘ Sₘ(leftIndex)) *ₘ
          (rightBase ^ₘ Sₘ(rightIndex)))) ∧ₘ
      (rightIndex ∈ₘ
        ((leftBase ^ₘ Sₘ(leftIndex)) *ₘ
          (rightBase ^ₘ Sₘ(rightIndex)))))

def natural_exponent_product_index_bound_axiom : SetSentence :=
  let free := [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
  let leftBase : SetOpenTerm free := .fvar (.there (.there (.there .here)))
  let leftIndex : SetOpenTerm free := .fvar (.there (.there .here))
  let rightBase : SetOpenTerm free := .fvar (.there .here)
  let rightIndex : SetOpenTerm free := .fvar .here
  Metatheory.Formula.forall_close
    (natural_exponent_product_index_bound_instance
      leftBase leftIndex rightBase rightIndex)

def natural_exponentiation_bound_theory : SetTheory :=
  Theory.insert natural_exponentiation_index_bound_axiom
    (Theory.insert natural_exponent_product_index_bound_axiom
      godel_pairing_core_theory)

def natural_addition_bound_theory : SetTheory :=
  Theory.insert natural_addition_upper_bound_axiom
    (Theory.insert natural_positive_left_addition_strict_bound_axiom
      (Theory.insert natural_le_lt_transitivity_axiom
        (Theory.insert natural_godel_pairing_coordinate_bound_axiom
          natural_exponentiation_bound_theory)))

derive_theory_subset natural_exponentiation_theory ⊆ natural_exponentiation_bound_theory => natural_exponentiation_theory_subset_bound_theory

derive_theory_subset godel_pairing_core_theory ⊆ natural_exponentiation_bound_theory => godel_pairing_core_theory_subset_bound_theory

derive_theory_subset natural_exponentiation_bound_theory ⊆ natural_addition_bound_theory => natural_exponentiation_bound_theory_subset_addition_bound_theory

/-! ## 配数坐标严格下降合同 -/

private theorem natural_godel_pairing_coordinate_bound_axiom_derives :
    ([] : Context signature []) ⊢ₘ[natural_addition_bound_theory]
      Formula.fromSentence natural_godel_pairing_coordinate_bound_axiom :=
  FirstOrder.Derives.theory_axiom (by
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))

private theorem natural_le_lt_transitivity_axiom_derives :
    ([] : Context signature []) ⊢ₘ[natural_addition_bound_theory]
      Formula.fromSentence natural_le_lt_transitivity_axiom :=
  FirstOrder.Derives.theory_axiom (by
    exact Or.inr (Or.inr (Or.inl rfl)))

/-- 自然数的“后继内成员 + 严格成员”传递律可在开放上下文中直接实例化。 -/
theorem natural_le_lt_transitivity_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (point middle upper : SetOpenTerm free) :
    Γ ⊢ₘ[natural_addition_bound_theory]
      natural_le_lt_transitivity_instance point middle upper := by
  let body : SetOpenFormula [SetSort.set, SetSort.set, SetSort.set] :=
    natural_le_lt_transitivity_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons upper
      (VariableSubstitution.cons middle
        (VariableSubstitution.cons point VariableSubstitution.empty))
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [natural_le_lt_transitivity_axiom, body] using
        natural_le_lt_transitivity_axiom_derives)
  simpa [body, τ, natural_le_lt_transitivity_instance,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- 配数坐标界可在任意开放上下文中直接实例化。 -/
theorem natural_godel_pairing_coordinate_bound_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[natural_addition_bound_theory]
      natural_godel_pairing_coordinate_bound_instance left right := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    natural_godel_pairing_coordinate_bound_instance
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons right
      (VariableSubstitution.cons left VariableSubstitution.empty)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [natural_godel_pairing_coordinate_bound_axiom, body] using
        natural_godel_pairing_coordinate_bound_axiom_derives)
  simpa [body, τ, natural_godel_pairing_coordinate_bound_instance,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- 两个自然数坐标都严格小于带后继外壳的配数节点。 -/
theorem natural_godel_pairing_coordinates_lt_node
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeft : Γ ⊢ₘ[natural_addition_bound_theory] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[natural_addition_bound_theory] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[natural_addition_bound_theory]
      (left ∈ₘ Sₘ(godel_pairₘ(left, right))) ∧ₘ
        (right ∈ₘ Sₘ(godel_pairₘ(left, right))) :=
  FirstOrder.Derives.imp_elim
    (natural_godel_pairing_coordinate_bound_instance_derives left right)
    (FirstOrder.Derives.conj_intro hLeft hRight)

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
