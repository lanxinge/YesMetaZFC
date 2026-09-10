import YesMetaZFC.Automation.ObjectDiagonalSyntax
import YesMetaZFC.Automation.ObjectRelationBinder

/-! # 当前 quotation 的具体自代入对象关系

两层最小输出依次确定数码项和保留尾部参数的首槽自由代入结果。唯一性覆盖任意对象见证，
只使用码域切分和标准候选输出的正负推导。
-/
namespace YesMetaZFC.Automation.ObjectDiagonal
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 4096
variable {parameters : SetContext}

abbrev minimumNumeral (D : Delta0CodeDomain) := ObjectMinimumRelation.template D numeral
abbrev minimumSubstitution (D : Delta0CodeDomain) {parameters : SetContext} :=
  ObjectMinimumRelation.template D (substitution (parameters := parameters))

private theorem domain_open {T : SetTheory} (S : Support T) {free : SetContext}
    {Γ : Context signature free} (number : Nat) :
    Derives T Γ (S.core.code_domain.condition (numₘ(number))) := by
  simpa only [Formula.substituteFree, Formula.substitute, Substitution.free_map,
    FormulaTemplate.apply_one_substituteMapped, finite_numeral_term_substituteMapped]
    using ObjectLeastWitness.closed (free := free) (Γ := Γ) (S.numeral_domain number)

theorem minimum_numeral_positive {T : SetTheory} (S : Support T) {free : SetContext}
    {Γ : Context signature free} (number : Nat) :
    Derives T Γ (minimumNumeral S.core.code_domain (numₘ(number)) (numₘ(0)) (numₘ(ObjectNumeralSyntax.value number))) := by
  apply ObjectMinimumRelation.positive S.core numeral _ _ _ (domain_open S _)
    (ObjectRelationBinder.closed_three numeral _ _ _ (numeral_positive S number))
  intro index hIndex
  exact ObjectRelationBinder.closed_three_negative numeral _ _ _
    (numeral_negative S number index (Nat.ne_of_gt hIndex))

theorem minimum_numeral_unique {T : SetTheory} (S : Support T) {free : SetContext}
    {Γ : Context signature free} (number : Nat) (point : SetOpenTerm free)
    (h : Derives T Γ (minimumNumeral S.core.code_domain (numₘ(number)) (numₘ(0)) point)) :
    Derives T Γ (point ≐ₘ numₘ(ObjectNumeralSyntax.value number)) := by
  apply ObjectMinimumRelation.unique S.core numeral _ _ point _ h
    (ObjectRelationBinder.closed_three numeral _ _ _ (numeral_positive S number))
  intro index _ hNe
  exact ObjectRelationBinder.closed_three_negative numeral _ _ _
    (numeral_negative S number index (Ne.symm hNe))

theorem minimum_substitution_positive {T : SetTheory} (S : Support T) {free : SetContext}
    {Γ : Context signature free} (body : ParameterFormula_m parameters) (number : Nat) :
    Derives T Γ (minimumSubstitution S.core.code_domain (parameters := parameters) (numₘ(code body))
      (numₘ(ObjectNumeralSyntax.value number)) (numₘ(value body number))) := by
  apply ObjectMinimumRelation.positive S.core (substitution (parameters := parameters)) _ _ _ (domain_open S _)
    (ObjectRelationBinder.closed_three (substitution (parameters := parameters)) _ _ _ (substitution_positive S body number))
  intro index hIndex
  exact ObjectRelationBinder.closed_three_negative (substitution (parameters := parameters)) _ _ _
    (substitution_negative S body number index (Nat.ne_of_gt hIndex))

theorem minimum_substitution_unique {T : SetTheory} (S : Support T) {free : SetContext}
    {Γ : Context signature free} (body : ParameterFormula_m parameters) (number : Nat) (point : SetOpenTerm free)
    (h : Derives T Γ (minimumSubstitution S.core.code_domain (parameters := parameters) (numₘ(code body))
      (numₘ(ObjectNumeralSyntax.value number)) point)) :
    Derives T Γ (point ≐ₘ numₘ(value body number)) := by
  apply ObjectMinimumRelation.unique S.core (substitution (parameters := parameters)) _ _ point _ h
    (ObjectRelationBinder.closed_three (substitution (parameters := parameters)) _ _ _ (substitution_positive S body number))
  intro index _ hNe
  exact ObjectRelationBinder.closed_three_negative (substitution (parameters := parameters)) _ _ _
    (substitution_negative S body number index (Ne.symm hNe))

def relationBody (D : Delta0CodeDomain) {parameters : SetContext} {bound free : SetContext}
    (input output : SetTerm bound free) : SetFormula (SetSort.set :: bound) free :=
  minimumNumeral D (input.weakenBound SetSort.set) (numₘ(0)) (.bvar .here) ∧ₘ
    minimumSubstitution D (parameters := parameters) (input.weakenBound SetSort.set) (.bvar .here) (output.weakenBound SetSort.set)

def condition (D : Delta0CodeDomain) {parameters : SetContext} {bound free : SetContext}
    (input output : SetTerm bound free) : SetFormula bound free :=
  .existsE SetSort.set (relationBody D (parameters := parameters) input output)

@[simp] theorem condition_substituteMapped (D : Delta0CodeDomain) {sb sf tb tf : SetContext}
    (input output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (condition D (parameters := parameters) input output).substituteMapped bs fs =
      condition D (parameters := parameters) (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp only [condition, relationBody, Formula.substituteMapped,
    FormulaTemplate.apply_three_substituteMapped, Term.substituteMapped_weakenBound,
    finite_numeral_term_substituteMapped, Term.substituteMapped, VariableSubstitution.liftBound]

def relation (D : Delta0CodeDomain) {parameters : SetContext} : FormulaTemplate.Binary where
  body := condition D (parameters := parameters) (.fvar .here) (.fvar (.there .here))

@[simp] theorem relation_apply (D : Delta0CodeDomain) {bound free : SetContext}
    (input output : SetTerm bound free) : relation D (parameters := parameters) input output = condition D (parameters := parameters) input output := by
  simp [relation, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

@[simp] theorem relationBody_at (D : Delta0CodeDomain) {free : SetContext}
    (input output point : SetOpenTerm free) :
    (relationBody D (parameters := parameters) input output).instantiateTop point =
      (minimumNumeral D input (numₘ(0)) point ∧ₘ minimumSubstitution D (parameters := parameters) input point output) := by
  simp only [relationBody, Formula.instantiateTop_conj,
    FormulaTemplate.apply_three_instantiateTop_arguments, Term.instantiateTop_weakenBound,
    ObjectRelationBinder.numeral_at]
  rfl

@[simp] theorem relationBody_open (D : Delta0CodeDomain) {free : SetContext}
    (input output : SetOpenTerm free) :
    Formula.openBoundTop (σ := signature) SetSort.set (relationBody D (parameters := parameters) input output) =
      (minimumNumeral D (input.weakenFree SetSort.set) (numₘ(0)) (.fvar .here) ∧ₘ
        minimumSubstitution D (parameters := parameters) (input.weakenFree SetSort.set) (.fvar .here) (output.weakenFree SetSort.set)) := by
  simp only [relationBody, Formula.openBoundTop_eq_instantiateTop_weakenFree,
    Formula.weakenFree_conj, ObjectRelationBinder.weaken_three,
    finite_numeral_term_weakenFree, Term.weakenFree_bvar,
    ← Term.weakenFree_weakenBound SetSort.set SetSort.set input,
    ← Term.weakenFree_weakenBound SetSort.set SetSort.set output,
    Formula.instantiateTop_conj, FormulaTemplate.apply_three_instantiateTop_arguments,
    ObjectRelationBinder.numeral_at, Term.instantiateTop_weakenBound]
  rfl

theorem positive {T : SetTheory} (S : Support T) {free : SetContext}
    {Γ : Context signature free} (body : ParameterFormula_m parameters) :
    Derives T Γ (relation S.core.code_domain (parameters := parameters) (numₘ(code body)) (numₘ(value body (code body)))) := by
  rw [relation_apply, condition]
  apply FirstOrder.Derives.exists_intro (numₘ(ObjectNumeralSyntax.value (code body)))
  rw [relationBody_at]
  exact FirstOrder.Derives.conj_intro (minimum_numeral_positive S _)
    (minimum_substitution_positive S body _)

theorem unique {T : SetTheory} (S : Support T) {free : SetContext}
    {Γ : Context signature free} (body : ParameterFormula_m parameters) (point : SetOpenTerm free)
    (h : Derives T Γ (relation S.core.code_domain (parameters := parameters) (numₘ(code body)) point)) :
    Derives T Γ (point ≐ₘ numₘ(value body (code body))) := by
  rw [relation_apply, condition] at h
  apply ObjectRelationBinder.eliminate _ h
  rw [relationBody_open]
  simp only [finite_numeral_term_weakenFree, Formula.weakenFree_equal]
  let opened : SetOpenFormula (SetSort.set :: free) :=
    minimumNumeral S.core.code_domain (numₘ(code body)) (numₘ(0)) (.fvar .here) ∧ₘ
      minimumSubstitution S.core.code_domain (parameters := parameters) (numₘ(code body)) (.fvar .here) (point.weakenFree SetSort.set)
  have hBoth : Derives T (opened :: FreshVariable.extendContext SetSort.set Γ) opened :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hTerm := minimum_numeral_unique S (code body) (.fvar .here)
    (FirstOrder.Derives.conj_elim_left hBoth)
  have hSub := FirstOrder.Derives.conj_elim_right hBoth
  have hSub' := FirstOrder.Derives.eq_subst
    (body := minimumSubstitution S.core.code_domain (parameters := parameters) (numₘ(code body)) (.bvar .here)
      ((point.weakenFree SetSort.set).weakenBound SetSort.set)) hTerm
  simp only [FormulaTemplate.apply_three_instantiateTop_arguments,
    ObjectRelationBinder.numeral_at,
    Term.instantiateTop_weakenBound] at hSub'
  exact minimum_substitution_unique S body (code body) (point.weakenFree SetSort.set) (hSub' hSub)

end YesMetaZFC.Automation.ObjectDiagonal
