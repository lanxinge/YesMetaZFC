import YesMetaZFC.Automation.ObjectDiagonalRelation

/-! # 保留任意有限参数的对角固定点

自代入只替换首个编码槽；参数变量留在原上下文中。抽象与重新打开均复用公共 binder 定律。
-/
namespace YesMetaZFC.Automation.ObjectParameterDiagonal
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT ObjectDiagonal
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 4096
variable {parameters : SetContext}

/-- 对开放公式取原结构 quotation，再将闭编码项放入参数上下文。 -/
def quote_m (φ : SetOpenFormula parameters) : SetOpenTerm parameters :=
  (IntrinsicQuotation.quote φ).substituteMapped VariableSubstitution.boundId VariableSubstitution.empty

def templateBody_m (D : Delta0CodeDomain) (P : ParameterFormula_m parameters) :
    ParameterFormula_m parameters :=
  .existsE SetSort.set (relation D (parameters := parameters) (.fvar .here) (.bvar .here) ∧ₘ
    P.abstractFreeTop.weakenFree SetSort.set)

def condition_m (D : Delta0CodeDomain) (P : ParameterFormula_m parameters)
    (input : SetOpenTerm parameters) : SetOpenFormula parameters :=
  .existsE SetSort.set (relation D (parameters := parameters) (input.weakenBound SetSort.set) (.bvar .here) ∧ₘ
    P.abstractFreeTop)

def fixedPoint_m (D : Delta0CodeDomain) (P : ParameterFormula_m parameters) : SetOpenFormula parameters :=
  instantiate (templateBody_m D P) (code (templateBody_m D P))

private theorem templateBody_at_m (D : Delta0CodeDomain) (P : ParameterFormula_m parameters) (number : Nat) :
    instantiate (templateBody_m D P) number = condition_m D P (numₘ(number)) := by
  rw [instantiate_eq_m]
  simp only [templateBody_m, Formula.instantiateFreeTop_existsE, Formula.instantiateFreeTop_conj,
    Formula.instantiateFreeTop_weakenFree, condition_m]
  congr 2
  simp only [Formula.instantiateFreeTop, Formula.substitute, Substitution.instantiateFreeTop,
    FormulaTemplate.apply_two_substituteMapped, Term.substituteMapped,
    VariableSubstitution.instantiateFreeTop, VariableSubstitution.boundId]

theorem fixedPoint_shape_m (D : Delta0CodeDomain) (P : ParameterFormula_m parameters) :
    fixedPoint_m D P = condition_m D P (numₘ(code (templateBody_m D P))) :=
  templateBody_at_m D P _

private theorem condition_at_m (D : Delta0CodeDomain) (P : ParameterFormula_m parameters)
    (input point : SetOpenTerm parameters) :
    (relation D (parameters := parameters) (input.weakenBound SetSort.set) (.bvar .here) ∧ₘ
      P.abstractFreeTop).instantiateTop point =
      (relation D (parameters := parameters) input point ∧ₘ P.instantiateFreeTop point) := by
  rw [Formula.instantiateTop_conj, ObjectRelationBinder.second_at, Formula.instantiateTop_abstractFreeTop]

private theorem condition_open_m (D : Delta0CodeDomain) (P : ParameterFormula_m parameters)
    (input : SetOpenTerm parameters) :
    Formula.openBoundTop (σ := signature) SetSort.set
      (relation D (parameters := parameters) (input.weakenBound SetSort.set) (.bvar .here) ∧ₘ P.abstractFreeTop) =
      (relation D (parameters := parameters) (input.weakenFree SetSort.set) (.fvar .here) ∧ₘ P) := by
  simp only [Formula.openBoundTop_eq_instantiateTop_weakenFree, Formula.weakenFree_conj,
    FormulaTemplate.apply_two_weakenFree, Term.weakenFree_bvar,
    ← Term.weakenFree_weakenBound SetSort.set SetSort.set input,
    Formula.instantiateTop_conj]
  rw [ObjectRelationBinder.second_at (relation D (parameters := parameters))
    (input.weakenFree SetSort.set) (FreshVariable.newest (σ := signature) SetSort.set)]
  congr 1
  exact Formula.instantiateTop_weakenFree_abstractFreeTop
    (σ := signature) (bound := []) (free := parameters) SetSort.set P

private theorem fixedPoint_numeral_m {T : SetTheory} (S : Support T) (P : ParameterFormula_m parameters) :
    Derives T [] (fixedPoint_m S.core.code_domain P ↔ₘ
      P.instantiateFreeTop (numₘ(IntrinsicQuotation.value (fixedPoint_m S.core.code_domain P)))) := by
  let body := templateBody_m S.core.code_domain P
  change Derives T [] (fixedPoint_m S.core.code_domain P ↔ₘ
    P.instantiateFreeTop (numₘ(value body (code body))))
  apply Derives.iff_intro
  · have h : Derives T [fixedPoint_m S.core.code_domain P]
        (condition_m S.core.code_domain P (numₘ(code body))) := by
      rw [← fixedPoint_shape_m]
      exact Derives.assumption List.mem_cons_self
    apply ObjectRelationBinder.eliminate _ h
    rw [condition_open_m]
    simp only [finite_numeral_term_weakenFree]
    have h₁ : Derives T
        ((relation S.core.code_domain (parameters := parameters) (numₘ(code body)) (.fvar .here) ∧ₘ P) ::
          FreshVariable.extendContext SetSort.set [fixedPoint_m S.core.code_domain P])
        (relation S.core.code_domain (parameters := parameters) (numₘ(code body)) (.fvar .here) ∧ₘ P) :=
      Derives.assumption List.mem_cons_self
    have h₂ := unique S body (.fvar .here) (Derives.conj_elim_left h₁)
    have h₃ := Derives.eq_subst (body := P.abstractFreeTop.weakenFree SetSort.set) h₂
    have hP : (P.abstractFreeTop.weakenFree SetSort.set).instantiateTop
        (.fvar .here) = P :=
      Formula.instantiateTop_weakenFree_abstractFreeTop
        (σ := signature) (bound := []) (free := parameters) SetSort.set P
    rw [hP] at h₃
    have h₄ := h₃ (Derives.conj_elim_right h₁)
    rw [← Formula.instantiateTop_renameMapped_abstractFreeTop_weakenFree (σ := signature)
      (introduced := SetSort.set) (numₘ(value body (code body)) : SetOpenTerm parameters) P]
    simpa only [Formula.weakenFree_eq_renameMapped, finite_numeral_term_weakenFree] using h₄
  · rw [fixedPoint_shape_m, condition_m]
    apply Derives.exists_intro (numₘ(value body (code body)))
    rw [condition_at_m]
    exact Derives.conj_intro (positive S body) (Derives.assumption List.mem_cons_self)

theorem quote_evaluate_m {T : SetTheory} (C : CertificateCore T) (φ : SetOpenFormula parameters) :
    Derives T ([] : Context signature parameters) (quote_m φ ≐ₘ numₘ(IntrinsicQuotation.value φ)) := by
  simpa only [quote_m, Formula.substituteFree, Formula.substitute, Substitution.free_map,
    Formula.substituteMapped, finite_numeral_term_substituteMapped] using
    ObjectLeastWitness.closed (free := parameters) (Γ := []) (IntrinsicQuotation.quote_evaluate C φ)

/-- 参数统一保留的实际固定点等价，不要求参数可由闭项命名。 -/
theorem fixed_point_m {T : SetTheory} (S : Support T) (P : ParameterFormula_m parameters) :
    Derives T [] (fixedPoint_m S.core.code_domain P ↔ₘ
      P.instantiateFreeTop (quote_m (fixedPoint_m S.core.code_domain P))) := by
  have h := fixedPoint_numeral_m S P
  have h₁ := quote_evaluate_m S.certificate (fixedPoint_m S.core.code_domain P)
  apply Derives.iff_intro
  · have h₂ := Derives.eq_subst (Γ := [fixedPoint_m S.core.code_domain P])
      (body := P.abstractFreeTop) (Derives.eq_symm h₁).context_weaken_cons
    simp only [Formula.instantiateTop_abstractFreeTop] at h₂
    exact h₂ (Derives.iff_elim_left h.context_weaken_cons (Derives.assumption List.mem_cons_self))
  · have h₂ := Derives.eq_subst (Γ := [P.instantiateFreeTop (quote_m (fixedPoint_m S.core.code_domain P))])
      (body := P.abstractFreeTop) h₁.context_weaken_cons
    simp only [Formula.instantiateTop_abstractFreeTop] at h₂
    exact Derives.iff_elim_right h.context_weaken_cons (h₂ (Derives.assumption List.mem_cons_self))

end YesMetaZFC.Automation.ObjectParameterDiagonal
