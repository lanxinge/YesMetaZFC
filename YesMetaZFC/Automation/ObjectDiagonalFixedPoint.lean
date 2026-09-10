import YesMetaZFC.Automation.ObjectDiagonalRelation

/-! # 当前类型安全内核 quotation 的具体对角固定点

句子由两层存在公式和一次实际自由代入直接构造。对象证明消费自代入关系的
存在性及任意对象输出的唯一性，最后把自然数码传输回当前结构 quotation。
-/
namespace YesMetaZFC.Automation.ObjectDiagonal
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 4096

def diagonalBody (D : Delta0CodeDomain) (P : FormulaTemplate.Unary) {bound free : SetContext}
    (input : SetTerm bound free) : SetFormula (SetSort.set :: bound) free :=
  relation D (parameters := []) (input.weakenBound SetSort.set) (.bvar .here) ∧ₘ P (.bvar .here)

def diagonalCondition (D : Delta0CodeDomain) (P : FormulaTemplate.Unary) {bound free : SetContext}
    (input : SetTerm bound free) : SetFormula bound free :=
  .existsE SetSort.set (diagonalBody D P input)

@[simp] theorem diagonalCondition_substituteMapped (D : Delta0CodeDomain) (P : FormulaTemplate.Unary)
    {sb sf tb tf : SetContext} (input : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (diagonalCondition D P input).substituteMapped bs fs =
      diagonalCondition D P (input.substituteMapped bs fs) := by
  simp [diagonalCondition, diagonalBody, Formula.substituteMapped,
    Term.substituteMapped, VariableSubstitution.liftBound]

def diagonalTemplate (D : Delta0CodeDomain) (P : FormulaTemplate.Unary) : FormulaTemplate.Unary where
  body := diagonalCondition D P (.fvar .here)

@[simp] theorem diagonalTemplate_apply (D : Delta0CodeDomain) (P : FormulaTemplate.Unary)
    {bound free : SetContext} (input : SetTerm bound free) :
    diagonalTemplate D P input = diagonalCondition D P input := by
  simp [diagonalTemplate, FormulaTemplate.apply_one, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

/-- 完全确定的实际句子；不以抽象固定点契约或选择公理代替构造。 -/
def fixedPoint (D : Delta0CodeDomain) (P : FormulaTemplate.Unary) : SetSentence :=
  instantiate (diagonalTemplate D P).body (code (diagonalTemplate D P).body)

private theorem instantiate_template (P : FormulaTemplate.Unary) (number : Nat) :
    instantiate P.body number = P (numₘ(number) : Code) := by
  unfold instantiate FormulaTemplate.apply_one FormulaTemplate.instantiate
  simp only [Formula.substituteFree, Formula.substitute, Substitution.free_map]
  congr 1
  funext sort entry
  exact nomatch entry

/-- 暴露最外层存在量词形状，避免使用者展开具体固定点的巨大 quotation。 -/
theorem fixedPoint_shape (D : Delta0CodeDomain) (P : FormulaTemplate.Unary) :
    fixedPoint D P = diagonalCondition D P (numₘ(code (diagonalTemplate D P).body)) := by
  rw [fixedPoint, instantiate_template, diagonalTemplate_apply]

private theorem diagonalBody_at (D : Delta0CodeDomain) (P : FormulaTemplate.Unary)
    {free : SetContext} (input point : SetOpenTerm free) :
    (diagonalBody D P input).instantiateTop point = (relation D (parameters := []) input point ∧ₘ P point) := by
  rw [diagonalBody, Formula.instantiateTop_conj,
    ObjectRelationBinder.second_at (relation D) input point,
    FormulaTemplate.apply_one_instantiateTop_bvar P point]

private theorem diagonalBody_open (D : Delta0CodeDomain) (P : FormulaTemplate.Unary)
    {free : SetContext} (input : SetOpenTerm free) :
    Formula.openBoundTop (σ := signature) SetSort.set (diagonalBody D P input) =
      (relation D (parameters := []) (input.weakenFree SetSort.set) (.fvar .here) ∧ₘ P (.fvar .here)) := by
  simp only [diagonalBody, Formula.openBoundTop_eq_instantiateTop_weakenFree,
    Formula.weakenFree_conj, FormulaTemplate.apply_two_weakenFree,
    FormulaTemplate.apply_one_weakenFree, Term.weakenFree_bvar,
    ← Term.weakenFree_weakenBound SetSort.set SetSort.set input,
    Formula.instantiateTop_conj]
  rw [ObjectRelationBinder.second_at (relation D) (input.weakenFree SetSort.set)
    (FreshVariable.newest (σ := signature) SetSort.set),
    FormulaTemplate.apply_one_instantiateTop_bvar P (FreshVariable.newest (σ := signature) SetSort.set)]
  rfl

private theorem fixedPoint_numeral {T : SetTheory} (S : Support T) (P : FormulaTemplate.Unary) :
    Derives T [] (fixedPoint S.core.code_domain P ↔ₘ
      P (numₘ(IntrinsicQuotation.value (fixedPoint S.core.code_domain P)))) := by
  let body := (diagonalTemplate S.core.code_domain P).body
  have hValue : IntrinsicQuotation.value (fixedPoint S.core.code_domain P) = value body (code body) := rfl
  rw [hValue]
  apply FirstOrder.Derives.iff_intro
  · have h : Derives T [fixedPoint S.core.code_domain P]
        (diagonalCondition S.core.code_domain P (numₘ(code body))) := by
      rw [← fixedPoint_shape]
      exact FirstOrder.Derives.assumption List.mem_cons_self
    change Derives T [fixedPoint S.core.code_domain P] (.existsE SetSort.set _) at h
    apply ObjectRelationBinder.eliminate _ h
    rw [diagonalBody_open]
    simp only [finite_numeral_term_weakenFree, FormulaTemplate.apply_one_weakenFree]
    let opened : SetOpenFormula [SetSort.set] :=
      relation S.core.code_domain (parameters := []) (numₘ(code body)) (.fvar .here) ∧ₘ P (.fvar .here)
    have hBoth : Derives T (opened :: FreshVariable.extendContext SetSort.set [fixedPoint S.core.code_domain P]) opened :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hEq := unique S body (.fvar .here) (FirstOrder.Derives.conj_elim_left hBoth)
    have hTransport := FirstOrder.Derives.eq_subst (body := P (.bvar .here)) hEq
    rw [FormulaTemplate.apply_one_instantiateTop_bvar,
      FormulaTemplate.apply_one_instantiateTop_bvar] at hTransport
    exact hTransport (FirstOrder.Derives.conj_elim_right hBoth)
  · rw [fixedPoint_shape, diagonalCondition]
    apply FirstOrder.Derives.exists_intro (numₘ(value body (code body)))
    rw [diagonalBody_at]
    exact FirstOrder.Derives.conj_intro (positive S body)
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 对任意固定一元对象公式，给出当前 quotation 下的具体固定点及普通推导。 -/
theorem fixedPoint_spec {T : SetTheory} (S : Support T) (P : FormulaTemplate.Unary) :
    Derives T [] (fixedPoint S.core.code_domain P ↔ₘ
      P (IntrinsicQuotation.quote (fixedPoint S.core.code_domain P))) := by
  have hFixed := fixedPoint_numeral S P
  have hQuote := IntrinsicQuotation.quote_evaluate S.certificate (fixedPoint S.core.code_domain P)
  apply FirstOrder.Derives.iff_intro
  · have hNum := FirstOrder.Derives.iff_elim_left (FirstOrder.Derives.context_weaken_cons hFixed)
      (FirstOrder.Derives.assumption List.mem_cons_self)
    have hTransport := FirstOrder.Derives.eq_subst (Γ := [fixedPoint S.core.code_domain P]) (body := P (.bvar .here))
      (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.eq_symm hQuote))
    rw [FormulaTemplate.apply_one_instantiateTop_bvar,
      FormulaTemplate.apply_one_instantiateTop_bvar] at hTransport
    exact hTransport hNum
  · have hTransport := FirstOrder.Derives.eq_subst (Γ := [P (IntrinsicQuotation.quote (fixedPoint S.core.code_domain P))]) (body := P (.bvar .here))
      (FirstOrder.Derives.context_weaken_cons hQuote)
    rw [FormulaTemplate.apply_one_instantiateTop_bvar,
      FormulaTemplate.apply_one_instantiateTop_bvar] at hTransport
    exact FirstOrder.Derives.iff_elim_right (FirstOrder.Derives.context_weaken_cons hFixed)
      (hTransport (FirstOrder.Derives.assumption List.mem_cons_self))

end YesMetaZFC.Automation.ObjectDiagonal
