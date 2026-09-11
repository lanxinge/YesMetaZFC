import YesMetaZFC.Model.Henkin.CanonicalModel
import YesMetaZFC.Logic.FirstOrder.FormulaComplexity
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-!
# 内在类型典范模型的真值引理

完成候选中的闭句成员关系与典范模型满足关系等价。原实现中的 admissibility、
sortInterp、dummy 点和 open/close 证书已经全部消失；量词分支仅对闭项实例按公式
复杂度递归。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
namespace CanonicalModel

open HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
variable {T : Theory (HSignature σ)} {background : Background T}

omit [DecidableEq σ.SortSymbol] in
/-- 关系原子的满足关系由参数逐项等词合同直接还原为候选成员关系。 -/
private theorem rel_truth (result : Result background)
    (relation : (HSignature σ).RelSymbol)
    (arguments : Arguments (HSignature σ) [] []
      ((HSignature σ).relDomain relation)) :
    Formula.satisfies (canonical_env result) (.rel relation arguments) ↔
      result.candidate (.rel relation arguments) := by
  have hArguments := eval_arguments_equivalent result arguments
  simpa [Formula.satisfies, model, relInterp] using
    rel_mem_congr_iff result relation hArguments

omit [DecidableEq σ.SortSymbol] in
/-- 等词原子的语义相等恰好是闭项商中的候选等价。 -/
private theorem equal_truth (result : Result background)
    {sort : σ.SortSymbol}
    (left right : OpenTerm (HSignature σ) [] sort) :
    Formula.satisfies (canonical_env result) (.equal left right) ↔
      result.candidate (.equal left right) := by
  simp only [Formula.satisfies]
  rw [eval_eq_classOf result left, eval_eq_classOf result right]
  constructor
  · exact Quotient.exact
  · intro hEquality
    apply Quotient.sound
    exact hEquality

omit [DecidableEq σ.SortSymbol] in
/-- 典范模型满足一个闭句，当且仅当该闭句属于完成候选。 -/
theorem truth_lemma (result : Result background)
    (formula : Sentence (HSignature σ)) :
    Formula.satisfies (canonical_env result) formula ↔
      result.candidate formula := by
  cases formula with
  | falsum =>
      simp [Formula.satisfies, result.not_contains_falsum]
  | truth =>
      simp [Formula.satisfies, result.contains_truth]
  | rel relation arguments =>
      exact rel_truth result relation arguments
  | equal left right =>
      exact equal_truth result left right
  | neg body =>
      exact
        (not_congr (truth_lemma result body)).trans
          result.neg_mem_iff.symm
  | conj left right =>
      exact
        (and_congr (truth_lemma result left)
          (truth_lemma result right)).trans
          result.conj_mem_iff.symm
  | disj left right =>
      exact
        (or_congr (truth_lemma result left)
          (truth_lemma result right)).trans
          result.disj_mem_iff.symm
  | imp left right =>
      exact
        (imp_congr (truth_lemma result left)
          (truth_lemma result right)).trans
          result.imp_mem_iff.symm
  | iff left right =>
      exact
        (iff_congr (truth_lemma result left)
          (truth_lemma result right)).trans
          result.iff_mem_iff.symm
  | forallE sort body =>
      constructor
      · intro hSatisfies
        apply result.forall_mem_iff.mpr
        intro term
        apply (truth_lemma result (body.instantiateTop term)).mp
        apply (Formula.satisfies_instantiateTop
          (canonical_env result) term body).mpr
        exact hSatisfies (Term.eval (canonical_env result) term)
      · intro hForall value
        let term : OpenTerm (HSignature σ) [] sort :=
          representative result value
        have hCandidate :
            result.candidate (body.instantiateTop term) :=
          result.forall_mem_iff.mp hForall term
        have hInstance :
            Formula.satisfies (canonical_env result)
              (body.instantiateTop term) :=
          (truth_lemma result (body.instantiateTop term)).mpr hCandidate
        have hBody :
            Formula.satisfies
              ((canonical_env result).pushBound
                (Term.eval (canonical_env result) term)) body :=
          (Formula.satisfies_instantiateTop
            (canonical_env result) term body).mp hInstance
        have hEval :
            Term.eval (canonical_env result) term = value :=
          (eval_eq_classOf result term).trans
            (classOf_representative result value)
        rw [hEval] at hBody
        exact hBody
  | existsE sort body =>
      constructor
      · rintro ⟨value, hBody⟩
        let term : OpenTerm (HSignature σ) [] sort :=
          representative result value
        have hEval :
            Term.eval (canonical_env result) term = value :=
          (eval_eq_classOf result term).trans
            (classOf_representative result value)
        have hInstance :
            Formula.satisfies (canonical_env result)
              (body.instantiateTop term) := by
          apply (Formula.satisfies_instantiateTop
            (canonical_env result) term body).mpr
          rw [hEval]
          exact hBody
        apply result.exists_mem_iff.mpr
        exact
          ⟨term,
            (truth_lemma result (body.instantiateTop term)).mp hInstance⟩
      · intro hExists
        rcases result.exists_mem_iff.mp hExists with
          ⟨term, hCandidate⟩
        have hInstance :
            Formula.satisfies (canonical_env result)
              (body.instantiateTop term) :=
          (truth_lemma result (body.instantiateTop term)).mpr hCandidate
        exact
          ⟨Term.eval (canonical_env result) term,
            (Formula.satisfies_instantiateTop
              (canonical_env result) term body).mp hInstance⟩
termination_by Formula.complexity formula
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
      | omega

end CanonicalModel
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
