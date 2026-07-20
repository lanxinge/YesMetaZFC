import YesMetaZFC.Automation.CoreNormalForm.AntiPrenex

/-!
# Anti-prenex soundness

本模块证明 dependency-driven mini-scoping 的语义等价。可信边界使用
`Nnf.usesCurrentBinder`；support 只保留为可复算审计摘要。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm

universe x

namespace Semantics

mutual
  theorem Term.eval_lowerAbove_of_not_occurs {M : Model} (env : Env M)
      (depth : Nat) (inserted : M.Carrier) (term : Term)
      (hOccurs : Term.occursBVarAt depth term = false) :
      Term.eval env (Term.lowerAbove depth term) =
        Term.eval (env.insertAt depth inserted) term := by
    cases term with
    | bvar sort index =>
        simp only [Term.occursBVarAt] at hOccurs
        by_cases hLt : index < depth
        · simp [Term.lowerAbove, Term.eval, Env.insertAt, hLt]
        · by_cases hEq : index = depth
          · subst index
            simp at hOccurs
          · simp [Term.lowerAbove, Term.eval, Env.insertAt, hLt, hEq]
    | fvar sort id =>
        simp [Term.lowerAbove, Term.eval, Env.insertAt]
    | app symbol args =>
        simp only [Term.occursBVarAt] at hOccurs
        simp only [Term.lowerAbove, Term.eval]
        congr 1
        exact Term.evalList_lowerAbove_of_not_occurs env depth inserted args hOccurs
    | apply fn arg =>
        simp only [Term.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        simp [Term.lowerAbove, Term.eval,
          Term.eval_lowerAbove_of_not_occurs env depth inserted fn hOccurs.1,
          Term.eval_lowerAbove_of_not_occurs env depth inserted arg hOccurs.2]
    | bool value =>
        simp [Term.lowerAbove, Term.eval]
    | notE body =>
        simp only [Term.occursBVarAt] at hOccurs
        simp [Term.lowerAbove, Term.eval,
          Term.eval_lowerAbove_of_not_occurs env depth inserted body hOccurs]
    | andE left right
    | orE left right
    | impE left right
    | iffE left right =>
        simp only [Term.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        simp [Term.lowerAbove, Term.eval,
          Term.eval_lowerAbove_of_not_occurs env depth inserted left hOccurs.1,
          Term.eval_lowerAbove_of_not_occurs env depth inserted right hOccurs.2]
    | quote formula =>
        simp only [Term.occursBVarAt] at hOccurs
        simp only [Term.lowerAbove, Term.eval]
        congr 1
        apply propext
        exact Formula.satisfies_lowerAbove_of_not_occurs env depth inserted formula hOccurs
    | lam domain codomain body =>
        simp only [Term.occursBVarAt] at hOccurs
        simp only [Term.lowerAbove, Term.eval]
        congr 1
        funext value
        rw [Term.eval_lowerAbove_of_not_occurs (env.push value) (depth + 1) inserted body
          hOccurs]
        apply Term.eval_eq_of_env_eq
        · exact Env.insertAt_push_bound depth env inserted value
        · intro sort id
          rfl
    | ite sort condition thenTerm elseTerm =>
        simp only [Term.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        rcases hOccurs with ⟨⟨hCondition, hThen⟩, hElse⟩
        simp only [Term.lowerAbove, Term.eval]
        congr 1
        · apply propext
          exact Formula.satisfies_lowerAbove_of_not_occurs env depth inserted condition
            hCondition
        · exact Term.eval_lowerAbove_of_not_occurs env depth inserted thenTerm hThen
        · exact Term.eval_lowerAbove_of_not_occurs env depth inserted elseTerm hElse

  theorem Formula.satisfies_lowerAbove_of_not_occurs {M : Model} (env : Env M)
      (depth : Nat) (inserted : M.Carrier) (formula : Formula)
      (hOccurs : Formula.occursBVarAt depth formula = false) :
      Formula.Satisfies env (Formula.lowerAbove depth formula) ↔
        Formula.Satisfies (env.insertAt depth inserted) formula := by
    cases formula with
    | trueE
    | falseE =>
        simp [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
    | atom predicate args =>
        simp only [Formula.occursBVarAt] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        rw [Term.evalList_lowerAbove_of_not_occurs env depth inserted args hOccurs]
    | equal sort left right =>
        simp only [Formula.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        rw [Term.eval_lowerAbove_of_not_occurs env depth inserted left hOccurs.1,
          Term.eval_lowerAbove_of_not_occurs env depth inserted right hOccurs.2]
    | boolTerm term =>
        simp only [Formula.occursBVarAt] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        rw [Term.eval_lowerAbove_of_not_occurs env depth inserted term hOccurs]
    | neg body =>
        simp only [Formula.occursBVarAt] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          not_congr
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted body hOccurs)
    | imp left right =>
        simp only [Formula.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          imp_congr
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted left hOccurs.1)
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted right hOccurs.2)
    | conj left right =>
        simp only [Formula.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          and_congr
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted left hOccurs.1)
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted right hOccurs.2)
    | disj left right =>
        simp only [Formula.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          or_congr
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted left hOccurs.1)
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted right hOccurs.2)
    | iffE left right =>
        simp only [Formula.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        simpa only [Formula.Satisfies] using
          iff_congr
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted left hOccurs.1)
            (Formula.satisfies_lowerAbove_of_not_occurs env depth inserted right hOccurs.2)
    | forallE sort body =>
        simp only [Formula.occursBVarAt] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        constructor <;> intro h value hSort
        · apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1) inserted)
              ((env.insertAt depth inserted).push value)
              (Env.insertAt_push_bound depth env inserted value)
              (by intro target id; rfl) body).mp
          exact (Formula.satisfies_lowerAbove_of_not_occurs
            (env.push value) (depth + 1) inserted body hOccurs).mp (h value hSort)
        · apply (Formula.satisfies_lowerAbove_of_not_occurs
            (env.push value) (depth + 1) inserted body hOccurs).mpr
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1) inserted)
              ((env.insertAt depth inserted).push value)
              (Env.insertAt_push_bound depth env inserted value)
              (by intro target id; rfl) body).mpr
          exact h value hSort
    | existsE sort body =>
        simp only [Formula.occursBVarAt] at hOccurs
        simp only [Formula.lowerAbove, Formula.Satisfies, Formula.eval]
        constructor
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1) inserted)
              ((env.insertAt depth inserted).push value)
              (Env.insertAt_push_bound depth env inserted value)
              (by intro target id; rfl) body).mp
          exact (Formula.satisfies_lowerAbove_of_not_occurs
            (env.push value) (depth + 1) inserted body hOccurs).mp hBody
        · rintro ⟨value, hSort, hBody⟩
          refine ⟨value, hSort, ?_⟩
          apply (Formula.satisfies_lowerAbove_of_not_occurs
            (env.push value) (depth + 1) inserted body hOccurs).mpr
          apply (Formula.satisfies_iff_of_env_eq
              ((env.push value).insertAt (depth + 1) inserted)
              ((env.insertAt depth inserted).push value)
              (Env.insertAt_push_bound depth env inserted value)
              (by intro target id; rfl) body).mpr
          exact hBody

  theorem Term.evalList_lowerAbove_of_not_occurs {M : Model} (env : Env M)
      (depth : Nat) (inserted : M.Carrier) (terms : List Term)
      (hOccurs : Term.occursBVarListAt depth terms = false) :
      (Term.lowerListAbove depth terms).map (Term.eval env) =
        terms.map (Term.eval (env.insertAt depth inserted)) := by
    cases terms with
    | nil =>
        rfl
    | cons head tail =>
        simp only [Term.occursBVarListAt, Bool.or_eq_false_iff] at hOccurs
        simp only [Term.lowerListAbove, List.map_cons]
        rw [Term.eval_lowerAbove_of_not_occurs env depth inserted head hOccurs.1,
          Term.evalList_lowerAbove_of_not_occurs env depth inserted tail hOccurs.2]
end

theorem Atom.satisfies_lowerAbove_of_not_occurs {M : Model} (env : Env M)
    (depth : Nat) (inserted : M.Carrier) (atom : Atom)
    (hOccurs : atom.occursBVarAt depth = false) :
    Atom.Satisfies env (atom.lowerAbove depth) ↔
      Atom.Satisfies (env.insertAt depth inserted) atom := by
  cases atom with
  | predicate predicate args =>
      simp only [Atom.occursBVarAt] at hOccurs
      simp only [Atom.lowerAbove, Atom.Satisfies]
      rw [Term.evalList_lowerAbove_of_not_occurs env depth inserted args hOccurs]
  | equal sort left right =>
      simp only [Atom.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
      simp only [Atom.lowerAbove, Atom.Satisfies]
      rw [Term.eval_lowerAbove_of_not_occurs env depth inserted left hOccurs.1,
        Term.eval_lowerAbove_of_not_occurs env depth inserted right hOccurs.2]
  | boolTerm term =>
      simp only [Atom.occursBVarAt] at hOccurs
      simp only [Atom.lowerAbove, Atom.Satisfies]
      rw [Term.eval_lowerAbove_of_not_occurs env depth inserted term hOccurs]

theorem Literal.satisfies_lowerAbove_of_not_occurs {M : Model} (env : Env M)
    (depth : Nat) (inserted : M.Carrier) (literal : Literal)
    (hOccurs : literal.occursBVarAt depth = false) :
    Literal.Satisfies env (literal.lowerAbove depth) ↔
      Literal.Satisfies (env.insertAt depth inserted) literal := by
  cases literal with
  | mk positive atom =>
      simp only [Literal.occursBVarAt] at hOccurs
      cases positive
      · simp only [Literal.lowerAbove, Literal.Satisfies]
        exact not_congr
          (Atom.satisfies_lowerAbove_of_not_occurs env depth inserted atom hOccurs)
      · simp only [Literal.lowerAbove, Literal.Satisfies]
        exact Atom.satisfies_lowerAbove_of_not_occurs env depth inserted atom hOccurs

theorem Nnf.satisfies_iff_of_env_eq {M : Model} (env₁ env₂ : Env M)
    (hBound : ∀ index, env₁.boundVal index = env₂.boundVal index)
    (hFree : ∀ sort id, env₁.freeVal sort id = env₂.freeVal sort id)
    (nnf : Nnf) :
    Nnf.Satisfies env₁ nnf ↔ Nnf.Satisfies env₂ nnf := by
  rw [← Nnf.satisfies_toFormula env₁ nnf, ← Nnf.satisfies_toFormula env₂ nnf]
  exact Formula.satisfies_iff_of_env_eq env₁ env₂ hBound hFree nnf.toFormula

theorem Nnf.satisfies_lowerAbove_of_not_occurs {M : Model} (env : Env M)
    (depth : Nat) (inserted : M.Carrier) (nnf : Nnf)
    (hOccurs : nnf.occursBVarAt depth = false) :
    Nnf.Satisfies env (nnf.lowerAbove depth) ↔
      Nnf.Satisfies (env.insertAt depth inserted) nnf := by
  induction nnf generalizing env depth with
  | trueE =>
      simp [Nnf.lowerAbove, Nnf.Satisfies]
  | falseE =>
      simp [Nnf.lowerAbove, Nnf.Satisfies]
  | lit literal =>
      simp only [Nnf.occursBVarAt] at hOccurs
      simp only [Nnf.lowerAbove, Nnf.Satisfies]
      exact Literal.satisfies_lowerAbove_of_not_occurs env depth inserted literal hOccurs
  | conj left right ihLeft ihRight =>
      simp only [Nnf.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
      simp only [Nnf.lowerAbove, Nnf.Satisfies]
      exact and_congr
        (ihLeft env depth hOccurs.1)
        (ihRight env depth hOccurs.2)
  | disj left right ihLeft ihRight =>
      simp only [Nnf.occursBVarAt, Bool.or_eq_false_iff] at hOccurs
      simp only [Nnf.lowerAbove, Nnf.Satisfies]
      exact or_congr
        (ihLeft env depth hOccurs.1)
        (ihRight env depth hOccurs.2)
  | forallE sort body ih =>
      simp only [Nnf.occursBVarAt] at hOccurs
      simp only [Nnf.lowerAbove, Nnf.Satisfies]
      constructor <;> intro h value hSort
      · apply (Nnf.satisfies_iff_of_env_eq
            ((env.push value).insertAt (depth + 1) inserted)
            ((env.insertAt depth inserted).push value)
            (Env.insertAt_push_bound depth env inserted value)
            (by intro target id; rfl) body).mp
        exact (ih (env.push value) (depth + 1) hOccurs).mp (h value hSort)
      · apply (ih (env.push value) (depth + 1) hOccurs).mpr
        apply (Nnf.satisfies_iff_of_env_eq
            ((env.push value).insertAt (depth + 1) inserted)
            ((env.insertAt depth inserted).push value)
            (Env.insertAt_push_bound depth env inserted value)
            (by intro target id; rfl) body).mpr
        exact h value hSort
  | existsE sort body ih =>
      simp only [Nnf.occursBVarAt] at hOccurs
      simp only [Nnf.lowerAbove, Nnf.Satisfies]
      constructor
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        apply (Nnf.satisfies_iff_of_env_eq
            ((env.push value).insertAt (depth + 1) inserted)
            ((env.insertAt depth inserted).push value)
            (Env.insertAt_push_bound depth env inserted value)
            (by intro target id; rfl) body).mp
        exact (ih (env.push value) (depth + 1) hOccurs).mp hBody
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        apply (ih (env.push value) (depth + 1) hOccurs).mpr
        apply (Nnf.satisfies_iff_of_env_eq
            ((env.push value).insertAt (depth + 1) inserted)
            ((env.insertAt depth inserted).push value)
            (Env.insertAt_push_bound depth env inserted value)
            (by intro target id; rfl) body).mpr
        exact hBody

theorem Env.insertAt_zero {M : Model} (env : Env M) (inserted : M.Carrier) :
    env.insertAt 0 inserted = env.push inserted := by
  cases env with
  | mk boundVal freeVal =>
      simp only [Env.insertAt, Env.push]
      congr 1
      funext index
      cases index <;> simp

theorem Nnf.satisfies_dropCurrentBinder_of_independent {M : Model} (env : Env M)
    (inserted : M.Carrier) (body : Nnf) (hIndependent : body.usesCurrentBinder = false) :
    Nnf.Satisfies env body.dropCurrentBinder ↔
      Nnf.Satisfies (env.push inserted) body := by
  rw [← Env.insertAt_zero env inserted]
  exact Nnf.satisfies_lowerAbove_of_not_occurs env 0 inserted body hIndependent

theorem Nnf.satisfies_forall_drop_of_independent {M : Model} (env : Env M)
    (sort : CoreSort) (body : Nnf) (hIndependent : body.usesCurrentBinder = false) :
    Nnf.Satisfies env (Nnf.forallE sort body) ↔
      Nnf.Satisfies env body.dropCurrentBinder := by
  simp only [Nnf.Satisfies]
  constructor
  · intro h
    obtain ⟨value, hSort⟩ := M.sortNonempty sort
    exact (Nnf.satisfies_dropCurrentBinder_of_independent
      env value body hIndependent).mpr (h value hSort)
  · intro h value _
    exact (Nnf.satisfies_dropCurrentBinder_of_independent
      env value body hIndependent).mp h

theorem Nnf.satisfies_exists_drop_of_independent {M : Model} (env : Env M)
    (sort : CoreSort) (body : Nnf) (hIndependent : body.usesCurrentBinder = false) :
    Nnf.Satisfies env (Nnf.existsE sort body) ↔
      Nnf.Satisfies env body.dropCurrentBinder := by
  simp only [Nnf.Satisfies]
  constructor
  · rintro ⟨value, _, hBody⟩
    exact (Nnf.satisfies_dropCurrentBinder_of_independent
      env value body hIndependent).mpr hBody
  · intro h
    obtain ⟨value, hSort⟩ := M.sortNonempty sort
    exact ⟨value, hSort, (Nnf.satisfies_dropCurrentBinder_of_independent
      env value body hIndependent).mp h⟩

theorem Nnf.Equivalent.conj_left {left left' right : Nnf}
    (h : Nnf.Equivalent.{x} left left') :
    Nnf.Equivalent.{x} (Nnf.conj left right) (Nnf.conj left' right) := by
  intro M env
  simp only [Nnf.Satisfies]
  exact and_congr (h env) Iff.rfl

theorem Nnf.Equivalent.conj_right {left right right' : Nnf}
    (h : Nnf.Equivalent.{x} right right') :
    Nnf.Equivalent.{x} (Nnf.conj left right) (Nnf.conj left right') := by
  intro M env
  simp only [Nnf.Satisfies]
  exact and_congr Iff.rfl (h env)

theorem Nnf.Equivalent.disj_left {left left' right : Nnf}
    (h : Nnf.Equivalent.{x} left left') :
    Nnf.Equivalent.{x} (Nnf.disj left right) (Nnf.disj left' right) := by
  intro M env
  simp only [Nnf.Satisfies]
  exact or_congr (h env) Iff.rfl

theorem Nnf.Equivalent.disj_right {left right right' : Nnf}
    (h : Nnf.Equivalent.{x} right right') :
    Nnf.Equivalent.{x} (Nnf.disj left right) (Nnf.disj left right') := by
  intro M env
  simp only [Nnf.Satisfies]
  exact or_congr Iff.rfl (h env)

theorem Nnf.Equivalent.forall_body {sort : CoreSort} {body body' : Nnf}
    (h : Nnf.Equivalent.{x} body body') :
    Nnf.Equivalent.{x} (Nnf.forallE sort body) (Nnf.forallE sort body') := by
  intro M env
  simp only [Nnf.Satisfies]
  constructor <;> intro hAll value hSort
  · exact (h (env.push value)).mp (hAll value hSort)
  · exact (h (env.push value)).mpr (hAll value hSort)

theorem Nnf.Equivalent.exists_body {sort : CoreSort} {body body' : Nnf}
    (h : Nnf.Equivalent.{x} body body') :
    Nnf.Equivalent.{x} (Nnf.existsE sort body) (Nnf.existsE sort body') := by
  intro M env
  simp only [Nnf.Satisfies]
  constructor
  · rintro ⟨value, hSort, hBody⟩
    exact ⟨value, hSort, (h (env.push value)).mp hBody⟩
  · rintro ⟨value, hSort, hBody⟩
    exact ⟨value, hSort, (h (env.push value)).mpr hBody⟩

theorem Nnf.Equivalent.refl (nnf : Nnf) :
    Nnf.Equivalent.{x} nnf nnf :=
  fun _ => Iff.rfl

theorem Nnf.Equivalent.trans {first second third : Nnf}
    (hFirst : Nnf.Equivalent.{x} first second)
    (hSecond : Nnf.Equivalent.{x} second third) :
    Nnf.Equivalent.{x} first third :=
  fun env => (hFirst env).trans (hSecond env)

end Semantics

namespace AntiPrenex

open Semantics

/-- 根节点的一步反前束重写保持 NNF 语义。 -/
theorem rewriteRoot?_satisfies {before : Nnf} {rewrite : Rewrite}
    (hRewrite : rewriteRoot? before = some rewrite) :
    ∀ {M : Model} (env : Env M),
      Nnf.Satisfies env before ↔ Nnf.Satisfies env rewrite.after := by
  classical
  intro M env
  cases before with
  | trueE | falseE | lit =>
      simp [rewriteRoot?] at hRewrite
  | conj | disj =>
      simp [rewriteRoot?] at hRewrite
  | forallE sort body =>
      by_cases hBody : Dependency.independentCurrentBinder body = true
      · simp [rewriteRoot?, hBody] at hRewrite
        subst rewrite
        apply Nnf.satisfies_forall_drop_of_independent
        simpa [Dependency.independentCurrentBinder] using hBody
      · cases body with
        | trueE | falseE | lit | forallE | existsE =>
            simp [rewriteRoot?, hBody] at hRewrite
        | conj left right =>
            by_cases hLeft : Dependency.independentCurrentBinder left = true
            · simp [rewriteRoot?, hBody, hLeft] at hRewrite
              subst rewrite
              have hIndependent : left.usesCurrentBinder = false := by
                simpa [Dependency.independentCurrentBinder] using hLeft
              change Nnf.Satisfies env (Nnf.forallE sort (Nnf.conj left right)) ↔
                (Nnf.Satisfies env left.dropCurrentBinder ∧
                  Nnf.Satisfies env (Nnf.forallE sort right))
              rw [← Nnf.satisfies_forall_drop_of_independent env sort left hIndependent]
              simp only [Nnf.Satisfies]
              constructor
              · intro h
                exact ⟨fun value hSort => (h value hSort).1,
                  fun value hSort => (h value hSort).2⟩
              · rintro ⟨hLeftAll, hRightAll⟩ value hSort
                exact ⟨hLeftAll value hSort, hRightAll value hSort⟩
            · by_cases hRight : Dependency.independentCurrentBinder right = true
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite
                subst rewrite
                have hIndependent : right.usesCurrentBinder = false := by
                  simpa [Dependency.independentCurrentBinder] using hRight
                change Nnf.Satisfies env (Nnf.forallE sort (Nnf.conj left right)) ↔
                  (Nnf.Satisfies env (Nnf.forallE sort left) ∧
                    Nnf.Satisfies env right.dropCurrentBinder)
                rw [← Nnf.satisfies_forall_drop_of_independent env sort right hIndependent]
                simp only [Nnf.Satisfies]
                constructor
                · intro h
                  exact ⟨fun value hSort => (h value hSort).1,
                    fun value hSort => (h value hSort).2⟩
                · rintro ⟨hLeftAll, hRightAll⟩ value hSort
                  exact ⟨hLeftAll value hSort, hRightAll value hSort⟩
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite
                subst rewrite
                simp only [Nnf.Satisfies]
                constructor
                · intro h
                  exact ⟨fun value hSort => (h value hSort).1,
                    fun value hSort => (h value hSort).2⟩
                · rintro ⟨hLeftAll, hRightAll⟩ value hSort
                  exact ⟨hLeftAll value hSort, hRightAll value hSort⟩
        | disj left right =>
            by_cases hLeft : Dependency.independentCurrentBinder left = true
            · simp [rewriteRoot?, hBody, hLeft] at hRewrite
              subst rewrite
              have hIndependent : left.usesCurrentBinder = false := by
                simpa [Dependency.independentCurrentBinder] using hLeft
              change Nnf.Satisfies env (Nnf.forallE sort (Nnf.disj left right)) ↔
                (Nnf.Satisfies env left.dropCurrentBinder ∨
                  Nnf.Satisfies env (Nnf.forallE sort right))
              simp only [Nnf.Satisfies]
              by_cases hConstant : Nnf.Satisfies env left.dropCurrentBinder
              · constructor
                · intro _
                  exact Or.inl hConstant
                · intro _ value _
                  exact Or.inl ((Nnf.satisfies_dropCurrentBinder_of_independent
                    env value left hIndependent).mp hConstant)
              · constructor
                · intro h
                  right
                  intro value hSort
                  rcases h value hSort with hValue | hRight
                  · exact False.elim (hConstant
                      ((Nnf.satisfies_dropCurrentBinder_of_independent
                        env value left hIndependent).mpr hValue))
                  · exact hRight
                · rintro (hImpossible | hRightAll)
                  · exact False.elim (hConstant hImpossible)
                  · intro value hSort
                    exact Or.inr (hRightAll value hSort)
            · by_cases hRight : Dependency.independentCurrentBinder right = true
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite
                subst rewrite
                have hIndependent : right.usesCurrentBinder = false := by
                  simpa [Dependency.independentCurrentBinder] using hRight
                change Nnf.Satisfies env (Nnf.forallE sort (Nnf.disj left right)) ↔
                  (Nnf.Satisfies env (Nnf.forallE sort left) ∨
                    Nnf.Satisfies env right.dropCurrentBinder)
                simp only [Nnf.Satisfies]
                by_cases hConstant : Nnf.Satisfies env right.dropCurrentBinder
                · constructor
                  · intro _
                    exact Or.inr hConstant
                  · intro _ value _
                    exact Or.inr ((Nnf.satisfies_dropCurrentBinder_of_independent
                      env value right hIndependent).mp hConstant)
                · constructor
                  · intro h
                    left
                    intro value hSort
                    rcases h value hSort with hLeftValue | hValue
                    · exact hLeftValue
                    · exact False.elim (hConstant
                        ((Nnf.satisfies_dropCurrentBinder_of_independent
                          env value right hIndependent).mpr hValue))
                  · rintro (hLeftAll | hImpossible)
                    · intro value hSort
                      exact Or.inl (hLeftAll value hSort)
                    · exact False.elim (hConstant hImpossible)
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite
  | existsE sort body =>
      by_cases hBody : Dependency.independentCurrentBinder body = true
      · simp [rewriteRoot?, hBody] at hRewrite
        subst rewrite
        apply Nnf.satisfies_exists_drop_of_independent
        simpa [Dependency.independentCurrentBinder] using hBody
      · cases body with
        | trueE | falseE | lit | forallE | existsE =>
            simp [rewriteRoot?, hBody] at hRewrite
        | disj left right =>
            by_cases hLeft : Dependency.independentCurrentBinder left = true
            · simp [rewriteRoot?, hBody, hLeft] at hRewrite
              subst rewrite
              have hIndependent : left.usesCurrentBinder = false := by
                simpa [Dependency.independentCurrentBinder] using hLeft
              change Nnf.Satisfies env (Nnf.existsE sort (Nnf.disj left right)) ↔
                (Nnf.Satisfies env left.dropCurrentBinder ∨
                  Nnf.Satisfies env (Nnf.existsE sort right))
              rw [← Nnf.satisfies_exists_drop_of_independent env sort left hIndependent]
              simp only [Nnf.Satisfies]
              constructor
              · rintro ⟨value, hSort, hLeftValue | hRightValue⟩
                · exact Or.inl ⟨value, hSort, hLeftValue⟩
                · exact Or.inr ⟨value, hSort, hRightValue⟩
              · rintro (⟨value, hSort, hLeftValue⟩ | ⟨value, hSort, hRightValue⟩)
                · exact ⟨value, hSort, Or.inl hLeftValue⟩
                · exact ⟨value, hSort, Or.inr hRightValue⟩
            · by_cases hRight : Dependency.independentCurrentBinder right = true
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite
                subst rewrite
                have hIndependent : right.usesCurrentBinder = false := by
                  simpa [Dependency.independentCurrentBinder] using hRight
                change Nnf.Satisfies env (Nnf.existsE sort (Nnf.disj left right)) ↔
                  (Nnf.Satisfies env (Nnf.existsE sort left) ∨
                    Nnf.Satisfies env right.dropCurrentBinder)
                rw [← Nnf.satisfies_exists_drop_of_independent env sort right hIndependent]
                simp only [Nnf.Satisfies]
                constructor
                · rintro ⟨value, hSort, hLeftValue | hRightValue⟩
                  · exact Or.inl ⟨value, hSort, hLeftValue⟩
                  · exact Or.inr ⟨value, hSort, hRightValue⟩
                · rintro (⟨value, hSort, hLeftValue⟩ | ⟨value, hSort, hRightValue⟩)
                  · exact ⟨value, hSort, Or.inl hLeftValue⟩
                  · exact ⟨value, hSort, Or.inr hRightValue⟩
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite
                subst rewrite
                simp only [Nnf.Satisfies]
                constructor
                · rintro ⟨value, hSort, hLeftValue | hRightValue⟩
                  · exact Or.inl ⟨value, hSort, hLeftValue⟩
                  · exact Or.inr ⟨value, hSort, hRightValue⟩
                · rintro (⟨value, hSort, hLeftValue⟩ | ⟨value, hSort, hRightValue⟩)
                  · exact ⟨value, hSort, Or.inl hLeftValue⟩
                  · exact ⟨value, hSort, Or.inr hRightValue⟩
        | conj left right =>
            by_cases hLeft : Dependency.independentCurrentBinder left = true
            · simp [rewriteRoot?, hBody, hLeft] at hRewrite
              subst rewrite
              have hIndependent : left.usesCurrentBinder = false := by
                simpa [Dependency.independentCurrentBinder] using hLeft
              change Nnf.Satisfies env (Nnf.existsE sort (Nnf.conj left right)) ↔
                (Nnf.Satisfies env left.dropCurrentBinder ∧
                  Nnf.Satisfies env (Nnf.existsE sort right))
              rw [← Nnf.satisfies_exists_drop_of_independent env sort left hIndependent]
              simp only [Nnf.Satisfies]
              constructor
              · rintro ⟨value, hSort, hLeftValue, hRightValue⟩
                exact ⟨⟨value, hSort, hLeftValue⟩, value, hSort, hRightValue⟩
              · rintro ⟨⟨leftValue, hLeftSort, hLeftValue⟩,
                    rightValue, hRightSort, hRightValue⟩
                exact ⟨rightValue, hRightSort,
                  (Nnf.satisfies_dropCurrentBinder_of_independent
                    env rightValue left hIndependent).mp
                    ((Nnf.satisfies_dropCurrentBinder_of_independent
                      env leftValue left hIndependent).mpr hLeftValue),
                  hRightValue⟩
            · by_cases hRight : Dependency.independentCurrentBinder right = true
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite
                subst rewrite
                have hIndependent : right.usesCurrentBinder = false := by
                  simpa [Dependency.independentCurrentBinder] using hRight
                change Nnf.Satisfies env (Nnf.existsE sort (Nnf.conj left right)) ↔
                  (Nnf.Satisfies env (Nnf.existsE sort left) ∧
                    Nnf.Satisfies env right.dropCurrentBinder)
                rw [← Nnf.satisfies_exists_drop_of_independent env sort right hIndependent]
                simp only [Nnf.Satisfies]
                constructor
                · rintro ⟨value, hSort, hLeftValue, hRightValue⟩
                  exact ⟨⟨value, hSort, hLeftValue⟩, value, hSort, hRightValue⟩
                · rintro ⟨⟨leftValue, hLeftSort, hLeftValue⟩,
                      rightValue, hRightSort, hRightValue⟩
                  exact ⟨leftValue, hLeftSort, hLeftValue,
                    (Nnf.satisfies_dropCurrentBinder_of_independent
                      env leftValue right hIndependent).mp
                      ((Nnf.satisfies_dropCurrentBinder_of_independent
                        env rightValue right hIndependent).mpr hRightValue)⟩
              · simp [rewriteRoot?, hBody, hLeft, hRight] at hRewrite

/-- 根规则的语义等价可沿 NNF 路径提升到整棵树。 -/
theorem rewriteOnceAt_satisfies {path : Path} {current : Nnf} {step : Step}
    (hStep : rewriteOnceAt path current = some step) :
    Nnf.Equivalent.{x} current step.after := by
  induction current generalizing path step with
  | trueE | falseE | lit =>
      simp [rewriteOnceAt, rewriteRoot?] at hStep
  | conj left right ihLeft ihRight =>
      rw [rewriteOnceAt] at hStep
      simp only [rewriteRoot?] at hStep
      cases hLeft : rewriteOnceAt (path ++ [PathStep.left]) left with
      | some child =>
          simp [hLeft] at hStep
          subst step
          exact Semantics.Nnf.Equivalent.conj_left (ihLeft hLeft)
      | none =>
          simp [hLeft] at hStep
          cases hRight : rewriteOnceAt (path ++ [PathStep.right]) right with
          | some child =>
              simp [hRight] at hStep
              subst step
              exact Semantics.Nnf.Equivalent.conj_right (ihRight hRight)
          | none =>
              simp [hRight] at hStep
  | disj left right ihLeft ihRight =>
      rw [rewriteOnceAt] at hStep
      simp only [rewriteRoot?] at hStep
      cases hLeft : rewriteOnceAt (path ++ [PathStep.left]) left with
      | some child =>
          simp [hLeft] at hStep
          subst step
          exact Semantics.Nnf.Equivalent.disj_left (ihLeft hLeft)
      | none =>
          simp [hLeft] at hStep
          cases hRight : rewriteOnceAt (path ++ [PathStep.right]) right with
          | some child =>
              simp [hRight] at hStep
              subst step
              exact Semantics.Nnf.Equivalent.disj_right (ihRight hRight)
          | none =>
              simp [hRight] at hStep
  | forallE sort body ih =>
      rw [rewriteOnceAt] at hStep
      cases hRoot : rewriteRoot? (Nnf.forallE sort body) with
      | some rewrite =>
          simp [hRoot] at hStep
          subst step
          exact rewriteRoot?_satisfies hRoot
      | none =>
          simp [hRoot] at hStep
          cases hBody : rewriteOnceAt (path ++ [PathStep.body]) body with
          | some child =>
              simp [hBody] at hStep
              subst step
              exact Semantics.Nnf.Equivalent.forall_body (ih hBody)
          | none =>
              simp [hBody] at hStep
  | existsE sort body ih =>
      rw [rewriteOnceAt] at hStep
      cases hRoot : rewriteRoot? (Nnf.existsE sort body) with
      | some rewrite =>
          simp [hRoot] at hStep
          subst step
          exact rewriteRoot?_satisfies hRoot
      | none =>
          simp [hRoot] at hStep
          cases hBody : rewriteOnceAt (path ++ [PathStep.body]) body with
          | some child =>
              simp [hBody] at hStep
              subst step
              exact Semantics.Nnf.Equivalent.exists_body (ih hBody)
          | none =>
              simp [hBody] at hStep

theorem rewriteOnce?_satisfies {current : Nnf} {step : Step}
    (hStep : rewriteOnce? current = some step) :
    Nnf.Equivalent.{x} current step.after :=
  rewriteOnceAt_satisfies hStep

/-- 单个 checked step 保持其 `before` 与 `after` 的语义。 -/
theorem Step.semanticEquivalent_of_check {step : Step}
    (hCheck : step.check = true) :
    Nnf.Equivalent.{x} step.before step.after := by
  unfold Step.check at hCheck
  cases hRewrite : rewriteOnce? step.before with
  | none =>
      simp [hRewrite] at hCheck
  | some expected =>
      have hEq : step = expected :=
        Step.eq_eq_true.mp (by simpa [hRewrite] using hCheck)
      subst expected
      intro M env
      exact rewriteOnce?_satisfies hRewrite env

theorem Trace.semanticEquivalent_of_replayList? {source result : Nnf}
    {steps : List Step}
    (hReplay : Trace.replayList? source steps = some result) :
    Nnf.Equivalent.{x} source result := by
  induction steps generalizing source result with
  | nil =>
      simp [Trace.replayList?] at hReplay
      subst result
      exact Semantics.Nnf.Equivalent.refl source
  | cons step rest ih =>
      simp only [Trace.replayList?] at hReplay
      by_cases hStep : SyntaxEq.nnfEq step.before source && step.check
      · simp [hStep] at hReplay
        have hParts := Bool.and_eq_true_iff.mp hStep
        have hBefore := SyntaxEq.nnfEq_eq_true.mp hParts.1
        subst source
        exact Nnf.Equivalent.trans
          (Step.semanticEquivalent_of_check hParts.2)
          (ih hReplay)
      · simp [hStep] at hReplay

/-- checked trace 的逐步语义等价由所有 checked step 顺序组合得到。 -/
theorem Trace.semanticEquivalent_of_check {source result : Nnf} {trace : Trace}
    (hCheck : Trace.check source result trace = true) :
    Nnf.Equivalent.{x} source result := by
  unfold Trace.check at hCheck
  cases hReplay : Trace.replay? source trace with
  | none =>
      simp [hReplay] at hCheck
  | some replayed =>
      have hResult : replayed = result :=
        SyntaxEq.nnfEq_eq_true.mp (by simpa [hReplay] using hCheck)
      subst result
      apply Trace.semanticEquivalent_of_replayList?
      simpa [Trace.replay?] using hReplay

theorem normalizeLoop_satisfies (remaining : Nat) (current : Nnf) (trace : Trace) :
    Nnf.Equivalent.{x} current (normalizeLoop remaining current trace).result := by
  induction remaining generalizing current trace with
  | zero =>
      exact Semantics.Nnf.Equivalent.refl current
  | succ remaining ih =>
      cases hStep : rewriteOnce? current with
      | none =>
          simp [normalizeLoop, hStep]
          exact Semantics.Nnf.Equivalent.refl current
      | some step =>
          simp [normalizeLoop, hStep]
          exact Nnf.Equivalent.trans (rewriteOnce?_satisfies hStep)
            (ih step.after (trace.push step))

theorem normalize_satisfies (config : Config) (source : Nnf) :
    Nnf.Equivalent.{x} source (normalize config source).result :=
  normalizeLoop_satisfies config.maxSteps source #[]

end AntiPrenex

namespace AntiPrenexPayload

open Semantics

theorem semanticEquivalent_of_check {payload : AntiPrenexPayload}
    (h : check payload = true) :
    Nnf.Equivalent.{x} payload.source payload.result := by
  unfold check at h
  simp only [Bool.and_eq_true_iff] at h
  exact AntiPrenex.Trace.semanticEquivalent_of_check h.2

end AntiPrenexPayload

end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
