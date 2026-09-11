import YesMetaZFC.Automation.HostFirstOrder.Syntax
import YesMetaZFC.Model.FirstOrder.Theory

/-!
# 索引化宿主一阶语义

宿主解释直接生成内在一阶结构；绑定环境直接由 `Fin depth` 承担。这里不再构造
raw AST 的良构、scope 或 admissibility 桥。原始搜索表示若被下游使用，只在独立的
证书编译模块中检查，不进入本语义接口。
-/

namespace YesMetaZFC
namespace Automation
namespace HostFirstOrder
namespace Semantics

universe u

open CoreSyntax
open _root_.YesMetaZFC.Logic

namespace Values

def toList {α : Type u} :
    {sorts : List CoreSort} →
      Logic.FirstOrder.Values (fun _ => α) sorts → List α
  | _, .nil => []
  | _, .cons value rest => value :: toList rest

@[simp] theorem toList_cast {α : Type u}
    {left right : List CoreSort} (h : left = right)
    (values : Logic.FirstOrder.Values (fun _ => α) left) :
    toList (h ▸ values) = toList values := by
  cases h
  rfl

end Values

@[simp] theorem arguments_eval_cast {_α : Type u}
    {M : Logic.FirstOrder.Structure SearchMaterialization.SearchSignature}
    {bound free : Logic.FirstOrder.SortContext SearchMaterialization.SearchSignature}
    (env : Logic.FirstOrder.Env M bound free)
    {left right : List CoreSort} (h : left = right)
    (arguments : Logic.FirstOrder.Arguments SearchMaterialization.SearchSignature
      bound free left) :
    Logic.FirstOrder.Arguments.eval env (h ▸ arguments) =
      h ▸ Logic.FirstOrder.Arguments.eval env arguments := by
  cases h
  rfl

@[implicit_reducible]
def model {α : Type u} (interpretation : Interpretation α) :
    Logic.FirstOrder.Structure SearchMaterialization.SearchSignature where
  Carrier := fun _ => α
  nonempty := fun _ => ⟨interpretation.default⟩
  funcInterp := fun function arguments =>
    interpretation.function function.id (Values.toList arguments)
  relInterp := fun relation arguments =>
    match relation with
    | .predicate predicate =>
        interpretation.predicate predicate.id (Values.toList arguments)
    | _ => False

def boundValue {α : Type u} :
    (depth : Nat) → (Fin depth → α) →
      {sort : CoreSort} →
        Logic.FirstOrder.Variable (ObjectContext depth) sort → α
  | 0, _, _, entry => nomatch entry
  | Nat.succ depth, bound, _, .here => bound ⟨0, Nat.zero_lt_succ depth⟩
  | Nat.succ depth, bound, _, .there previous =>
      boundValue depth (fun index => bound index.succ) previous

def env {α : Type u} (interpretation : Interpretation α)
    {depth : Nat} (bound : Fin depth → α) :
    Logic.FirstOrder.Env (model interpretation) (ObjectContext depth) [] where
  boundVal := fun entry => boundValue depth bound entry
  freeVal := fun entry => nomatch entry

@[simp] theorem boundValue_boundVariable {α : Type u} {depth : Nat}
    (bound : Fin depth → α) (index : Fin depth) :
    boundValue depth bound (boundVariable depth index) = bound index := by
  cases depth with
  | zero => exact Fin.elim0 index
  | succ depth =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simpa [boundVariable, boundValue] using!
          boundValue_boundVariable (bound := fun value => bound value.succ) tail

@[simp] theorem env_boundVariable {α : Type u}
    (interpretation : Interpretation α) {depth : Nat} (bound : Fin depth → α)
    (index : Fin depth) :
    (env interpretation bound).boundVal (boundVariable depth index) = bound index := by
  simp [env]

theorem env_pushBound_eq {α : Type u} (interpretation : Interpretation α)
    {depth : Nat} (bound : Fin depth → α) (value : α) :
    env interpretation (Formula.pushBound value bound) =
      (env interpretation bound).pushBound value := by
  apply Logic.FirstOrder.Env.ext
  · intro sort entry
    cases entry with
    | here => rfl
    | there previous =>
        simp [env, boundValue, Logic.FirstOrder.Env.pushBound]
        have hShift :
            (fun index : Fin depth => Formula.pushBound value bound index.succ) = bound := by
          funext index
          rfl
        rw [hShift]
  · intro sort entry
    cases entry

def intrinsicValues {α : Type u} (interpretation : Interpretation α)
    {depth : Nat} (bound : Fin depth → α) (terms : List (Term depth)) : List α :=
  Values.toList
    (Logic.FirstOrder.Arguments.eval (env interpretation bound)
      (Term.toIntrinsicList terms))

@[simp] theorem evalList_eq_map {α : Type u} (interpretation : Interpretation α)
    {depth : Nat} (bound : Fin depth → α) :
    ∀ terms : List (Term depth),
      Term.evalList interpretation bound terms =
        terms.map (Term.eval interpretation bound)
  | [] => by simp [Term.evalList]
  | head :: tail => by
      simp [Term.evalList, evalList_eq_map interpretation bound tail]

theorem term_eval {α : Type u} (interpretation : Interpretation α)
    {depth : Nat} (bound : Fin depth → α) (term : Term depth) :
    Logic.FirstOrder.Term.eval (env interpretation bound) term.toIntrinsic =
      Term.eval interpretation bound term := by
  induction term using Term.rec
    (motive_2 := fun terms =>
      Values.toList
          (Logic.FirstOrder.Arguments.eval (env interpretation bound)
            (Term.toIntrinsicList terms)) =
        terms.map (Term.eval interpretation bound)) with
  | bvar index =>
      simp [Term.toIntrinsic, Logic.FirstOrder.Term.eval, Term.eval, env]
  | app symbol arguments arguments_ih =>
      simp only [Term.toIntrinsic, Logic.FirstOrder.Term.eval, model, Term.eval]
      rw [evalList_eq_map]
      exact congrArg (interpretation.function symbol) arguments_ih
  | nil =>
      simp [Term.toIntrinsicList, Logic.FirstOrder.Arguments.eval, Values.toList]
  | cons head tail head_ih tail_ih =>
      simp [Term.toIntrinsicList, Logic.FirstOrder.Arguments.eval,
        Values.toList, head_ih, tail_ih]

theorem termList_eval {α : Type u} (interpretation : Interpretation α)
    {depth : Nat} (bound : Fin depth → α) :
    ∀ terms : List (Term depth),
      Values.toList
          (Logic.FirstOrder.Arguments.eval (env interpretation bound)
            (Term.toIntrinsicList terms)) =
        Term.evalList interpretation bound terms
  | [] => by simp [Term.toIntrinsicList, Logic.FirstOrder.Arguments.eval, Values.toList]
  | head :: tail => by
      simp [Term.toIntrinsicList, Logic.FirstOrder.Arguments.eval,
        Values.toList, term_eval interpretation bound head,
        termList_eval interpretation bound tail]

theorem formula_satisfies {α : Type u} (interpretation : Interpretation α)
    {depth : Nat} (formula : Formula depth) :
    ∀ bound : Fin depth → α,
      Logic.FirstOrder.Formula.satisfies (env interpretation bound)
          formula.toIntrinsic ↔
        Formula.eval interpretation bound formula := by
  induction formula using Formula.rec with
  | atom symbol arguments =>
      intro bound
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies,
        model, Formula.eval, Formula.predicateSymbol] using!
        (iff_of_eq <| congrArg (interpretation.predicate symbol)
          (termList_eval interpretation bound arguments))
  | equal left right =>
      intro bound
      simp only [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies,
        Formula.eval, term_eval interpretation bound left,
        term_eval interpretation bound right]
  | falsum =>
      intro bound
      simp [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval]
  | truth =>
      intro bound
      simp [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval]
  | neg body ih =>
      intro bound
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval] using
        not_congr (ih bound)
  | conj left right left_ih right_ih =>
      intro bound
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval] using
        and_congr (left_ih bound) (right_ih bound)
  | disj left right left_ih right_ih =>
      intro bound
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval] using
        or_congr (left_ih bound) (right_ih bound)
  | imp left right left_ih right_ih =>
      intro bound
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval] using
        imp_congr (left_ih bound) (right_ih bound)
  | iff left right left_ih right_ih =>
      intro bound
      simpa [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval] using
        iff_congr (left_ih bound) (right_ih bound)
  | forallE body ih =>
      intro bound
      simp only [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval]
      constructor
      · intro h value
        change α at value
        have hBody := h value
        rw [← env_pushBound_eq interpretation bound value] at hBody
        exact (ih (Formula.pushBound value bound)).mp hBody
      · intro h value
        change α at value
        have hBody := (ih (Formula.pushBound value bound)).mpr (h value)
        rw [env_pushBound_eq interpretation bound value] at hBody
        exact hBody
  | existsE body ih =>
      intro bound
      simp only [Formula.toIntrinsic, Logic.FirstOrder.Formula.satisfies, Formula.eval]
      constructor
      · rintro ⟨value, hValue⟩
        change α at value
        refine ⟨value, ?_⟩
        rw [← env_pushBound_eq interpretation bound value] at hValue
        exact (ih (Formula.pushBound value bound)).mp hValue
      · rintro ⟨value, hValue⟩
        change α at value
        refine ⟨value, ?_⟩
        have hBody := (ih (Formula.pushBound value bound)).mpr hValue
        rw [env_pushBound_eq interpretation bound value] at hBody
        exact hBody

def closedBound {α : Type u} : Fin 0 → α := Fin.elim0

def closedEval {α : Type u} (interpretation : Interpretation α)
    (formula : ClosedFormula) : Prop :=
  Formula.eval interpretation closedBound formula

theorem env_closed_eq {α : Type u} (interpretation : Interpretation α) :
    env interpretation closedBound =
      (Logic.FirstOrder.Env.empty :
        Logic.FirstOrder.Env (model interpretation) [] []) := by
  apply Logic.FirstOrder.Env.ext
  · intro sort entry
    cases entry
  · intro sort entry
    cases entry

theorem trueIn_iff {α : Type u} (interpretation : Interpretation α)
    (formula : ClosedFormula) :
    formula.toIntrinsic.TrueIn (model interpretation) ↔
      closedEval interpretation formula := by
  change Logic.FirstOrder.Formula.satisfies
    (Logic.FirstOrder.Env.empty (M := model interpretation)) formula.toIntrinsic ↔ _
  rw [← env_closed_eq interpretation]
  exact formula_satisfies interpretation formula closedBound

structure CheckedInput {α : Type u} (goal : Prop) where
  interpretation : Interpretation α
  facts : HostProp.Facts
  premises : List ClosedFormula
  target : ClosedFormula
  premisesAligned :
    premises.map (closedEval interpretation) = facts.propositions
  targetAligned : closedEval interpretation target = goal

namespace CheckedInput

theorem premiseHolds {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal)
    {formula : ClosedFormula} (hFormula : formula ∈ input.premises) :
    closedEval input.interpretation formula := by
  apply input.facts.holds
  rw [← input.premisesAligned]
  exact List.mem_map.mpr ⟨formula, hFormula, rfl⟩

theorem goalOfTarget {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal)
    (hTarget : closedEval input.interpretation input.target) : goal := by
  rw [← input.targetAligned]
  exact hTarget

def sourceProblem {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal) : SourcePreprocessing.Problem :=
  sourceProblemOfSyntax input.premises input.target

def searchProblem {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal) : SourcePreprocessing.DeepProblem :=
  searchProblemOfSyntax input.premises input.target

def intrinsicProblem {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal) :
    LogicSoundness.SetLevel.DeepProblem SearchMaterialization.SearchSignature := {
  premises := input.premises.map Formula.toIntrinsic
  target := input.target.toIntrinsic
}

@[simp] theorem searchProblem_compilation {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal) :
    DAGCertificate.Compile.compileProblem? input.searchProblem =
      some input.intrinsicProblem := by
  exact HostFirstOrder.searchProblem_compilation input.premises input.target

def checkedProblem {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal) :
    DAGCertificate.Compile.CheckedProblem input.searchProblem :=
  checkedProblemOfSyntax input.premises input.target

@[simp] theorem checkedProblem_problem {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal) :
    input.checkedProblem.problem = input.intrinsicProblem :=
  rfl

theorem soundOfIntrinsicAt {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
        input.intrinsicProblem.theory input.intrinsicProblem.target) : goal := by
  have hTarget :
      input.target.toIntrinsic.TrueIn (model input.interpretation) :=
    hSearch (model input.interpretation) (by
      intro sentence hSentence
      rcases List.mem_map.mp hSentence with ⟨source, hSource, rfl⟩
      exact (trueIn_iff input.interpretation source).mpr
        (input.premiseHolds hSource))
  exact input.goalOfTarget <|
    (trueIn_iff input.interpretation input.target).mp hTarget

theorem soundOfIntrinsic {α : Type u} {goal : Prop}
    (input : CheckedInput (α := α) goal)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
        input.intrinsicProblem.theory input.intrinsicProblem.target) : goal :=
  input.soundOfIntrinsicAt hSearch

end CheckedInput

end Semantics
end HostFirstOrder
end Automation
end YesMetaZFC
