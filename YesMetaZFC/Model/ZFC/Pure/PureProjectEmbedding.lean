import YesMetaZFC.Model.ZFC.Pure.PureModel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.Project

/-! # 原 Project 公理像的纯隶属约化

比较两套实际语法嵌入；唯一额外关系原子是子集，其语义必须由源定义给出。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProjectEmbedding
open Nonlogical.BasicSetTheory QuineEncoding
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
set_option maxRecDepth 32768
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set

def reduct (𝒩 : Structure.{0,0,0,x} S) : Structure.{0,0,0,x} ℒ where
  Carrier _ := 𝒩.Carrier s
  nonempty _ := 𝒩.nonempty s
  funcInterp symbol := nomatch symbol
  relInterp symbol args := by
    cases symbol
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    exact 𝒩.relInterp .membership (.cons left (.cons right .nil))

attribute [local implicit_reducible] reduct _root_.YesMetaZFC.SetTheory.signature

def pureEnv {𝒩 : Structure.{0,0,0,x} S} {depth : Nat}
    (env : Env 𝒩 (project_bound_context depth) []) : Env (reduct 𝒩) (Project.fo_bound_context depth) [] where
  boundVal := by
    intro sort entry
    exact env.boundVal (project_bound_variable ⟨entry.index, by
      simpa [Project.fo_bound_context] using entry.index_lt_length⟩)
  freeVal := by intro sort entry; cases entry

theorem pureEnv_variable {𝒩 : Structure.{0,0,0,x} S} {depth : Nat}
    (env : Env 𝒩 (project_bound_context depth) []) (entry : Fin depth) :
    (pureEnv env).boundVal (Project.fo_bound_variable entry) = env.boundVal (project_bound_variable entry) := by
  have hIndex : (Project.fo_bound_variable entry).index = entry.val := by
    clear env
    induction depth with
    | zero => exact Fin.elim0 entry
    | succ depth ih =>
        refine Fin.cases ?_ (fun previous => ?_) entry
        · rfl
        · change (Project.fo_bound_variable previous).index + 1 = previous.val + 1
          exact congrArg (· + 1) (ih previous)
  simp only [pureEnv, hIndex]

theorem pureEnv_push {𝒩 : Structure.{0,0,0,x} S} {depth : Nat}
    (env : Env 𝒩 (project_bound_context depth) []) (value : 𝒩.Carrier s) :
    pureEnv (depth := depth + 1) (env.pushBound value) =
      (pureEnv env).pushBound (sort := PureModel.setSort) value := by
  apply Env.ext
  · intro sort entry
    cases sort
    cases entry with
    | here => rfl
    | there previous => rfl
  · intro sort entry; cases entry

theorem term_correct {𝒩 : Structure.{0,0,0,x} S} {depth : Nat}
    (term : Project.Term depth) (hClosed : term.freeSupport = [])
    (env : Env 𝒩 (project_bound_context depth) []) :
    (Project.fo_term term hClosed).eval (pureEnv env) = (project_term term hClosed).eval env := by
  cases term with
  | bound entry => exact pureEnv_variable env entry
  | free id => cases hClosed

theorem weakened_term_correct {𝒩 : Structure.{0,0,0,x} S} {depth : Nat}
    (term : Project.Term depth) (hClosed : term.freeSupport = [])
    (env : Env 𝒩 (project_bound_context depth) []) (value : 𝒩.Carrier s) :
    ((Project.fo_term term hClosed).weakenBound PureModel.setSort).eval ((pureEnv env).pushBound value) =
      (project_term term hClosed).eval env := by
  cases term with
  | bound entry => exact pureEnv_variable env entry
  | free id => cases hClosed

/-- 任意自由闭合 Project 公式在两种实际嵌入下等价。 -/
theorem formula_correct {𝒩 : Structure.{0,0,0,x} S}
    (hSubset : ∀ left right, 𝒩.relInterp .subset (.cons left (.cons right .nil)) ↔
      ∀ element, 𝒩.relInterp .membership (.cons element (.cons left .nil)) →
        𝒩.relInterp .membership (.cons element (.cons right .nil)))
    {stage depth : Nat} (formula : Project.Formula stage depth) (hClosed : formula.FreeClosed)
    (env : Env 𝒩 (project_bound_context depth) []) :
    (Project.fo_formula formula hClosed).satisfies (pureEnv env) ↔
      (project_formula formula hClosed).satisfies env := by
  induction formula with
  | falsum => simp only [Project.fo_formula, project_formula, Formula.satisfies]
  | truth => simp only [Project.fo_formula, project_formula, Formula.satisfies]
  | mem left right =>
      simp only [Project.fo_formula, Project.fo_mem, project_formula, project_mem,
        Formula.satisfies, Arguments.eval, term_correct]
      rfl
  | atom symbol hStage args =>
      cases symbol with
      | extensionalEq =>
          simp only [Project.fo_formula, project_formula, Formula.satisfies, term_correct]
      | subset =>
          simp only [Project.fo_formula, Project.fo_mem, project_formula, Formula.satisfies,
            Arguments.eval, weakened_term_correct]
          exact (hSubset _ _).symm
  | neg body ih =>
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.fo_formula, project_formula, Formula.satisfies]
      exact not_congr (ih hClosed env)
  | conj left right ihLeft ihRight =>
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.fo_formula, project_formula, Formula.satisfies]
      exact and_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | disj left right ihLeft ihRight =>
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.fo_formula, project_formula, Formula.satisfies]
      exact or_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | imp left right ihLeft ihRight =>
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.fo_formula, project_formula, Formula.satisfies]
      exact imp_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | iff left right ihLeft ihRight =>
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.fo_formula, project_formula, Formula.satisfies]
      exact iff_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | forallE body ih =>
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.fo_formula, project_formula, Formula.satisfies]
      apply forall_congr'
      intro value
      exact (pureEnv_push env value) ▸ ih hClosed (env.pushBound value)
  | existsE body ih =>
      simp only [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simp only [Project.fo_formula, project_formula, Formula.satisfies]
      apply exists_congr
      intro value
      exact (pureEnv_push env value) ▸ ih hClosed (env.pushBound value)

theorem sentence_correct {𝒩 : Structure.{0,0,0,x} S}
    (hSubset : ∀ left right, 𝒩.relInterp .subset (.cons left (.cons right .nil)) ↔
      ∀ element, 𝒩.relInterp .membership (.cons element (.cons left .nil)) →
        𝒩.relInterp .membership (.cons element (.cons right .nil)))
    (sentence : Project.Sentence) :
    (Project.fo_sentence sentence).TrueIn (reduct 𝒩) ↔ (project_sentence sentence).TrueIn 𝒩 := by
  have hEnv : pureEnv (depth := 0) (Env.empty : Env 𝒩 [] []) = (Env.empty : Env (reduct 𝒩) [] []) := by
    apply Env.ext <;> intro sort entry <;> cases entry
  change (Project.fo_formula sentence.formula sentence.freeClosed).satisfies Env.empty ↔ _
  rw [← hEnv]
  exact formula_correct hSubset sentence.formula sentence.freeClosed Env.empty

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureProjectEmbedding
