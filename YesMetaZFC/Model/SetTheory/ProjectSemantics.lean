import YesMetaZFC.SetTheory.Definitional.Project.Derivation
import YesMetaZFC.Model.FirstOrder.Theory

/-! # Project 公式与类型化纯集合论核的语义桥

同一对象域和隶属关系上的两套公式语义逐构造对应。外延等同原子翻译成逻辑等号时，
显式使用模型外延性；不假定模型标准、传递或外部良基。
-/
namespace YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
open Logic.FirstOrder
set_option autoImplicit false
universe x

abbrev Carrier (ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ) := ℳ.Carrier SetSort.set

/-- 类型化纯语言模型的隶属结构。 -/
def reduct (ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ) : SetTheory.Structure.{x} where
  Domain := Carrier ℳ
  nonempty := ℳ.nonempty SetSort.set
  mem left right := ℳ.relInterp RelationSymbol.membership (.cons left (.cons right .nil))

attribute [local implicit_reducible] reduct

def projectEnv {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ} {depth : Nat}
    (env : Logic.FirstOrder.Env ℳ (fo_bound_context depth) [])
    (free : FreeVarId → Carrier ℳ) : SetTheory.Env (reduct ℳ) depth where
  bound entry := env.boundVal (fo_bound_variable entry)
  free := free

theorem projectEnv_push {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ} {depth : Nat}
    (env : Logic.FirstOrder.Env ℳ (fo_bound_context depth) [])
    (free : FreeVarId → Carrier ℳ) (value : Carrier ℳ) :
    projectEnv (env.pushBound value) free = (projectEnv env free).push value := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    refine Fin.cases ?_ (fun previous => ?_) entry <;> rfl
  · rfl

theorem term_correct {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ} {depth : Nat}
    (env : Logic.FirstOrder.Env ℳ (fo_bound_context depth) []) (free : FreeVarId → Carrier ℳ)
    (term : Project.Term depth) (hClosed : term.freeSupport = []) :
    (fo_term term hClosed).eval env = Definitional.Term.eval (projectEnv env free) term := by
  cases term with
  | bound entry => rfl
  | free id => cases hClosed

private theorem weakened_term_correct {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ} {depth : Nat}
    (env : Logic.FirstOrder.Env ℳ (fo_bound_context depth) []) (free : FreeVarId → Carrier ℳ)
    (value : Carrier ℳ) (term : Project.Term depth) (hClosed : term.freeSupport = []) :
    ((fo_term term hClosed).weakenBound SetSort.set).eval (env.pushBound value) =
      Definitional.Term.eval (projectEnv env free) term := by
  cases term with
  | bound entry => rfl
  | free id => cases hClosed

/-- 任意自由闭合正文在两套语法中的满足关系等价。 -/
theorem formula_correct {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ}
    (hExt : Extensional (reduct ℳ)) {stage depth : Nat}
    (formula : Project.Formula stage depth) (hClosed : formula.FreeClosed)
    (env : Logic.FirstOrder.Env ℳ (fo_bound_context depth) []) (free : FreeVarId → Carrier ℳ) :
    (fo_formula formula hClosed).satisfies env ↔
      Definitional.Semantics.satisfies Project.Semantics.interpretation (projectEnv env free) formula := by
  induction formula with
  | falsum => simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
  | truth => simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
  | mem left right =>
      simp only [fo_formula, fo_mem, Logic.FirstOrder.Formula.satisfies,
        Arguments.eval, term_correct env free, Definitional.Semantics.satisfies, reduct]
  | atom symbol hStage args =>
      cases symbol with
      | extensionalEq =>
          simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, term_correct env free,
            Definitional.Semantics.satisfies, Project.Semantics.interpretation]
          change (_ = _) ↔ ∀ value, (reduct ℳ).mem value _ ↔ (reduct ℳ).mem value _
          constructor
          · intro h
            change Definitional.Term.eval (projectEnv env free) (args 0) =
              Definitional.Term.eval (projectEnv env free) (args 1) at h
            change ∀ value, (reduct ℳ).mem value (Definitional.Term.eval (projectEnv env free) (args 0)) ↔
              (reduct ℳ).mem value (Definitional.Term.eval (projectEnv env free) (args 1))
            exact h ▸ (fun _ => Iff.rfl)
          · exact hExt.eq_of_same_members _ _
      | subset =>
          simp only [fo_formula, fo_mem, Logic.FirstOrder.Formula.satisfies, Arguments.eval,
            weakened_term_correct env free, Logic.FirstOrder.Term.eval,
            Definitional.Semantics.satisfies, Project.Semantics.interpretation]
          rfl
  | neg body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
      exact not_congr (ih hClosed env)
  | conj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
      exact and_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | disj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
      exact or_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | imp left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
      exact imp_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | iff left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
      exact iff_congr (ihLeft hClosed.1 env) (ihRight hClosed.2 env)
  | forallE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
      exact forall_congr' (fun value => by
        simpa only [projectEnv_push] using ih hClosed (env.pushBound value))
  | existsE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Definitional.Semantics.satisfies]
      exact exists_congr (fun value => by
        simpa only [projectEnv_push] using ih hClosed (env.pushBound value))

theorem projectEnv_empty {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ}
    (free : FreeVarId → Carrier ℳ) :
    projectEnv (Logic.FirstOrder.Env.empty (M := ℳ)) free =
      ({ bound := Fin.elim0, free := free } : SetTheory.Env (reduct ℳ) 0) := by
  dsimp only [projectEnv]
  rw [SetTheory.Env.mk.injEq]
  exact ⟨funext (fun entry => Fin.elim0 entry), rfl⟩

theorem sentence_correct {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ}
    (hExt : Extensional (reduct ℳ)) (sentence : Project.Sentence) :
    (fo_sentence sentence).TrueIn ℳ ↔ (reduct ℳ).SatisfiesSentence sentence := by
  constructor
  · intro h free
    simpa only [projectEnv_empty, Project.kernel] using
      (formula_correct hExt sentence.formula sentence.freeClosed Env.empty free).mp h
  · intro h
    obtain ⟨value⟩ := ℳ.nonempty SetSort.set
    exact (formula_correct hExt sentence.formula sentence.freeClosed Env.empty (fun _ => value)).mpr
      (by simpa only [projectEnv_empty, Project.kernel] using h (fun _ => value))

/-- 模型桥适用于任意 Project 理论；外延性在合同中显式保留。 -/
theorem models_iff {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ}
    (hExt : Extensional (reduct ℳ)) (T : Project.Theory) :
    Logic.FirstOrder.Theory.Models ℳ (fo_theory T) ↔ (reduct ℳ).Models T := by
  constructor
  · intro h
    exact ⟨hExt, fun sentence hSentence =>
      (sentence_correct hExt sentence).mp (h _ ⟨sentence, hSentence, rfl⟩)⟩
  · intro h target hTarget
    obtain ⟨sentence, hSentence, rfl⟩ := hTarget
    exact (sentence_correct hExt sentence).mpr (h.2 sentence hSentence)

end YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
