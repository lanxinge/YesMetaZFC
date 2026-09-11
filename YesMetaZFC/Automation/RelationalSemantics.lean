import YesMetaZFC.Automation.RelationalEnvironment

/-! # 函数图消去的完整语义正确性

任意目标模型对全部符号定义的实现，诱导同载体的源模型。先互递归证明项图与
参数图精确表示实际值，再沿全部公式构造子证明满足关系等价。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
universe x
variable {σ τ : Signature.{0, 0, 0}}

/-- 目标模型各排序上的源符号解释。 -/
structure Expansion (I : Interpretation σ τ) (M : Structure.{0, 0, 0, x} τ) where
  function : (symbol : σ.FuncSymbol) →
    Values (fun sort => M.Carrier (I.sort sort)) (σ.funcDomain symbol) → M.Carrier (I.sort (σ.funcCodomain symbol))
  relation : (symbol : σ.RelSymbol) →
    Values (fun sort => M.Carrier (I.sort sort)) (σ.relDomain symbol) → Prop

def Expansion.model {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) : Structure.{0, 0, 0, x} σ where
  Carrier sort := M.Carrier (I.sort sort)
  nonempty sort := M.nonempty (I.sort sort)
  funcInterp := E.function
  relInterp := E.relation

/-- 固定定义图对全部对象参数准确实现源符号；这是待由具体集合论定义证明的条件。 -/
structure Realizes {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ} (E : Expansion I M) : Prop where
  function : ∀ symbol args output,
    (I.function symbol).satisfies (templateEnv (.cons output (mapValues I args))) ↔ output = E.function symbol args
  relation : ∀ symbol args,
    (I.relation symbol).satisfies (templateEnv (mapValues I args)) ↔ E.relation symbol args

def sourceEnv {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ} (E : Expansion I M)
    {sb sf : SortContext σ} {bound free : SortContext τ} (env : Env M bound free)
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free) : Env E.model sb sf where
  boundVal entry := (bs entry).eval env
  freeVal entry := (fs entry).eval env

@[simp] theorem sourceEnv_weaken {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) {sb sf : SortContext σ} {bound free sorts : SortContext τ}
    (env : Env M bound free) (values : Values M.Carrier sorts)
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free) :
    sourceEnv E (pushBlock env values) (weakenAssignment I sorts bs) (weakenAssignment I sorts fs) =
      sourceEnv E env bs fs := by
  apply Env.ext
  · intro sort entry
    exact weakenTerm_eval env values (bs entry)
  · intro sort entry
    exact weakenTerm_eval env values (fs entry)

@[simp] theorem sourceEnv_lift {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) {sb sf : SortContext σ} {bound free : SortContext τ}
    (env : Env M bound free) (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (sort : σ.SortSymbol) (value : M.Carrier (I.sort sort)) :
    sourceEnv E (env.pushBound value) (liftAssignment I sort bs) (weakenAssignment I [I.sort sort] fs) =
      (sourceEnv E env bs fs).pushBound value := by
  apply Env.ext
  · intro _ entry
    cases entry with
    | here => rfl
    | there previous => exact Term.eval_weakenBound env value (bs previous)
  · intro _ entry
    exact weakenTerm_eval env (Values.cons value .nil) (fs entry)

mutual
/-- 项图成立当且仅当输出等于源项的实际值。 -/
theorem term_correct {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) (hE : Realizes E) {sb sf : SortContext σ} {bound free : SortContext τ}
    (env : Env M bound free) (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    {sort : σ.SortSymbol} (input : Term σ sb sf sort) (output : Term τ bound free (I.sort sort)) :
    (term I bs fs input output).satisfies env ↔ output.eval env = input.eval (sourceEnv E env bs fs) := by
  cases input with
  | bvar entry => rfl
  | fvar entry => rfl
  | app symbol args =>
    rw [term, existsBlock_satisfies]
    constructor
    · rintro ⟨values, hArgs, hGraph⟩
      have hValues := (arguments_correct E hE (pushBlock env values)
        (weakenAssignment I _ bs) (weakenAssignment I _ fs) args (witnesses _)).mp hArgs
      rw [witnesses_eval, sourceEnv_weaken] at hValues
      subst values
      rw [applyTemplate_satisfies] at hGraph
      simp only [Arguments.eval, weakenTerm_eval, witnesses_eval] at hGraph
      exact (hE.function symbol _ _).mp hGraph
    · intro h
      refine ⟨mapValues I (args.eval (sourceEnv E env bs fs)), ?_, ?_⟩
      · apply (arguments_correct E hE _ _ _ args _).mpr
        rw [witnesses_eval, sourceEnv_weaken]
      · rw [applyTemplate_satisfies]
        simp only [Arguments.eval, weakenTerm_eval, witnesses_eval]
        exact (hE.function symbol _ _).mpr h

/-- 参数图成立当且仅当整列参数值精确相等。 -/
theorem arguments_correct {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) (hE : Realizes E) {sb sf : SortContext σ} {bound free : SortContext τ}
    (env : Env M bound free) (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    {sorts : SortContext σ} (input : Arguments σ sb sf sorts) (output : Arguments τ bound free (sorts.map I.sort)) :
    (arguments I bs fs input output).satisfies env ↔ output.eval env = mapValues I (input.eval (sourceEnv E env bs fs)) := by
  cases input with
  | nil => cases output; exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | cons head tail =>
    cases output with
    | cons first rest =>
      simp only [arguments, Formula.satisfies, term_correct E hE env bs fs head first,
        arguments_correct E hE env bs fs tail rest, Arguments.eval, mapValues, mapSortValues]
      constructor
      · rintro ⟨hFirst, hRest⟩
        rw [hFirst, hRest]
      · intro h
        exact Values.cons.inj h
end

/-- 完整公式翻译的满足关系等价，包含任意嵌套量词及否定。 -/
theorem formula_correct {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) (hE : Realizes E) {sb sf : SortContext σ} {bound free : SortContext τ}
    (env : Env M bound free) (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (input : Formula σ sb sf) :
    (formula I bs fs input).satisfies env ↔ input.satisfies (sourceEnv E env bs fs) := by
  induction input generalizing bound free with
  | falsum => rfl
  | truth => rfl
  | rel symbol args =>
    rw [formula, existsBlock_satisfies]
    constructor
    · rintro ⟨values, hArgs, hRelation⟩
      have hValues := (arguments_correct E hE (pushBlock env values)
        (weakenAssignment I _ bs) (weakenAssignment I _ fs) args (witnesses _)).mp hArgs
      rw [witnesses_eval, sourceEnv_weaken] at hValues
      subst values
      rw [applyTemplate_satisfies, witnesses_eval] at hRelation
      exact (hE.relation symbol _).mp hRelation
    · intro h
      refine ⟨mapValues I (args.eval (sourceEnv E env bs fs)), ?_, ?_⟩
      · apply (arguments_correct E hE _ _ _ args _).mpr
        rw [witnesses_eval, sourceEnv_weaken]
      · rw [applyTemplate_satisfies, witnesses_eval]
        exact (hE.relation symbol _).mpr h
  | equal left right =>
    rename_i sourceBound sourceFree sort
    change (∃ value, (term I _ _ left _).satisfies (env.pushBound value) ∧
      (term I _ _ right _).satisfies (env.pushBound value)) ↔ _
    have hEnv (value : M.Carrier (I.sort sort)) :=
      sourceEnv_weaken E env (Values.cons value .nil) bs fs
    simp only [term_correct E hE, Term.eval, Env.pushBound_bound_here]
    simp only [pushBlock] at hEnv
    simp only [hEnv, Formula.satisfies]
    constructor
    · rintro ⟨_, hLeft, hRight⟩
      exact hLeft.symm.trans hRight
    · intro h
      exact ⟨left.eval (sourceEnv E env bs fs), rfl, h⟩
  | neg body ih => exact not_congr (ih env bs fs)
  | conj left right ihLeft ihRight => exact and_congr (ihLeft env bs fs) (ihRight env bs fs)
  | disj left right ihLeft ihRight => exact or_congr (ihLeft env bs fs) (ihRight env bs fs)
  | imp left right ihLeft ihRight => exact imp_congr (ihLeft env bs fs) (ihRight env bs fs)
  | iff left right ihLeft ihRight => exact iff_congr (ihLeft env bs fs) (ihRight env bs fs)
  | forallE sort body ih =>
    change (∀ value, (formula I _ _ body).satisfies (env.pushBound value)) ↔ _
    simp only [ih, sourceEnv_lift, Formula.satisfies]
    rfl
  | existsE sort body ih =>
    change (∃ value, (formula I _ _ body).satisfies (env.pushBound value)) ↔ _
    simp only [ih, sourceEnv_lift, Formula.satisfies]
    rfl

/-- 闭句在扩张模型和目标模型中的真值完全一致。 -/
theorem sentence_correct {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) (hE : Realizes E) (input : Sentence σ) :
    (sentence I input).TrueIn M ↔ input.TrueIn E.model := by
  unfold Formula.TrueIn sentence
  rw [formula_correct E hE]
  apply Iff.of_eq
  congr 1
  exact Env.empty_unique _

end YesMetaZFC.Automation.RelationalTranslation
