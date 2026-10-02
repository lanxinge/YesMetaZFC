import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteSet
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicFormulaTemplate

/-!
# 由固定局部规则定义的统一对象轨迹

轨迹是有界集合的子集；其成员既可以有重复构造来源，也可以包含与根无关的行。
正向证明构造有限闭合轨迹，负向消去接受任意对象轨迹，不要求轨迹来自宿主解析。
-/
namespace YesMetaZFC.Automation.ObjectTrace
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 局部规则的两个槽位依次为当前行和整个轨迹。 -/
def closed (step : FormulaTemplate.Binary) {bound free : SetContext}
    (trace : SetTerm bound free) : SetFormula bound free :=
  Formula.LevyBound.boundedForall set_levy_bound trace
    (step (.bvar .here) (trace.weakenBound SetSort.set))

def witnessBody (step : FormulaTemplate.Binary) {bound free : SetContext}
    (root trace : SetTerm bound free) : SetFormula bound free :=
  (root ∈ₘ trace) ∧ₘ closed step trace

/-- 一个固定模板同时约束所有输入，输入只占根行码和载体两个槽位。 -/
def condition (step : FormulaTemplate.Binary) {bound free : SetContext}
    (carrier root : SetTerm bound free) : SetFormula bound free :=
  Formula.LevyBound.boundedExists set_levy_bound (𝒫ₘ(carrier))
    (witnessBody step (root.weakenBound SetSort.set) (.bvar .here))

theorem condition_delta0 (step : FormulaTemplate.Binary)
    (hStep : Formula.IsDelta0 set_levy_bound step.body)
    {bound free : SetContext} (carrier root : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition step carrier root) :=
  Formula.IsDelta0.bounded_exists _ (Formula.IsDelta0.conj
    (Formula.IsDelta0.rel _ _) (Formula.IsDelta0.bounded_forall _
      (step.instantiate_delta0 hStep _)))

@[simp] theorem closed_substituteMapped (step : FormulaTemplate.Binary)
    {sb sf tb tf : SetContext} (trace : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (closed step trace).substituteMapped bs fs =
      closed step (trace.substituteMapped bs fs) := by
  simp [closed, Formula.LevyBound.boundedForall, set_levy_bound, Formula.LevyBound.membership,
    Formula.substituteMapped, Arguments.substituteMapped, Term.substituteMapped,
    VariableSubstitution.liftBound]

@[simp] theorem witnessBody_instantiateTop (step : FormulaTemplate.Binary)
    {free : SetContext} (root trace : SetOpenTerm free) :
    (witnessBody step (root.weakenBound SetSort.set) (.bvar .here)).instantiateTop trace =
      witnessBody step root trace := by
  simp [witnessBody, Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Formula.substituteMapped, Arguments.substituteMapped, Term.substituteMapped,
    VariableSubstitution.instantiateTop]

@[simp] theorem step_instantiateTop (step : FormulaTemplate.Binary)
    {free : SetContext} (trace row : SetOpenTerm free) :
    (step (.bvar .here) (trace.weakenBound SetSort.set)).instantiateTop row = step row trace := by
  simp [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, VariableSubstitution.instantiateTop]

theorem positive {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (step : FormulaTemplate.Binary) {free : SetContext} {Γ : Context signature free}
    (carrier root : SetOpenTerm free) (rows : List (SetOpenTerm free))
    (hRoot : root ∈ rows)
    (hBound : ∀ row, row ∈ rows → Derives T Γ (row ∈ₘ carrier))
    (hStep : ∀ row, row ∈ rows → Derives T Γ (step row (ObjectFiniteSet.term rows))) :
    Derives T Γ (condition step carrier root) := by
  apply bounded_exists_intro _ _ (ObjectFiniteSet.term rows)
    (ObjectFiniteSet.mem_powerSet S hPower rows carrier hBound)
  rw [witnessBody_instantiateTop]
  apply FirstOrder.Derives.conj_intro (ObjectFiniteSet.member_intro S hRoot)
  apply ObjectFiniteSet.forall_intro S rows
  intro row hRow
  rw [step_instantiateTop]
  exact hStep row hRow

theorem closed_elim {T : SetTheory} (step : FormulaTemplate.Binary)
    {free : SetContext} {Γ : Context signature free} (trace row : SetOpenTerm free)
    (hClosed : Derives T Γ (closed step trace)) (hMember : Derives T Γ (row ∈ₘ trace)) :
    Derives T Γ (step row trace) := by
  have h := bounded_forall_elim trace
    (step (.bvar .here) (trace.weakenBound SetSort.set)) row hClosed hMember
  rwa [step_instantiateTop] at h

@[simp] theorem witnessBody_substituteMapped (step : FormulaTemplate.Binary)
    {sb sf tb tf : SetContext} (root trace : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (witnessBody step root trace).substituteMapped bs fs =
      witnessBody step (root.substituteMapped bs fs) (trace.substituteMapped bs fs) := by
  simp [witnessBody, Formula.substituteMapped, Arguments.substituteMapped]

@[simp] theorem condition_substituteMapped (step : FormulaTemplate.Binary)
    {sb sf tb tf : SetContext} (carrier root : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition step carrier root).substituteMapped bs fs =
      condition step (carrier.substituteMapped bs fs) (root.substituteMapped bs fs) := by
  simp [condition, Formula.LevyBound.boundedExists, set_levy_bound, Formula.LevyBound.membership,
    Formula.substituteMapped, Arguments.substituteMapped, Term.substituteMapped,
    VariableSubstitution.liftBound]

@[simp] theorem witnessBody_openBoundTop (step : FormulaTemplate.Binary)
    {free : SetContext} (root : SetOpenTerm free) :
    Formula.openBoundTop (σ := signature) SetSort.set
      (witnessBody step (root.weakenBound SetSort.set) (.bvar .here)) =
      witnessBody step (root.weakenFree SetSort.set)
        (FreshVariable.newest (σ := signature) (free := free) SetSort.set) := by
  unfold Formula.openBoundTop
  rw [witnessBody_substituteMapped]
  change witnessBody step
    (Term.openBoundTop (σ := signature) SetSort.set (root.weakenBound SetSort.set))
    (FreshVariable.newest (σ := signature) (free := free) SetSort.set) = _
  rw [Term.openBoundTop_weakenBound]

/-- 只要局部闭合排除根行，就排除所有对象轨迹；不要求见证标准或已经解析。 -/
theorem negative {T : SetTheory} (step : FormulaTemplate.Binary) (carrier : SetTerm [] []) (root : Nat)
    (hRefute : ∀ (Γ : Context signature [SetSort.set]) (trace : SetOpenTerm [SetSort.set]),
      Derives T Γ (closed step trace) → Derives T Γ (¬ₘ ((numₘ(root)) ∈ₘ trace))) :
    Derives T [] (¬ₘ condition step carrier (numₘ(root))) := by
  apply FirstOrder.Derives.neg_intro
  apply bounded_exists_elim (𝒫ₘ(carrier))
    (witnessBody step ((numₘ(root) : SetTerm [] []).weakenBound SetSort.set) (.bvar .here)) Formula.falsum
    (FirstOrder.Derives.assumption List.mem_cons_self)
  let body := witnessBody step ((numₘ(root) : SetTerm [] []).weakenBound SetSort.set) (.bvar .here)
  let Δ : Context signature [SetSort.set] :=
    Formula.openBoundTop (σ := signature) SetSort.set (bounded_exists_body (𝒫ₘ(carrier)) body) ::
      FreshVariable.extendContext SetSort.set [condition step carrier (numₘ(root))]
  have hOpened := FirstOrder.Derives.assumption (T := T) (Γ := Δ)
    (formula := Formula.openBoundTop (σ := signature) SetSort.set
      (bounded_exists_body (𝒫ₘ(carrier)) body)) List.mem_cons_self
  rw [bounded_exists_body_openBoundTop] at hOpened
  have hBody := FirstOrder.Derives.conj_elim_right hOpened
  have hBody' := Eq.mp (congrArg (fun φ : SetOpenFormula [SetSort.set] => Derives T Δ φ)
    (witnessBody_openBoundTop step (numₘ(root) : SetTerm [] []))) hBody
  simp only [finite_numeral_term_weakenFree] at hBody'
  exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hBody')
    (hRefute Δ _ (FirstOrder.Derives.conj_elim_right hBody'))

end YesMetaZFC.Automation.ObjectTrace
