import YesMetaZFC.Model.Henkin.Embedding
import YesMetaZFC.Model.Henkin.WitnessSupport

/-!
# Henkin 扩张的证明论保守性

本模块把已经消去全部见证常量的 Henkin 语法与 Hilbert 证明直接降回原签名。
降签名函数只接受空有限支持证书，因此见证分支由矛盾消去，不需要默认常量、选择公理
或不可计算实例。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}}

/-! ## 可计算的基础语法识别器 -/

mutual

/-- 尝试把 Henkin 项识别为原签名项。 -/
def Term.lower? {bound free : SortContext σ} :
    {sort : σ.SortSymbol} →
      Term (HSignature σ) bound free sort → Option (Term σ bound free sort)
  | _, .bvar entry => some (.bvar entry)
  | _, .fvar entry => some (.fvar entry)
  | _, .app (HenkinFunc.base function) arguments =>
      match Arguments.lower? arguments with
      | some lowered => some (.app function lowered)
      | none => none
  | _, .app (HenkinFunc.witness _ _) _ => none

/-- 尝试把 Henkin 参数列识别为原签名参数列。 -/
def Arguments.lower? {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} →
      Arguments (HSignature σ) bound free sorts →
        Option (Arguments σ bound free sorts)
  | _, .nil => some .nil
  | _, .cons head tail =>
      match Term.lower? head, Arguments.lower? tail with
      | some loweredHead, some loweredTail =>
          some (.cons loweredHead loweredTail)
      | _, _ => none

end

/-- 尝试把 Henkin 公式识别为原签名公式。 -/
def Formula.lower? {bound free : SortContext σ} :
    Formula (HSignature σ) bound free → Option (Formula σ bound free)
  | .falsum => some .falsum
  | .truth => some .truth
  | .rel relation arguments =>
      match Arguments.lower? arguments with
      | some lowered => some (.rel relation lowered)
      | none => none
  | .equal left right =>
      match Term.lower? left, Term.lower? right with
      | some loweredLeft, some loweredRight =>
          some (.equal loweredLeft loweredRight)
      | _, _ => none
  | .neg body =>
      match Formula.lower? body with
      | some lowered => some (.neg lowered)
      | none => none
  | .conj left right =>
      match Formula.lower? left, Formula.lower? right with
      | some loweredLeft, some loweredRight =>
          some (.conj loweredLeft loweredRight)
      | _, _ => none
  | .disj left right =>
      match Formula.lower? left, Formula.lower? right with
      | some loweredLeft, some loweredRight =>
          some (.disj loweredLeft loweredRight)
      | _, _ => none
  | .imp left right =>
      match Formula.lower? left, Formula.lower? right with
      | some loweredLeft, some loweredRight =>
          some (.imp loweredLeft loweredRight)
      | _, _ => none
  | .iff left right =>
      match Formula.lower? left, Formula.lower? right with
      | some loweredLeft, some loweredRight =>
          some (.iff loweredLeft loweredRight)
      | _, _ => none
  | .forallE sort body =>
      match Formula.lower? body with
      | some lowered => some (.forallE sort lowered)
      | none => none
  | .existsE sort body =>
      match Formula.lower? body with
      | some lowered => some (.existsE sort lowered)
      | none => none

mutual

@[simp] theorem Term.lower?_liftTerm
    {bound free : SortContext σ} :
    {sort : σ.SortSymbol} → (term : Term σ bound free sort) →
      Term.lower? (liftTerm term) = some term
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments => by
      change
        (match Arguments.lower? (liftArguments arguments) with
        | some lowered => some (Term.app function lowered)
        | none => none) = some (Term.app function arguments)
      rw [Arguments.lower?_liftArguments arguments]

@[simp] theorem Arguments.lower?_liftArguments
    {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound free sorts) →
        Arguments.lower? (liftArguments arguments) = some arguments
  | _, .nil => rfl
  | _, .cons head tail => by
      change
        (match Term.lower? (liftTerm head),
            Arguments.lower? (liftArguments tail) with
        | some loweredHead, some loweredTail =>
            some (Arguments.cons loweredHead loweredTail)
        | _, _ => none) = some (Arguments.cons head tail)
      rw [Term.lower?_liftTerm head, Arguments.lower?_liftArguments tail]

end

@[simp] theorem Formula.lower?_liftFormula
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    Formula.lower? (liftFormula formula) = some formula := by
  induction formula <;>
    simp_all only [Formula.lower?, liftFormula, Term.lower?_liftTerm,
      Arguments.lower?_liftArguments]

/-- 原项提升是单射。 -/
theorem liftTerm_injective
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {left right : Term σ bound free sort}
    (hLift : liftTerm left = liftTerm right) : left = right := by
  have hLower := congrArg (fun term => Term.lower? (σ := σ) term) hLift
  simpa using hLower

/-- 原参数列提升是单射。 -/
theorem liftArguments_injective
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    {left right : Arguments σ bound free sorts}
    (hLift : liftArguments left = liftArguments right) : left = right := by
  have hLower :=
    congrArg (fun arguments => Arguments.lower? (σ := σ) arguments) hLift
  simpa using hLower

/-- 原公式提升是单射。 -/
theorem liftFormula_injective
    {bound free : SortContext σ}
    {left right : Formula σ bound free}
    (hLift : liftFormula left = liftFormula right) : left = right := by
  have hLower := congrArg (fun formula => Formula.lower? (σ := σ) formula) hLift
  simpa using hLower

/-! ## 由空支持证书直接降签名 -/

mutual

/-- 空见证支持的 Henkin 项直接降为原签名项。 -/
def Term.lower {bound free : SortContext σ} :
    {sort : σ.SortSymbol} →
      (term : Term (HSignature σ) bound free sort) →
      Term.witnessSupport term = [] → Term σ bound free sort
  | _, .bvar entry, _ => .bvar entry
  | _, .fvar entry, _ => .fvar entry
  | _, .app (HenkinFunc.base function) arguments, hSupport =>
      .app function (Arguments.lower arguments hSupport)
  | _, .app (HenkinFunc.witness _ _) _, hSupport => by
      simp [Term.witnessSupport] at hSupport

/-- 空见证支持的 Henkin 参数列直接降为原签名参数列。 -/
def Arguments.lower {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments (HSignature σ) bound free sorts) →
      Arguments.witnessSupport arguments = [] →
        Arguments σ bound free sorts
  | _, .nil, _ => .nil
  | _, .cons head tail, hSupport =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      .cons (Term.lower head hParts.1) (Arguments.lower tail hParts.2)

end

/-- 空见证支持的 Henkin 公式直接降为原签名公式。 -/
def Formula.lower {bound free : SortContext σ} :
    (formula : Formula (HSignature σ) bound free) →
    Formula.witnessSupport formula = [] → Formula σ bound free
  | .falsum, _ => .falsum
  | .truth, _ => .truth
  | .rel relation arguments, hSupport =>
      .rel relation (Arguments.lower arguments hSupport)
  | .equal left right, hSupport =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      .equal (Term.lower left hParts.1) (Term.lower right hParts.2)
  | .neg body, hSupport => .neg (Formula.lower body hSupport)
  | .conj left right, hSupport => by
      have hParts := List.append_eq_nil_iff.mp hSupport
      exact .conj (Formula.lower left hParts.1)
        (Formula.lower right hParts.2)
  | .disj left right, hSupport => by
      have hParts := List.append_eq_nil_iff.mp hSupport
      exact .disj (Formula.lower left hParts.1)
        (Formula.lower right hParts.2)
  | .imp left right, hSupport => by
      have hParts := List.append_eq_nil_iff.mp hSupport
      exact .imp (Formula.lower left hParts.1)
        (Formula.lower right hParts.2)
  | .iff left right, hSupport => by
      have hParts := List.append_eq_nil_iff.mp hSupport
      exact .iff (Formula.lower left hParts.1)
        (Formula.lower right hParts.2)
  | .forallE sort body, hSupport =>
      .forallE sort (Formula.lower body hSupport)
  | .existsE sort body, hSupport =>
      .existsE sort (Formula.lower body hSupport)

mutual

/-- 降签名后再提升，恢复原 Henkin 项。 -/
theorem Term.lift_lower {bound free : SortContext σ} :
    {sort : σ.SortSymbol} → (term : Term (HSignature σ) bound free sort) →
    (hSupport : Term.witnessSupport term = []) →
    liftTerm (Term.lower term hSupport) = term
  | _, .bvar _, _ => rfl
  | _, .fvar _, _ => rfl
  | _, .app (HenkinFunc.base function) arguments, hSupport => by
      simpa [Term.lower, liftTerm] using Arguments.lift_lower arguments hSupport
  | _, .app (HenkinFunc.witness sort index) arguments, hSupport => by
      simp [Term.witnessSupport] at hSupport

/-- 降签名后再提升，恢复原 Henkin 参数列。 -/
theorem Arguments.lift_lower {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} → (arguments : Arguments (HSignature σ) bound free sorts) →
    (hSupport : Arguments.witnessSupport arguments = []) →
    liftArguments (Arguments.lower arguments hSupport) = arguments
  | _, .nil, _ => rfl
  | _, .cons head tail, hSupport => by
      have hParts := List.append_eq_nil_iff.mp hSupport
      simp [Arguments.lower, Term.lift_lower head hParts.1,
        Arguments.lift_lower tail hParts.2]

end

/-- 降签名后再提升，恢复原 Henkin 公式。 -/
theorem Formula.lift_lower
    {bound free : SortContext σ}
    (formula : Formula (HSignature σ) bound free)
    (hSupport : Formula.witnessSupport formula = []) :
    liftFormula (Formula.lower formula hSupport) = formula := by
  refine Formula.rec
    (motive := fun _ _ formula => ∀ hSupport : Formula.witnessSupport formula = [],
      liftFormula (Formula.lower formula hSupport) = formula)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ formula hSupport
  case refine_3 =>
    intro bound free relation args h
    exact congrArg (Formula.rel relation) (Arguments.lift_lower (σ := σ) args h)
  case refine_5 =>
    intro bound free body ih h
    exact congrArg Formula.neg (ih h)
  case refine_10 =>
    intro bound free sort body ih h
    exact congrArg (Formula.forallE sort) (ih h)
  case refine_11 =>
    intro bound free sort body ih h
    exact congrArg (Formula.existsE sort) (ih h)
  all_goals intros
  all_goals simp_all only [Formula.lower, liftFormula, Term.lift_lower]

/-- 原公式提升后不含任何见证，因而其有限支持为空。 -/
@[simp] theorem Formula.witnessSupport_liftFormula
    [DecidableEq σ.SortSymbol]
    {bound free : SortContext σ}
    (formula : Formula σ bound free) :
    Formula.witnessSupport (liftFormula formula) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨sort, index⟩ hMem
  exact liftFormula_not_usesWitness sort index formula
    ((Formula.mem_witnessSupport_iff sort index (liftFormula formula)).mp hMem)

/-! ## 变量替换降签名 -/

namespace VariableSubstitution

/-- 空见证支持的统一变量替换逐槽降回原签名。 -/
def lower
    {bound free : SortContext σ} :
    {source : SortContext σ} →
      (substitution : VariableSubstitution (HSignature σ) source bound free) →
      witnessSupport (σ := σ) substitution = [] →
        VariableSubstitution σ source bound free
  | [], _, _ => VariableSubstitution.empty
  | _ :: source, substitution, hSupport =>
      let hParts := List.append_eq_nil_iff.mp hSupport
      VariableSubstitution.cons
        (Term.lower (σ := σ) (substitution .here) hParts.1)
        (lower (source := source)
          (fun entry => substitution (.there entry)) hParts.2)

/-- 变量替换降签名后再逐槽提升，恢复原替换。 -/
theorem lift_lower
    {bound free : SortContext σ} :
    {source : SortContext σ} →
      (substitution : VariableSubstitution (HSignature σ) source bound free) →
      (hSupport : witnessSupport (σ := σ) substitution = []) →
      (liftVariableSubstitution
          (lower (σ := σ) substitution hSupport) :
        VariableSubstitution (HSignature σ) source bound free) =
        (fun {sort} (entry : Variable source sort) => substitution entry)
  | [], substitution, _ => by
      funext sort entry
      exact nomatch entry
  | _ :: source, substitution, hSupport => by
      have hParts := List.append_eq_nil_iff.mp hSupport
      funext resultSort entry
      cases entry with
      | here =>
          simpa [lower,
            VariableSubstitution.cons, liftVariableSubstitution] using
            (Term.lift_lower (σ := σ) (substitution .here) hParts.1)
      | there previous =>
          have hTail := lift_lower (source := source)
            (fun entry => substitution (.there entry)) hParts.2
          have hPoint := congrArg (fun tail => tail previous) hTail
          simpa [lower,
            VariableSubstitution.cons, liftVariableSubstitution] using hPoint

end VariableSubstitution

end HenkinSignature

open HenkinSignature

variable {σ : Signature.{u, v, w}}

universe u₁ u₂ u₃ u₄

private theorem eq_map₂
    {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃}
    (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
    (hA : a₁ = a₂) (hB : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ := by
  cases hA
  cases hB
  rfl

private theorem eq_map₃
    {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃} {δ : Sort u₄}
    (f : α → β → γ → δ)
    {a₁ a₂ : α} {b₁ b₂ : β} {c₁ c₂ : γ}
    (hA : a₁ = a₂) (hB : b₁ = b₂) (hC : c₁ = c₂) :
    f a₁ b₁ c₁ = f a₂ b₂ c₂ := by
  cases hA
  cases hB
  cases hC
  rfl

namespace HilbertBaseAxiom

/-- Henkin 公理的原签名原像，以及结论提升后恢复原结论的证书。 -/
structure Lowered
    {free : SortContext σ}
    (target : OpenFormula (HSignature σ) free) where
  source : OpenFormula σ free
  proof : HilbertBaseAxiom σ source
  lift_source : liftFormula source = target

/-- 空载荷支持的 Henkin 基础公理直接降回原签名。 -/
def lower
    {free : SortContext σ}
    {target : OpenFormula (HSignature σ) free}
    (hAxiom : HilbertBaseAxiom (HSignature σ) target)
    (hSupport : witnessSupport hAxiom = []) : Lowered target := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      have hHead := List.append_eq_nil_iff.mp hParts.1
      let antecedent' := Formula.lower (σ := σ) antecedent hHead.1
      let middle' := Formula.lower (σ := σ) middle hHead.2
      let consequent' := Formula.lower (σ := σ) consequent hParts.2
      have hLiftAntecedent : liftFormula antecedent' = antecedent :=
        Formula.lift_lower (σ := σ) antecedent hHead.1
      have hLiftMiddle : liftFormula middle' = middle :=
        Formula.lift_lower (σ := σ) middle hHead.2
      have hLiftConsequent : liftFormula consequent' = consequent :=
        Formula.lift_lower (σ := σ) consequent hParts.2
      refine ⟨_, .implication_distribution antecedent' middle' consequent', ?_⟩
      simp only [liftFormula_imp]
      exact eq_map₃
        (fun a m c =>
          Formula.imp (Formula.imp a (Formula.imp m c))
            (Formula.imp (Formula.imp a m) (Formula.imp a c)))
        hLiftAntecedent hLiftMiddle hLiftConsequent
  | self_implication formula =>
      let formula' := Formula.lower (σ := σ) formula hSupport
      have hLiftFormula : liftFormula formula' = formula :=
        Formula.lift_lower (σ := σ) formula hSupport
      refine ⟨_, .self_implication formula', ?_⟩
      simp only [liftFormula_imp]
      exact congrArg (fun p => Formula.imp p (Formula.imp p p)) hLiftFormula
  | weakening left right
  | contradiction left right
  | explosion left right
  | case_analysis left right
  | conjunction_intro left right
  | conjunction_elim_left left right
  | conjunction_elim_right left right
  | disjunction_intro_left left right
  | disjunction_intro_right left right
  | biconditional_intro left right
  | biconditional_elim_left left right
  | biconditional_elim_right left right =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      let left' := Formula.lower (σ := σ) left hParts.1
      let right' := Formula.lower (σ := σ) right hParts.2
      have hLiftLeft : liftFormula left' = left := Formula.lift_lower left hParts.1
      have hLiftRight : liftFormula right' = right := Formula.lift_lower right hParts.2
      first
      | refine ⟨_, .weakening left' right', ?_⟩
        solve | simp only [liftFormula_imp, hLiftLeft, hLiftRight]
      | refine ⟨_, .contradiction left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_neg, hLiftLeft, hLiftRight]
      | refine ⟨_, .explosion left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_neg, hLiftLeft, hLiftRight]
      | refine ⟨_, .case_analysis left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_neg, hLiftLeft, hLiftRight]
      | refine ⟨_, .conjunction_intro left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_conj, hLiftLeft, hLiftRight]
      | refine ⟨_, .conjunction_elim_left left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_conj, hLiftLeft, hLiftRight]
      | refine ⟨_, .conjunction_elim_right left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_conj, hLiftLeft, hLiftRight]
      | refine ⟨_, .disjunction_intro_left left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_disj, hLiftLeft, hLiftRight]
      | refine ⟨_, .disjunction_intro_right left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_disj, hLiftLeft, hLiftRight]
      | refine ⟨_, .biconditional_intro left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_iff, hLiftLeft, hLiftRight]
      | refine ⟨_, .biconditional_elim_left left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_iff, hLiftLeft, hLiftRight]
      | refine ⟨_, .biconditional_elim_right left' right', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_iff, hLiftLeft, hLiftRight]
  | classical formula
  | falsum_elimination formula
  | negation_intro formula
  | negation_elimination formula =>
      let formula' := Formula.lower (σ := σ) formula hSupport
      have hLiftFormula : liftFormula formula' = formula := Formula.lift_lower formula hSupport
      first
      | refine ⟨_, .classical formula', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_neg, hLiftFormula]
      | refine ⟨_, .falsum_elimination formula', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_falsum, hLiftFormula]
      | refine ⟨_, .negation_intro formula', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_falsum, liftFormula_neg, hLiftFormula]
      | refine ⟨_, .negation_elimination formula', ?_⟩
        solve | simp only [liftFormula_imp, liftFormula_neg, liftFormula_falsum, hLiftFormula]
  | truth_intro =>
      exact ⟨.truth, .truth_intro, liftFormula_truth⟩
  | disjunction_elimination left right conclusion =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      have hHead := List.append_eq_nil_iff.mp hParts.1
      let left' := Formula.lower (σ := σ) left hHead.1
      let right' := Formula.lower (σ := σ) right hHead.2
      let conclusion' := Formula.lower (σ := σ) conclusion hParts.2
      have hLiftLeft : liftFormula left' = left :=
        Formula.lift_lower (σ := σ) left hHead.1
      have hLiftRight : liftFormula right' = right :=
        Formula.lift_lower (σ := σ) right hHead.2
      have hLiftConclusion : liftFormula conclusion' = conclusion :=
        Formula.lift_lower (σ := σ) conclusion hParts.2
      refine ⟨_, .disjunction_elimination left' right' conclusion', ?_⟩
      simp only [liftFormula_imp, liftFormula_disj]
      exact eq_map₃
        (fun l r c => Formula.imp (Formula.imp l c)
          (Formula.imp (Formula.imp r c)
            (Formula.imp (Formula.disj l r) c)))
        hLiftLeft hLiftRight hLiftConclusion
  | forall_specialization sort body term =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      let body' := Formula.lower (σ := σ) body hParts.1
      let term' := Term.lower (σ := σ) term hParts.2
      have hLiftBody : liftFormula body' = body :=
        Formula.lift_lower (σ := σ) body hParts.1
      have hLiftTerm : liftTerm term' = term :=
        Term.lift_lower (σ := σ) term hParts.2
      refine ⟨_, HilbertBaseAxiom.forall_specialization
        (σ := σ) sort body' term', ?_⟩
      simp only [liftFormula_imp, liftFormula_forallE,
        liftFormula_instantiateTop]
      exact eq_map₂
        (fun b t => Formula.imp (Formula.forallE sort b)
          (Formula.instantiateTop t b)) hLiftBody hLiftTerm
  | forall_distribution sort antecedent consequent =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      let antecedent' := Formula.lower (σ := σ) antecedent hParts.1
      let consequent' := Formula.lower (σ := σ) consequent hParts.2
      have hLiftAntecedent : liftFormula antecedent' = antecedent :=
        Formula.lift_lower (σ := σ) antecedent hParts.1
      have hLiftConsequent : liftFormula consequent' = consequent :=
        Formula.lift_lower (σ := σ) consequent hParts.2
      have hLiftImp :
          liftFormula (Formula.imp antecedent' consequent') =
            Formula.imp (liftFormula antecedent') (liftFormula consequent') :=
        liftFormula_imp (σ := σ) antecedent' consequent'
      refine ⟨_, HilbertBaseAxiom.forall_distribution
        (σ := σ) sort antecedent' consequent', ?_⟩
      simp only [liftFormula_imp, liftFormula_forallFreeTop]
      have hStructural := congrArg
        (fun inner => Formula.imp
          (Formula.forallFreeTop (σ := HSignature σ) sort inner)
          (Formula.imp
            (Formula.forallFreeTop (σ := HSignature σ) sort
              (liftFormula antecedent'))
            (Formula.forallFreeTop (σ := HSignature σ) sort
              (liftFormula consequent')))) hLiftImp
      exact Eq.trans hStructural
        (eq_map₂
          (fun a c => Formula.imp
            (Formula.forallFreeTop (σ := HSignature σ) sort
              (Formula.imp a c))
            (Formula.imp
              (Formula.forallFreeTop (σ := HSignature σ) sort a)
              (Formula.forallFreeTop (σ := HSignature σ) sort c)))
          hLiftAntecedent hLiftConsequent)
  | vacuous_forall sort formula =>
      let formula' := Formula.lower (σ := σ) formula hSupport
      have hLiftFormula : liftFormula formula' = formula :=
        Formula.lift_lower (σ := σ) formula hSupport
      have hLiftWeaken :
          liftFormula (Formula.weakenFree (σ := σ) sort formula') =
            Formula.weakenFree (σ := HSignature σ) sort
              (liftFormula formula') :=
        liftFormula_weakenFree (σ := σ) sort formula'
      refine ⟨_, HilbertBaseAxiom.vacuous_forall
        (σ := σ) sort formula', ?_⟩
      simp only [liftFormula_imp, liftFormula_forallFreeTop]
      have hStructural := congrArg
        (fun weakened => Formula.imp (liftFormula formula')
          (Formula.forallFreeTop (σ := HSignature σ) sort weakened))
        hLiftWeaken
      exact Eq.trans hStructural
        (congrArg
          (fun p => Formula.imp p
            (Formula.forallFreeTop (σ := HSignature σ) sort
              (Formula.weakenFree (σ := HSignature σ) sort p)))
          hLiftFormula)
  | exists_introduction sort body term =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      let body' := Formula.lower (σ := σ) body hParts.1
      let term' := Term.lower (σ := σ) term hParts.2
      have hLiftBody : liftFormula body' = body :=
        Formula.lift_lower (σ := σ) body hParts.1
      have hLiftTerm : liftTerm term' = term :=
        Term.lift_lower (σ := σ) term hParts.2
      refine ⟨_, HilbertBaseAxiom.exists_introduction
        (σ := σ) sort body' term', ?_⟩
      simp only [liftFormula_imp, liftFormula_instantiateTop,
        liftFormula_existsE]
      exact eq_map₂
        (fun b t => Formula.imp (Formula.instantiateTop t b)
          (Formula.existsE sort b)) hLiftBody hLiftTerm
  | exists_elimination sort body conclusion =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      let body' := Formula.lower (σ := σ) body hParts.1
      let conclusion' := Formula.lower (σ := σ) conclusion hParts.2
      have hLiftBody : liftFormula body' = body :=
        Formula.lift_lower (σ := σ) body hParts.1
      have hLiftConclusion : liftFormula conclusion' = conclusion :=
        Formula.lift_lower (σ := σ) conclusion hParts.2
      have hLiftWeak :
          liftFormula (Formula.weakenFree (σ := σ) sort conclusion') =
            Formula.weakenFree (σ := HSignature σ) sort
              (liftFormula conclusion') :=
        liftFormula_weakenFree (σ := σ) sort conclusion'
      have hLiftInner :
          liftFormula
              (Formula.imp body'
                (Formula.weakenFree (σ := σ) sort conclusion')) =
            Formula.imp (liftFormula body')
              (Formula.weakenFree (σ := HSignature σ) sort
                (liftFormula conclusion')) :=
        Eq.trans (liftFormula_imp (σ := σ) body'
          (Formula.weakenFree (σ := σ) sort conclusion'))
          (congrArg (Formula.imp (liftFormula body')) hLiftWeak)
      refine ⟨_, HilbertBaseAxiom.exists_elimination
        (σ := σ) sort body' conclusion', ?_⟩
      simp only [liftFormula_imp, liftFormula_forallFreeTop,
        liftFormula_existsFreeTop]
      have hStructural := congrArg
        (fun inner => Formula.imp
          (Formula.forallFreeTop (σ := HSignature σ) sort inner)
          (Formula.imp
            (Formula.existsFreeTop (σ := HSignature σ) sort
              (liftFormula body'))
            (liftFormula conclusion'))) hLiftInner
      exact Eq.trans hStructural
        (eq_map₂
          (fun b c => Formula.imp
            (Formula.forallFreeTop (σ := HSignature σ) sort
              (Formula.imp b
                (Formula.weakenFree (σ := HSignature σ) sort c)))
            (Formula.imp
              (Formula.existsFreeTop (σ := HSignature σ) sort b) c))
          hLiftBody hLiftConclusion)
  | equality_substitution sort left right body =>
      have hParts := List.append_eq_nil_iff.mp hSupport
      have hHead := List.append_eq_nil_iff.mp hParts.1
      let left' := Term.lower (σ := σ) left hHead.1
      let right' := Term.lower (σ := σ) right hHead.2
      let body' := Formula.lower (σ := σ) body hParts.2
      have hLiftLeft : liftTerm left' = left :=
        Term.lift_lower (σ := σ) left hHead.1
      have hLiftRight : liftTerm right' = right :=
        Term.lift_lower (σ := σ) right hHead.2
      have hLiftBody : liftFormula body' = body :=
        Formula.lift_lower (σ := σ) body hParts.2
      refine ⟨_, HilbertBaseAxiom.equality_substitution
        (σ := σ) sort left' right' body', ?_⟩
      simp only [liftFormula_imp, liftFormula_equal,
        liftFormula_instantiateTop]
      exact eq_map₃
        (fun l r b => Formula.imp (Formula.equal l r)
          (Formula.imp (Formula.instantiateTop l b)
            (Formula.instantiateTop r b)))
        hLiftLeft hLiftRight hLiftBody
  | equality_reflexivity term =>
      let term' := Term.lower (σ := σ) term hSupport
      have hLiftTerm : liftTerm term' = term :=
        Term.lift_lower (σ := σ) term hSupport
      refine ⟨_, HilbertBaseAxiom.equality_reflexivity
        (σ := σ) term', ?_⟩
      simp only [liftFormula_equal]
      exact congrArg (fun t => Formula.equal t t) hLiftTerm

end HilbertBaseAxiom

/-! ## Hilbert 推导降签名 -/

namespace Formula

/-- 被提升公式若呈蕴含形，则原公式本身也具有唯一对应的蕴含分解。 -/
structure ImpPreimage {free : SortContext σ}
    (source : OpenFormula σ free)
    (antecedent consequent : OpenFormula (HSignature σ) free) where
  sourceAntecedent : OpenFormula σ free
  sourceConsequent : OpenFormula σ free
  source_eq : source = .imp sourceAntecedent sourceConsequent
  lift_antecedent : liftFormula sourceAntecedent = antecedent
  lift_consequent : liftFormula sourceConsequent = consequent

/-- 提升不会伪造公式最外层的蕴含构造子。 -/
def impPreimage {free : SortContext σ}
    {source : OpenFormula σ free}
    {antecedent consequent : OpenFormula (HSignature σ) free}
    (hLift : liftFormula source = .imp antecedent consequent) :
    ImpPreimage source antecedent consequent := by
  cases source with
  | falsum => cases hLift
  | truth => cases hLift
  | rel relation arguments => cases hLift
  | equal left right => cases hLift
  | neg body => cases hLift
  | conj left right => cases hLift
  | disj left right => cases hLift
  | imp left right =>
      simp only [liftFormula_imp] at hLift
      cases hLift
      exact ⟨left, right, rfl, rfl, rfl⟩
  | iff left right => cases hLift
  | forallE sort body => cases hLift
  | existsE sort body => cases hLift

end Formula

namespace HilbertDerivation

/-- 空见证支持的 Henkin 推导降回原签名时携带其精确结论等式。 -/
structure Lowered {T : Theory σ} {free : SortContext σ}
    (target : OpenFormula (HSignature σ) free) where
  source : OpenFormula σ free
  proof : HilbertDerivation T free source
  lift_source : liftFormula source = target

/--
逐节点降低一棵已经清空有限见证支持的 Hilbert 推导。
所有规则载荷都同步降低，因此结果不依赖额外桥接公理或默认项。
-/
def lower [DecidableEq σ.SortSymbol]
    {T : Theory σ} {free : SortContext σ}
    {target : OpenFormula (HSignature σ) free}
    (proof : HilbertDerivation (liftTheory T) free target)
    (hSupport : witnessSupport proof = []) : Lowered (T := T) target :=
  match proof with
  | .logical_axiom hAxiom =>
      let lowered := HilbertBaseAxiom.lower hAxiom hSupport
      ⟨lowered.source, .logical_axiom lowered.proof, lowered.lift_source⟩
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.theory_axiom
      _ _ free sentence hTheory =>
      have hSentenceSupport : Formula.witnessSupport sentence = [] := by
        rw [← Formula.witnessSupport_fromSentence (free := free) sentence]
        exact hSupport
      let source := Formula.lower (σ := σ) sentence hSentenceSupport
      have hLiftSentence : liftFormula source = sentence :=
        Formula.lift_lower (σ := σ) sentence hSentenceSupport
      have hSource : T source := by
        rcases hTheory with ⟨candidate, hCandidate, hLiftCandidate⟩
        have hCandidateSource : candidate = source :=
          liftFormula_injective
            (Eq.trans hLiftCandidate hLiftSentence.symm)
        cases hCandidateSource
        exact hCandidate
      ⟨Formula.fromSentence source, .theory_axiom hSource,
        Eq.trans
          (liftFormula_fromSentence (σ := σ) (free := free) source)
          (congrArg
            (fun lifted : Sentence (HSignature σ) =>
              Formula.fromSentence (free := free) lifted)
            hLiftSentence)⟩
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.modus_ponens
      _ _ free antecedent consequent hAntecedent hImplication =>
      let hParts := List.append_eq_nil_iff.mp hSupport
      let loweredAntecedent := lower hAntecedent hParts.1
      let loweredImplication := lower hImplication hParts.2
      let preimage := Formula.impPreimage loweredImplication.lift_source
      have hAntecedentSource :
          loweredAntecedent.source = preimage.sourceAntecedent :=
        liftFormula_injective
          (Eq.trans loweredAntecedent.lift_source
            preimage.lift_antecedent.symm)
      let antecedentProof :=
        HilbertDerivation.castFormula hAntecedentSource
          loweredAntecedent.proof
      let implicationProof :=
        HilbertDerivation.castFormula preimage.source_eq
          loweredImplication.proof
      ⟨preimage.sourceConsequent,
        .modus_ponens antecedentProof implicationProof,
        preimage.lift_consequent⟩
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.forall_generalization
      _ _ free sort formula hFormula =>
      let lowered := lower hFormula hSupport
      ⟨Formula.forallFreeTop sort lowered.source,
        .forall_generalization lowered.proof,
        Eq.trans
          (liftFormula_forallFreeTop (σ := σ) sort lowered.source)
          (congrArg
            (Formula.forallFreeTop (σ := HSignature σ) sort)
            lowered.lift_source)⟩
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.free_strengthening
      _ _ free sort formula hFormula =>
      let lowered := lower hFormula hSupport
      have hTargetSupport :
          Formula.witnessSupport
              (Formula.weakenFree (σ := HSignature σ) sort formula) = [] := by
        rw [← lowered.lift_source]
        exact Formula.witnessSupport_liftFormula lowered.source
      have hWeakenSupport :
          Formula.witnessSupport
              (Formula.weakenFree (σ := HSignature σ) sort formula) =
            Formula.witnessSupport formula := by
        unfold Formula.weakenFree
        exact Formula.witnessSupport_renameMapped _ _ formula
      have hFormulaSupport : Formula.witnessSupport formula = [] := by
        rw [← hWeakenSupport]
        exact hTargetSupport
      let source := Formula.lower (σ := σ) formula hFormulaSupport
      have hLiftSource : liftFormula source = formula :=
        Formula.lift_lower (σ := σ) formula hFormulaSupport
      have hLiftWeaken :
          liftFormula (Formula.weakenFree (σ := σ) sort source) =
            Formula.weakenFree (σ := HSignature σ) sort formula :=
        Eq.trans (liftFormula_weakenFree (σ := σ) sort source)
          (congrArg
            (Formula.weakenFree (σ := HSignature σ) sort)
            hLiftSource)
      have hChildSource :
          lowered.source = Formula.weakenFree (σ := σ) sort source :=
        liftFormula_injective
          (Eq.trans lowered.lift_source hLiftWeaken.symm)
      let childProof :=
        HilbertDerivation.castFormula hChildSource lowered.proof
      ⟨source, .free_strengthening childProof, hLiftSource⟩
  | @YesMetaZFC.Logic.FirstOrder.HilbertDerivation.free_substitution
      _ _ sourceFree targetFree substitution formula hFormula =>
      let hParts := List.append_eq_nil_iff.mp hSupport
      let loweredSubstitution :
          VariableSubstitution σ sourceFree [] targetFree :=
        HenkinSignature.VariableSubstitution.lower
          (σ := σ) (bound := []) (free := targetFree)
          (source := sourceFree)
          (fun {sort : σ.SortSymbol} (entry : Variable sourceFree sort) =>
            substitution entry)
          hParts.1
      let loweredFormula := lower hFormula hParts.2
      have hLiftSubstitution :
          (liftVariableSubstitution (σ := σ) loweredSubstitution :
              VariableSubstitution (HSignature σ) sourceFree [] targetFree) =
            (fun {sort : σ.SortSymbol} (entry : Variable sourceFree sort) =>
              substitution entry) := by
        simpa only [loweredSubstitution] using!
          (HenkinSignature.VariableSubstitution.lift_lower
            (σ := σ) (bound := []) (free := targetFree)
            (source := sourceFree)
            (fun {sort : σ.SortSymbol} (entry : Variable sourceFree sort) =>
              substitution entry)
            hParts.1)
      have hSubstituted :
          Formula.substituteFree (σ := HSignature σ)
              (liftVariableSubstitution (σ := σ) loweredSubstitution)
              (liftFormula loweredFormula.source) =
            Formula.substituteFree (σ := HSignature σ)
              (fun {sort : σ.SortSymbol}
                (entry : Variable sourceFree sort) => substitution entry)
              formula := by
        rw [hLiftSubstitution, loweredFormula.lift_source]
      ⟨Formula.substituteFree loweredSubstitution loweredFormula.source,
        .free_substitution loweredSubstitution loweredFormula.proof,
        Eq.trans
          (liftFormula_substituteFree (σ := σ)
            loweredSubstitution loweredFormula.source)
          hSubstituted⟩

end HilbertDerivation

namespace Provable

/--
Henkin 扩张对原签名闭句的证明论保守性。
先有限清洗证明树中的全部见证，再由可计算降签名恢复原证明。
-/
theorem lowerHenkin [DecidableEq σ.SortSymbol]
    {T : Theory σ} {sentence : Sentence σ}
    (hSentence : Provable (liftTheory T) (liftFormula sentence)) :
    Provable T sentence := by
  rcases hSentence with ⟨proof⟩
  let hTheoryAvoids :
      ∀ witness : WitnessRef σ,
        ∀ {theorySentence : Sentence (HSignature σ)},
          liftTheory T theorySentence →
            ¬ Formula.usesWitness witness.1 witness.2 theorySentence :=
    fun witness _ hTheory =>
      liftTheory_avoids hTheory witness.1 witness.2
  let hSentenceAvoids :
      ∀ witness : WitnessRef σ,
        ¬ Formula.usesWitness witness.1 witness.2
          (liftFormula sentence) :=
    fun witness =>
      liftFormula_not_usesWitness witness.1 witness.2 sentence
  let cleaned := HilbertDerivation.eliminateOwnWitnessSupport
    hTheoryAvoids hSentenceAvoids proof
  have hCleanedSupport :
      HilbertDerivation.witnessSupport cleaned = [] := by
    simpa only [cleaned] using
      (HilbertDerivation.witnessSupport_eliminateOwnWitnessSupport
        hTheoryAvoids hSentenceAvoids proof)
  let lowered := HilbertDerivation.lower cleaned hCleanedSupport
  have hSource : lowered.source = sentence :=
    liftFormula_injective lowered.lift_source
  exact ⟨HilbertDerivation.castFormula hSource lowered.proof⟩

end Provable

namespace Derives

/-- Henkin 扩张对原签名闭句的空上下文推导保守性。 -/
theorem lowerHenkin [DecidableEq σ.SortSymbol]
    {T : Theory σ} {sentence : Sentence σ}
    (hSentence : Derives (liftTheory T) [] (liftFormula sentence)) :
    Derives T [] sentence := by
  change Provable (liftTheory T) (liftFormula sentence) at hSentence
  change Provable T sentence
  exact Provable.lowerHenkin hSentence

end Derives

end FirstOrder
end Logic
end YesMetaZFC
