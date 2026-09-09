import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodeDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core

/-!
# ProofT 内在有界量词规则

这里把成员 guard 与对象量词的引入、消去固定成类型化接口。调用方只提供实际
见证及其成员证明，不再手写自由变量编号、关闭公式或新鲜性合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 推导沿规范最新 free 槽提升，不要求调用方处理上下文重命名。 -/
theorem fresh_context_weaken
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    {formula : SetOpenFormula free}
    (hFormula : Γ ⊢ₘ[T] formula) :
    FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
      formula.weakenFree SetSort.set := by
  simpa only [FreshVariable.extendContext, Formula.weakenFree,
    Formula.renameFree, Renaming.weakenFree] using!
    FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set) hFormula

theorem instantiate_top_membership
    {free : SetContext}
    (bound witness : SetOpenTerm free) :
    Formula.instantiateTop witness
        (set_levy_bound.membership
          (.bvar .here) (bound.weakenBound SetSort.set)) =
      witness ∈ₘ bound := by
  change
    @Formula.rel signature [] free RelationSymbol.membership
        ((Arguments.cons
            (.bvar .here)
            (Arguments.cons (bound.weakenBound SetSort.set) .nil)).instantiateTop
          witness) =
      @Formula.rel signature [] free RelationSymbol.membership
        (Arguments.cons witness (Arguments.cons bound .nil))
  rw [Arguments.instantiateTop_cons,
    Term.instantiateTop_bvar_here,
    Arguments.instantiateTop_cons,
    Term.instantiateTop_weakenBound,
    Arguments.instantiateTop_nil]

theorem bounded_exists_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (bound : SetOpenTerm free)
    (body : SetFormula [SetSort.set] free)
    (witness : SetOpenTerm free)
    (hBound : Γ ⊢ₘ[T] witness ∈ₘ bound)
    (hBody : Γ ⊢ₘ[T] body.instantiateTop witness) :
    Γ ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound bound body := by
  have hBoundAt :
      Γ ⊢ₘ[T]
        Formula.instantiateTop witness
          (set_levy_bound.membership
            (.bvar .here) (bound.weakenBound SetSort.set)) := by
    rw [instantiate_top_membership]
    exact hBound
  apply FirstOrder.Derives.exists_intro witness
  simpa [Formula.LevyBound.boundedExists] using
    FirstOrder.Derives.conj_intro hBoundAt hBody

/--
有界全称引入：在规范 fresh 槽及其成员假设下证明主体后，直接封闭为有界全称。
调用方不再展开 `abstractFreeTop`，也不需要提供变量编号或新鲜性证明。
-/
theorem bounded_forall_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (bound : SetOpenTerm free)
    (body : SetFormula [SetSort.set] free)
    (hBody :
      ((FreshVariable.newest (σ := signature) (free := free) SetSort.set ∈ₘ
          bound.weakenFree SetSort.set) ::
        FreshVariable.extendContext SetSort.set Γ) ⊢ₘ[T]
          Formula.openBoundTop (σ := signature) SetSort.set body) :
    Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound bound body := by
  let guarded : SetFormula [SetSort.set] free :=
    set_levy_bound.membership
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (bound.weakenBound SetSort.set) ⟶ₘ
      body
  have hGuarded :
      FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
        Formula.openBoundTop (σ := signature) SetSort.set guarded := by
    have hImp := FirstOrder.Derives.imp_intro hBody
    change FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
      (FreshVariable.newest (σ := signature) (free := free) SetSort.set ∈ₘ
          Term.openBoundTop (σ := signature) SetSort.set
            (bound.weakenBound SetSort.set)) ⟶ₘ
        Formula.openBoundTop (σ := signature) SetSort.set body
    rw [Term.openBoundTop_weakenBound]
    exact hImp
  simpa [Formula.LevyBound.boundedForall, guarded] using
    FirstOrder.Derives.forall_intro hGuarded

/--
有限 numeral 上的有界全称由外部有限分支直接装配。索引范围、fresh 变量及等式运输
都由内在类型和 `FiniteCore` 固定，调用方只需给出每个标准位置的证明。
-/
theorem bounded_forall_numeral_intro
    {T : SetTheory}
    (C : FiniteCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (bound : Nat)
    (body : SetFormula [SetSort.set] free)
    (hBody :
      ∀ index, index < bound →
        Γ ⊢ₘ[T] body.instantiateTop (numₘ(index))) :
    Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (numₘ(bound)) body := by
  apply bounded_forall_intro (bound := numₘ(bound)) (body := body)
  let finiteBound : SetOpenTerm free := numₘ(bound)
  let point : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  let Δ : Context signature (SetSort.set :: free) :=
    (point ∈ₘ finiteBound.weakenFree SetSort.set) ::
      FreshVariable.extendContext SetSort.set Γ
  change Δ ⊢ₘ[T] Formula.openBoundTop
    (σ := signature) SetSort.set body
  have hMemberRaw :
      Δ ⊢ₘ[T] point ∈ₘ finiteBound.weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hMember : Δ ⊢ₘ[T] point ∈ₘ numₘ(bound) := by
    simpa [finiteBound] using hMemberRaw
  apply C.member_elim bound point
    (Formula.openBoundTop (σ := signature) SetSort.set body) hMember
  intro index hIndex
  let equality : SetOpenFormula (SetSort.set :: free) :=
    point ≐ₘ numₘ(index)
  let Ε : Context signature (SetSort.set :: free) := equality :: Δ
  let numeral : SetOpenTerm free := numₘ(index)
  change Ε ⊢ₘ[T] Formula.openBoundTop
    (σ := signature) SetSort.set body
  have hEquality : Ε ⊢ₘ[T] point ≐ₘ numₘ(index) :=
    FirstOrder.Derives.assumption (by simp [Ε, equality])
  have hNumeralWeakened :
      Ε ⊢ₘ[T]
        (body.instantiateTop numeral).weakenFree SetSort.set := by
    simpa [Ε, Δ, equality, finiteBound, numeral] using
      (FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons
          (fresh_context_weaken (hBody index hIndex))))
  have hNumeral :
      Ε ⊢ₘ[T]
        (body.weakenFree SetSort.set).instantiateTop
          (numeral.weakenFree SetSort.set) := by
    rw [Formula.instantiateTop_weakenFree]
    exact hNumeralWeakened
  have hNumeralEquality :
      Ε ⊢ₘ[T] numeral.weakenFree SetSort.set ≐ₘ point := by
    simpa [numeral] using FirstOrder.Derives.eq_symm hEquality
  have hTransport := FirstOrder.Derives.eq_subst
    (body := body.weakenFree SetSort.set)
    hNumeralEquality hNumeral
  simpa only [Formula.openBoundTop_eq_instantiateTop_weakenFree] using
    hTransport

/-- 只替换量词的集合界，主体的当前 binder 保持不变。 -/
theorem bounded_forall_of_bound_eq
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    {left right : SetOpenTerm free}
    {body : SetFormula [SetSort.set] free}
    (hBound : Γ ⊢ₘ[T] left ≐ₘ right)
    (hBody : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound right body) :
    Γ ⊢ₘ[T] Formula.LevyBound.boundedForall set_levy_bound left body := by
  let template : SetFormula [SetSort.set] free :=
    Formula.LevyBound.boundedForall set_levy_bound
      (.bvar .here) (body.weakenBoundUnderTop SetSort.set)
  have hAt : Γ ⊢ₘ[T] template.instantiateTop right := by
    change Γ ⊢ₘ[T]
      (Formula.LevyBound.boundedForall set_levy_bound
        ((.bvar .here) : SetTerm [SetSort.set] free)
        (body.weakenBoundUnderTop SetSort.set)).instantiateTop right
    rw [Formula.LevyBound.boundedForall_instantiateTop_bvar]
    exact hBody
  have hResult := FirstOrder.Derives.eq_subst (body := template)
    (FirstOrder.Derives.eq_symm hBound) hAt
  change Γ ⊢ₘ[T]
    (Formula.LevyBound.boundedForall set_levy_bound
      ((.bvar .here) : SetTerm [SetSort.set] free)
      (body.weakenBoundUnderTop SetSort.set)).instantiateTop left at hResult
  rw [Formula.LevyBound.boundedForall_instantiateTop_bvar] at hResult
  exact hResult

theorem bounded_forall_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (bound : SetOpenTerm free)
    (body : SetFormula [SetSort.set] free)
    (witness : SetOpenTerm free)
    (hForall : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound bound body)
    (hBound : Γ ⊢ₘ[T] witness ∈ₘ bound) :
    Γ ⊢ₘ[T] body.instantiateTop witness := by
  have hBoundAt :
      Γ ⊢ₘ[T]
        Formula.instantiateTop witness
          (set_levy_bound.membership
            (.bvar .here) (bound.weakenBound SetSort.set)) := by
    rw [instantiate_top_membership]
    exact hBound
  have hAt := FirstOrder.Derives.forall_elim
    (term := witness) hForall
  exact FirstOrder.Derives.imp_elim hAt hBoundAt

/-- 有界存在的成员 guard 与主体合取。 -/
def bounded_exists_body
    {free : SetContext}
    (bound : SetOpenTerm free)
    (body : SetFormula [SetSort.set] free) :
    SetFormula [SetSort.set] free :=
  set_levy_bound.membership
      ((.bvar .here) : SetTerm [SetSort.set] free)
      (bound.weakenBound SetSort.set) ∧ₘ body

/-- 规范打开有界存在主体时，成员 guard 直接落到最新 free 槽。 -/
theorem bounded_exists_body_openBoundTop
    {free : SetContext}
    (bound : SetOpenTerm free)
    (body : SetFormula [SetSort.set] free) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body bound body) =
      (FreshVariable.newest (σ := signature) (free := free) SetSort.set ∈ₘ
        bound.weakenFree SetSort.set) ∧ₘ
        Formula.openBoundTop (σ := signature) SetSort.set body := by
  have hBound :
      (bound.weakenBound SetSort.set).substituteMapped
          (VariableSubstitution.instantiateTop
            (FreshVariable.newest (σ := signature) (free := free)
              SetSort.set))
          (VariableSubstitution.of_renaming
            (VariableRenaming.weaken SetSort.set)) =
        bound.weakenFree SetSort.set := by
    simpa [Term.openBoundTop] using
      (Term.openBoundTop_weakenBound
        (σ := signature) SetSort.set bound)
  simp [bounded_exists_body, Formula.openBoundTop,
    Formula.LevyBound.membership, set_levy_bound,
    Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.instantiateTop, hBound]

@[simp] theorem bounded_exists_openBoundLast
    {free prefixContext : SetContext}
    (bound : SetTerm (prefixContext ++ [SetSort.set]) free)
    (body : SetFormula
      ((SetSort.set :: prefixContext) ++ [SetSort.set]) free) :
    Formula.openBoundLast prefixContext SetSort.set
        (Formula.LevyBound.boundedExists set_levy_bound bound body) =
      Formula.LevyBound.boundedExists set_levy_bound
        (Term.openBoundLast prefixContext SetSort.set bound)
        (Formula.openBoundLast (SetSort.set :: prefixContext)
          SetSort.set body) := by
  change
    Formula.openBoundLast prefixContext SetSort.set
        (Formula.existsE SetSort.set
          (set_levy_bound.membership
              ((.bvar .here) : SetTerm
                ((SetSort.set :: prefixContext) ++ [SetSort.set]) free)
              (bound.weakenBound SetSort.set) ∧ₘ body)) =
      Formula.existsE SetSort.set
        (set_levy_bound.membership
            ((.bvar .here) : SetTerm
              (SetSort.set :: prefixContext)
              (SetSort.set :: free))
            ((Term.openBoundLast prefixContext SetSort.set bound).weakenBound
              SetSort.set) ∧ₘ
          Formula.openBoundLast (SetSort.set :: prefixContext)
            SetSort.set body)
  rw [Formula.openBoundLast_existsE]
  simp only [Formula.openBoundLast, Formula.substituteMapped,
    Formula.LevyBound.membership, Arguments.substituteMapped,
    Term.substituteMapped]
  congr 2
  congr 1
  congr 2
  exact Term.openBoundLast_weakenBound SetSort.set prefixContext SetSort.set bound

/-- 有界存在消去：成员 guard 与公式体统一打开到规范 fresh 槽位。 -/
theorem bounded_exists_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (bound : SetOpenTerm free)
    (body : SetFormula [SetSort.set] free)
    (conclusion : SetOpenFormula free)
    (hExist : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound bound body)
    (hCase :
      Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body bound body) ::
        FreshVariable.extendContext
            SetSort.set Γ
        ⊢ₘ[T] conclusion.weakenFree SetSort.set) :
    Γ ⊢ₘ[T] conclusion := by
  let opened : SetOpenFormula (SetSort.set :: free) :=
    Formula.openBoundTop (σ := signature) SetSort.set
      (bounded_exists_body bound body)
  have hExist' : Γ ⊢ₘ[T] opened.existsFreeTop SetSort.set := by
    simpa [opened, bounded_exists_body,
      Formula.LevyBound.boundedExists] using hExist
  exact FirstOrder.Derives.exists_elim hExist' (by
    simpa [opened] using hCase)

/-- 标准有限界上的存在命题可由逐点否定拒绝，见证不预先假定为宿主 numeral。 -/
theorem bounded_exists_numeral_neg
    {T : SetTheory} (C : FiniteCore T)
    {free : SetContext} {Γ : Context signature free}
    (bound : Nat) (body : SetFormula [SetSort.set] free)
    (hBody : ∀ index, index < bound →
      Γ ⊢ₘ[T] ¬ₘ body.instantiateTop (numₘ(index))) :
    Γ ⊢ₘ[T] ¬ₘ Formula.LevyBound.boundedExists set_levy_bound (numₘ(bound)) body := by
  have hAll := bounded_forall_numeral_intro C bound (.neg body) hBody
  apply FirstOrder.Derives.neg_intro
  apply bounded_exists_elim (bound := numₘ(bound)) (body := body)
    (conclusion := Formula.falsum) (FirstOrder.Derives.assumption List.mem_cons_self)
  let Δ : Context signature (SetSort.set :: free) :=
    Formula.openBoundTop (σ := signature) SetSort.set (bounded_exists_body (numₘ(bound)) body) ::
    FreshVariable.extendContext SetSort.set
      (Formula.LevyBound.boundedExists set_levy_bound (numₘ(bound)) body :: Γ)
  have hOpened := FirstOrder.Derives.assumption (T := T) (Γ := Δ)
    (formula := Formula.openBoundTop (σ := signature) SetSort.set (bounded_exists_body (numₘ(bound)) body))
    List.mem_cons_self
  rw [bounded_exists_body_openBoundTop] at hOpened
  have hMember := FirstOrder.Derives.conj_elim_left hOpened
  have hInstance := FirstOrder.Derives.conj_elim_right hOpened
  have hAllAt : Δ ⊢ₘ[T] (Formula.LevyBound.boundedForall set_levy_bound
      (numₘ(bound)) (.neg body)).weakenFree SetSort.set :=
    FirstOrder.Derives.context_weaken_cons
      (fresh_context_weaken (FirstOrder.Derives.context_weaken_cons hAll))
  have hAllAt' : Δ ⊢ₘ[T] Formula.LevyBound.boundedForall set_levy_bound
      ((numₘ(bound) : SetOpenTerm free).weakenFree SetSort.set)
      ((Formula.neg body).weakenFree SetSort.set) := by
    simpa [Formula.LevyBound.boundedForall, set_levy_bound,
      Formula.LevyBound.membership] using hAllAt
  have hNeg := bounded_forall_elim _ _ _ hAllAt' hMember
  exact FirstOrder.Derives.neg_elim hInstance (by
    simpa [Δ, Formula.openBoundTop_eq_instantiateTop_weakenFree] using hNeg)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
