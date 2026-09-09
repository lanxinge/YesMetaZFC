import YesMetaZFC.Logic.FirstOrder.Derivation.QuantifierBlock
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceConstruction

/-!
# 有限图外延性

同域函数的逐点协议统一经图坐标传输；规范有限图只要求标准位置的值。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols Symbols

set_option autoImplicit false

/-! ## 函数图外延 -/

private theorem term_substituteMapped_weakenFree_cons
      {bound free : SetContext}
      (replacement : SetTerm bound (SetSort.set :: free))
      (term : SetTerm bound free) :
      (term.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
            (VariableRenaming.weaken SetSort.set))) =
        term.weakenFree SetSort.set := by
  rw [Term.substituteMapped_weakenFree_tail]
  simpa only [VariableSubstitution.cons, Term.weakenFree, Arguments.weakenFree,
    Term.rename, Arguments.rename, Renaming.weakenFree, Renaming.free] using
    Term.substituteMapped_of_renaming (VariableRenaming.weaken SetSort.set) term

private theorem arguments_substituteMapped_weakenFree_cons
      {bound free : SetContext} {sorts : List signature.SortSymbol}
      (replacement : SetTerm bound (SetSort.set :: free))
      (arguments : Arguments signature bound free sorts) :
      (arguments.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
              (VariableRenaming.weaken SetSort.set))) =
        arguments.weakenFree SetSort.set := by
  rw [Arguments.substituteMapped_weakenFree_tail]
  simpa only [VariableSubstitution.cons, Term.weakenFree, Arguments.weakenFree,
    Term.rename, Arguments.rename, Renaming.weakenFree, Renaming.free] using
    Arguments.substituteMapped_of_renaming (VariableRenaming.weaken SetSort.set) arguments

theorem function_equality_of_extensional_agreement
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeftFunction : Γ ⊢ₘ[T] is_function_formula left)
    (hRightFunction : Γ ⊢ₘ[T] is_function_formula right)
    (hAgreement : Γ ⊢ₘ[T]
      function_extensional_agreement left right) :
    Γ ⊢ₘ[T] left ≐ₘ right := by
  let Δ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Γ
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  have hLeftFunction' : Δ ⊢ₘ[T]
      is_function_formula (left.weakenFree SetSort.set) := by
    have hRenamed := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set) hLeftFunction
    simpa only [Δ, FreshVariable.extendContext, Formula.weakenFree,
      Formula.renameFree, Renaming.weakenFree] using! hRenamed
  have hRightFunction' : Δ ⊢ₘ[T]
      is_function_formula (right.weakenFree SetSort.set) := by
    have hRenamed := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set) hRightFunction
    simpa only [Δ, FreshVariable.extendContext, Formula.weakenFree,
      Formula.renameFree, Renaming.weakenFree] using! hRenamed
  have hDomainAgreement : Δ ⊢ₘ[T]
      domₘ(left.weakenFree SetSort.set) ≐ₘ
        domₘ(right.weakenFree SetSort.set) := by
    have hRenamed := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set)
        (FirstOrder.Derives.conj_elim_left hAgreement)
    simpa only [Δ, FreshVariable.extendContext, Formula.weakenFree,
      Formula.renameFree, Renaming.weakenFree] using! hRenamed
  have hPointwiseAt (input : SetOpenTerm (SetSort.set :: free)) :
      Δ ⊢ₘ[T]
        (input ∈ₘ domₘ(left.weakenFree SetSort.set)) ⟶ₘ
          ((left.weakenFree SetSort.set ·ₘ input) ≐ₘ
            (right.weakenFree SetSort.set ·ₘ input)) := by
    let ρ : VariableSubstitution signature free []
        (SetSort.set :: free) :=
      VariableSubstitution.of_renaming
        (bound := []) (VariableRenaming.weaken SetSort.set)
    let body : SetOpenFormula (SetSort.set :: free) :=
      (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set ∈ₘ
        domₘ(left.weakenFree SetSort.set)) ⟶ₘ
          ((left.weakenFree SetSort.set ·ₘ
              FreshVariable.newest
                (σ := signature) (free := free) SetSort.set) ≐ₘ
            (right.weakenFree SetSort.set ·ₘ
              FreshVariable.newest
                (σ := signature) (free := free) SetSort.set))
    let τ : VariableSubstitution signature (SetSort.set :: free) []
        (SetSort.set :: free) :=
      VariableSubstitution.cons input ρ
    have hUniversal := FirstOrder.Derives.free_substitution
      (T := T) ρ
        (FirstOrder.Derives.conj_elim_right hAgreement)
    rw [Formula.substituteFree_forallFreeTop] at hUniversal
    have hAt := FirstOrder.Derives.forall_elim input hUniversal
    rw [Formula.instantiateTop_abstractFreeTop] at hAt
    have hAt' : Context.substituteFree ρ Γ ⊢ₘ[T]
        Formula.instantiateFreeTop input
          (Formula.substituteFree
            (VariableSubstitution.liftFree SetSort.set ρ) body) := by
      simpa [body, function_extensional_agreement,
        FreshVariable.newest] using! hAt
    rw [Formula.instantiateFreeTop_substituteFree_liftFree] at hAt'
    have hAtContext : Δ ⊢ₘ[T] Formula.substituteFree τ body := by
      have hContext : Context.substituteFree ρ Γ = Δ := by
        unfold Context.substituteFree Δ FreshVariable.extendContext
        congr 1
        funext formula
        exact Formula.substituteFree_of_renaming _ formula
      rw [hContext] at hAt'
      exact hAt'
    simpa [τ, ρ, body, Context.substituteFree,
      Formula.substituteFree, Substitution.free_map,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId,
      VariableSubstitution.boundId, VariableSubstitution.weakenBound,
      VariableSubstitution.liftFree, FreshVariable.extendContext,
      FreshVariable.newest,
      term_substituteMapped_weakenFree_cons,
      arguments_substituteMapped_weakenFree_cons] using!
      hAtContext
  have hLeftCoordinateIff : Δ ⊢ₘ[T]
      (member ∈ₘ left.weakenFree SetSort.set) ↔ₘ
        function_graph_member_condition
          (left.weakenFree SetSort.set) member := by
    have hIff := FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application hSentence)
      (is_function_member_iff_coordinates
        (Γ := Δ) (left.weakenFree SetSort.set) member)
    exact FirstOrder.Derives.imp_elim hIff hLeftFunction'
  have hRightCoordinateIff : Δ ⊢ₘ[T]
      (member ∈ₘ right.weakenFree SetSort.set) ↔ₘ
        function_graph_member_condition
          (right.weakenFree SetSort.set) member := by
    have hIff := FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application hSentence)
      (is_function_member_iff_coordinates
        (Γ := Δ) (right.weakenFree SetSort.set) member)
    exact FirstOrder.Derives.imp_elim hIff hRightFunction'
  have hCoordinateAgreement : Δ ⊢ₘ[T]
      function_graph_member_condition (left.weakenFree SetSort.set) member ↔ₘ
        function_graph_member_condition (right.weakenFree SetSort.set) member := by
    have hDomains := membership_right_iff_of_equality
      (member)₀ₘ _ _ hDomainAgreement
    have hValues : Δ ⊢ₘ[T]
        ((member)₀ₘ ∈ₘ domₘ(left.weakenFree SetSort.set)) ⟶ₘ
          (((member)₁ₘ ≐ₘ (left.weakenFree SetSort.set ·ₘ (member)₀ₘ)) ↔ₘ
            ((member)₁ₘ ≐ₘ (right.weakenFree SetSort.set ·ₘ (member)₀ₘ))) := by
      apply FirstOrder.Derives.imp_intro
      exact Metatheory.Derives.equality_iff_of_equalities
        (FirstOrder.Derives.eq_refl _) (FirstOrder.Derives.imp_elim
          (FirstOrder.Derives.context_weaken_cons (hPointwiseAt (member)₀ₘ))
          (FirstOrder.Derives.assumption List.mem_cons_self))
    exact Metatheory.Derives.guarded_conj_congr_m hDomains hValues
  have hMembershipAgreement : Γ ⊢ₘ[T] membership_agreement left right := by
    unfold membership_agreement
    apply FirstOrder.Derives.forall_intro
    exact Metatheory.Derives.iff_trans hLeftCoordinateIff
      (Metatheory.Derives.iff_trans hCoordinateAgreement
        (Metatheory.Derives.iff_symm hRightCoordinateIff))
  have hExtensionality : Γ ⊢ₘ[T]
      extensionality_instance left right := by
    exact FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application
        (extensionality_theory_subset_function_application_theory hSentence))
      (extensionality_instance_derives (Γ := Γ) left right)
  simpa [extensionality_instance, agreement_to_equality] using
    FirstOrder.Derives.imp_elim hExtensionality hMembershipAgreement

/-- 任意同域函数只需给出标准位置的值，即等于该值列的规范有限图。 -/
theorem function_equality_of_finite_values
    {T : SetTheory} (C : FiniteCore T) (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (sequence : SetOpenTerm free) (elements : List (SetOpenTerm free))
    (hFunction : Γ ⊢ₘ[T] is_function_formula sequence)
    (hDomain : Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(elements.length))
    (hValues : ∀ index (hIndex : index < elements.length),
      Γ ⊢ₘ[T] (sequence ·ₘ numₘ(index)) ≐ₘ elements[index]) :
    Γ ⊢ₘ[T] sequence ≐ₘ standard_sequence elements := by
  let standard := standard_sequence elements
  have hPointwise : Γ ⊢ₘ[T] Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(sequence))
      ((sequence.weakenBound SetSort.set ·ₘ (.bvar .here)) ≐ₘ
        (standard.weakenBound SetSort.set ·ₘ (.bvar .here))) := by
    apply bounded_forall_of_bound_eq hDomain
    apply bounded_forall_numeral_intro C elements.length
    intro index hIndex
    have hAt := standard_sequence_getElem?_value (Γ := Γ) S
      (List.getElem?_eq_getElem hIndex)
    simpa only [Formula.instantiateTop_equal, Term.instantiateTop_app,
      Arguments.instantiateTop_cons, Arguments.instantiateTop_nil,
      Term.instantiateTop_weakenBound, Term.instantiateTop_bvar_here] using!
      FirstOrder.Derives.eq_trans (hValues index hIndex) (FirstOrder.Derives.eq_symm hAt)
  apply function_equality_of_extensional_agreement S sequence standard hFunction
    (standard_sequence_from_is_function S.toFiniteSequenceGraphSupport 0 elements)
  apply FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.eq_trans hDomain (FirstOrder.Derives.eq_symm
      (standard_sequence_domain_eq S.toFiniteSequenceGraphSupport)))
  simpa only [function_extensional_agreement, Formula.LevyBound.boundedForall,
    Formula.forallFreeTop, Formula.abstractFreeTop, Formula.substitute,
    Substitution.abstractFreeTop, Formula.substituteMapped,
    Term.substituteMapped_abstractFreeTop_weakenFree, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.abstractFreeTop,
    VariableSubstitution.abstractBound, set_levy_bound, Formula.LevyBound.membership] using! hPointwise

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
