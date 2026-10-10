import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceGraph
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-!
# 对象有限集合的证明装配

列表只给出有限集合的构造数据；成员消去覆盖任意对象项，允许重复元素。
此层供有限递归轨迹复用，不向目标理论添加解释符号或公理。
-/
namespace YesMetaZFC.Automation.ObjectFiniteSet
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def term {bound free : SetContext} : List (SetTerm bound free) → SetTerm bound free
  | [] => ∅ₘ
  | head :: tail => {head}ₘ ∪ₘ term tail

@[simp] theorem term_substituteMapped {sb sf tb tf : SetContext}
    (elements : List (SetTerm sb sf))
    (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (term elements).substituteMapped bs fs =
      term (elements.map (fun element => element.substituteMapped bs fs)) := by
  induction elements <;> simp_all [term, Term.substituteMapped, Arguments.substituteMapped]

@[simp] theorem term_renameMapped {sb sf tb tf : SetContext}
    (elements : List (SetTerm sb sf)) (bs : VariableRenaming sb tb) (fs : VariableRenaming sf tf) :
    (term elements).renameMapped bs fs =
      term (elements.map (fun element => element.renameMapped bs fs)) := by
  induction elements <;> simp_all [term, Term.renameMapped, Arguments.renameMapped]

@[simp] theorem term_weakenFree {bound free : SetContext} (elements : List (SetTerm bound free)) :
    (term elements).weakenFree SetSort.set =
      term (elements.map (fun element => element.weakenFree SetSort.set)) :=
  term_renameMapped elements VariableRenaming.id (VariableRenaming.weaken SetSort.set)

@[simp] theorem term_weakenBound {bound free : SetContext} (elements : List (SetTerm bound free)) :
    (term elements).weakenBound SetSort.set =
      term (elements.map (fun element => element.weakenBound SetSort.set)) :=
  term_renameMapped elements (VariableRenaming.weaken SetSort.set) VariableRenaming.id

theorem cons_member_iff {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (head point : SetOpenTerm free) (tail : List (SetOpenTerm free)) :
    Derives T Γ ((point ∈ₘ term (head :: tail)) ↔ₘ
      ((point ≐ₘ head) ∨ₘ (point ∈ₘ term tail))) := by
  have hUnion := binary_union_spec_membership_iff {head}ₘ (term tail) _ point
    (FirstOrder.Derives.theory_weaken S.contains_binary_union
      (binary_union_term_spec_derives (Γ := Γ) {head}ₘ (term tail)))
  have hSingle := singleton_spec_membership_iff head {head}ₘ point
    (FirstOrder.Derives.theory_weaken
      (fun h => S.contains_ordered_pair (singleton_operator_theory_subset_ordered_pair_operator_theory h))
      (singleton_term_spec_derives (Γ := Γ) head))
  apply FirstOrder.Derives.iff_intro
  · have h := FirstOrder.Derives.iff_elim_left (FirstOrder.Derives.context_weaken_cons hUnion)
      (FirstOrder.Derives.assumption List.mem_cons_self)
    apply FirstOrder.Derives.disj_elim h
    · exact FirstOrder.Derives.disj_intro_left (FirstOrder.Derives.iff_elim_left
        (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons hSingle))
        (FirstOrder.Derives.assumption List.mem_cons_self))
    · exact FirstOrder.Derives.disj_intro_right (FirstOrder.Derives.assumption List.mem_cons_self)
  · apply FirstOrder.Derives.iff_elim_right (FirstOrder.Derives.context_weaken_cons hUnion)
    apply FirstOrder.Derives.disj_elim (FirstOrder.Derives.assumption List.mem_cons_self)
    · exact FirstOrder.Derives.disj_intro_left (FirstOrder.Derives.iff_elim_right
        (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons hSingle))
        (FirstOrder.Derives.assumption List.mem_cons_self))
    · exact FirstOrder.Derives.disj_intro_right (FirstOrder.Derives.assumption List.mem_cons_self)

theorem member_intro {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    {elements : List (SetOpenTerm free)} {element : SetOpenTerm free}
    (h : element ∈ elements) : Derives T Γ (element ∈ₘ term elements) := by
  induction elements with
  | nil => cases h
  | cons head tail ih =>
      apply FirstOrder.Derives.iff_elim_right (cons_member_iff S head element tail)
      rcases List.mem_cons.mp h with rfl | h
      · exact FirstOrder.Derives.disj_intro_left (Metatheory.Derives.equality_refl _)
      · exact FirstOrder.Derives.disj_intro_right (ih h)

theorem member_elim {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free)) (point : SetOpenTerm free) (conclusion : SetOpenFormula free)
    (hMember : Derives T Γ (point ∈ₘ term elements))
    (hCases : ∀ element, element ∈ elements → Derives T ((point ≐ₘ element) :: Γ) conclusion) :
    Derives T Γ conclusion := by
  induction elements generalizing Γ with
  | nil =>
      exact FirstOrder.Derives.falsum_elim (FirstOrder.Derives.neg_elim hMember
        (FirstOrder.Derives.theory_weaken S.contains_empty_set
          (empty_set_term_has_no_members (Γ := Γ) point)))
  | cons head tail ih =>
      apply FirstOrder.Derives.disj_elim
        (FirstOrder.Derives.iff_elim_left (cons_member_iff S head point tail) hMember)
      · exact hCases head (List.mem_cons_self)
      · apply ih (FirstOrder.Derives.assumption List.mem_cons_self)
        intro element hElement
        exact FirstOrder.Derives.context_weaken
          (by intro φ hφ; simp only [List.mem_cons] at hφ ⊢; exact hφ.elim Or.inl (Or.inr ∘ Or.inr))
          (hCases element (List.mem_cons_of_mem head hElement))

/-- 有限集合上的全称引入，将任意对象成员反演为给定列表的一个元素。 -/
theorem forall_intro {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free)) (body : SetFormula [SetSort.set] free)
    (hBody : ∀ element, element ∈ elements → Derives T Γ (body.instantiateTop element)) :
    Derives T Γ (Formula.LevyBound.boundedForall set_levy_bound (term elements) body) := by
  apply bounded_forall_intro
  let point : SetOpenTerm (SetSort.set :: free) := FreshVariable.newest (σ := signature) (free := free) SetSort.set
  let lifted := elements.map (fun element => element.weakenFree SetSort.set)
  let Δ := (point ∈ₘ term lifted) :: FreshVariable.extendContext SetSort.set Γ
  have hMember : Derives T Δ (point ∈ₘ term lifted) := FirstOrder.Derives.assumption List.mem_cons_self
  have hResult : Derives T Δ (Formula.openBoundTop (σ := signature) SetSort.set body) := by
    apply member_elim S lifted point _ hMember
    intro element hElement
    obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hElement
    have h := FirstOrder.Derives.context_weaken_cons (assumption := point ≐ₘ original.weakenFree SetSort.set)
      (FirstOrder.Derives.context_weaken_cons (assumption := point ∈ₘ term lifted)
        (fresh_context_weaken (hBody original hOriginal)))
    rw [← Formula.instantiateTop_weakenFree] at h
    have hTransport := FirstOrder.Derives.eq_subst
      (body := body.weakenFree SetSort.set)
      (FirstOrder.Derives.eq_symm (FirstOrder.Derives.assumption List.mem_cons_self)) h
    simpa only [Δ, Formula.openBoundTop_eq_instantiateTop_weakenFree] using hTransport
  simpa only [Δ, lifted, point, term_weakenFree] using hResult

theorem mem_powerSet {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free)) (bound : SetOpenTerm free)
    (hMember : ∀ element, element ∈ elements → Derives T Γ (element ∈ₘ bound)) :
    Derives T Γ (term elements ∈ₘ 𝒫ₘ(bound)) := by
  apply FirstOrder.Derives.iff_elim_right (FirstOrder.Derives.theory_weaken hPower
    (mem_power_set_term_iff_subset bound (term elements)))
  apply FirstOrder.Derives.iff_elim_right (FirstOrder.Derives.theory_weaken
    (fun h => hPower (Or.inr (Or.inr h))) (subset_definition_instance_derives (term elements) bound))
  have hAll : Derives T Γ (Formula.LevyBound.boundedForall set_levy_bound (term elements)
      ((.bvar .here) ∈ₘ bound.weakenBound SetSort.set)) := by
    apply forall_intro S elements
    intro element hElement
    simpa [Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
      Formula.substituteMapped, Arguments.substituteMapped, Term.substituteMapped,
      VariableSubstitution.instantiateTop] using hMember element hElement
  simpa [subset_condition, Formula.forallFreeTop, Formula.abstractFreeTop, Formula.substitute,
    Substitution.abstractFreeTop, Formula.substituteMapped, Arguments.substituteMapped,
    Term.substituteMapped, VariableSubstitution.abstractFreeTop,
    Formula.LevyBound.boundedForall, set_levy_bound, Formula.LevyBound.membership,
    Function.comp_def] using hAll

end YesMetaZFC.Automation.ObjectFiniteSet
