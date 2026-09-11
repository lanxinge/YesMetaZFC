import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Ordinal
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# ε-极小公理模式

ε-极小模式直接作用于内在类型谓词。谓词的元素槽由 `SetPredicate` 携带，模式
公理通过 `forall_close` 关闭其外部参数，不再维护 admissibility 或自由变量支持。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 成员反自反基础 -/

def membership_irreflexive_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (let element : SetOpenTerm [SetSort.set] := .fvar .here
     ¬ₘ (element ∈ₘ element))

def membership_irreflexive_theory : SetTheory :=
  Theory.singleton membership_irreflexive_axiom

theorem membership_irreflexive_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (term : SetOpenTerm free) :
    Γ ⊢ₘ[membership_irreflexive_theory]
      ¬ₘ (term ∈ₘ term) := by
  have hAxiom :
      ([] : Context signature []) ⊢ₘ[membership_irreflexive_theory]
        Formula.fromSentence membership_irreflexive_axiom :=
    FirstOrder.Derives.theory_axiom (by
      simp [membership_irreflexive_theory, Theory.singleton])
  have hInstance :
      Γ ⊢ₘ[membership_irreflexive_theory]
        ¬ₘ (term ∈ₘ term) := by
    apply Metatheory.Derives.forall_close_elim
      (Γ := Γ)
      (let element : SetOpenTerm [SetSort.set] := .fvar .here
       ¬ₘ (element ∈ₘ element))
      (fun _ => term :
        VariableSubstitution signature [SetSort.set] [] free)
      hAxiom
  simpa [membership_irreflexive_axiom, Formula.fromSentence,
    Formula.substituteFree, Substitution.free_map, Formula.substitute]
    using hInstance

/-! ## ε-极小模式 -/

namespace SetPredicate

def epsilon_minimal_core {free : SetContext}
    (predicate : SetPredicate free) : SetOpenFormula free :=
  let candidate := predicate.atNewest
  let member : SetOpenTerm (SetSort.set :: SetSort.set :: free) := .fvar .here
  let candidate' : SetOpenTerm (SetSort.set :: SetSort.set :: free) :=
    .fvar (.there .here)
  let memberPredicate := candidate.weakenFree SetSort.set
  let minimality :=
    ((member ∈ₘ candidate') ⟶ₘ (¬ₘ memberPredicate))
      |>.forallFreeTop SetSort.set
  let witness := (candidate ∧ₘ minimality)
  (candidate.existsFreeTop SetSort.set) ⟶ₘ
    (witness.existsFreeTop SetSort.set)

def epsilon_minimal_axiom {free : SetContext}
    (predicate : SetPredicate free) : SetSentence :=
  Metatheory.Formula.forall_close predicate.epsilon_minimal_core

end SetPredicate

/-! ## 理论组合与嵌入 -/

def epsilon_minimal_schema : SetTheory :=
  fun formula =>
    ∃ (free : SetContext) (predicate : SetPredicate free),
      formula = predicate.epsilon_minimal_axiom

def foundation_theory : SetTheory :=
  fun formula =>
    ordinal_natural_theory formula ∨ epsilon_minimal_schema formula

theorem epsilon_minimal_axiom_mem {free : SetContext}
    (predicate : SetPredicate free) :
    epsilon_minimal_schema predicate.epsilon_minimal_axiom :=
  ⟨free, predicate, rfl⟩

theorem epsilon_minimal_axiom_mem_foundation_theory
    {free : SetContext} (predicate : SetPredicate free) :
    foundation_theory predicate.epsilon_minimal_axiom :=
  Or.inr (epsilon_minimal_axiom_mem predicate)

derive_theory_subset ordinal_natural_theory ⊆ foundation_theory

theorem epsilon_minimal_schema_subset_foundation_theory
    {sentence : SetSentence}
    (hSentence : epsilon_minimal_schema sentence) :
    foundation_theory sentence := Or.inr hSentence

theorem epsilon_minimal_axiom_derives {free : SetContext}
    (predicate : SetPredicate free) :
    ⊢ₘ[foundation_theory] predicate.epsilon_minimal_axiom :=
  FirstOrder.Derives.theory_axiom
    (epsilon_minimal_axiom_mem_foundation_theory predicate)

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
