import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuralSequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ArithmeticEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSpaceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingInversionDirect
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalArithmeticBound

/-!
# 结构码有限序列的直接构造

本模块把宿主列表中的对象项直接折叠为 Quine 结构码。轨迹项只保存每个前缀的
对象配数值，不再先把行值包进第二层自然数序列条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open IntrinsicPairing
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 直接构造所需的支撑合同 -/

/-- 直接结构码构造所需的有限序列、自然数与增长律合同。 -/
structure StructuralSequenceCodeSupport (T : SetTheory)
    extends FiniteSequenceSpaceSupport T where
  contains_infinity :
    ∀ {sentence}, infinity_theory sentence → T sentence
  contains_godel_pairing_core :
    ∀ {sentence}, godel_pairing_core_theory sentence → T sentence
  contains_natural_addition_bound :
    ∀ {sentence}, natural_addition_bound_theory sentence → T sentence

namespace StructuralSequenceCodeSupport

/-! ## 理论包含传递 -/

/-- 结构码支撑沿理论包含直接提升。 -/
theorem theory_weaken
    {T U : SetTheory}
    (S : StructuralSequenceCodeSupport T)
    (hTU : Theory.Extends U T) :
    StructuralSequenceCodeSupport U where
  toFiniteSequenceSpaceSupport :=
    S.toFiniteSequenceSpaceSupport.theory_weaken hTU
  contains_infinity := fun hSentence =>
    hTU (S.contains_infinity hSentence)
  contains_godel_pairing_core := fun hSentence =>
    hTU (S.contains_godel_pairing_core hSentence)
  contains_natural_addition_bound := fun hSentence =>
    hTU (S.contains_natural_addition_bound hSentence)

/-- 把直接结构码支撑投影为已有的有限算术求值支撑。 -/
theorem toArithmeticEvaluationSupport
    {T : SetTheory} (S : StructuralSequenceCodeSupport T) :
    ArithmeticEvaluationSupport T where
  toFiniteSequenceEvaluationSupport :=
    S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
  contains_infinity := S.contains_infinity
  contains_godel_pairing_core := S.contains_godel_pairing_core

theorem finite_numeral_mem_omega
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ :=
  S.toArithmeticEvaluationSupport.finite_numeral_mem_omega number

theorem successor_mem_omega
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (number : SetOpenTerm free)
    (hNumber : Γ ⊢ₘ[T] number ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] Sₘ(number) ∈ₘ ωₘ := by
  have hClosure := FirstOrder.Derives.theory_weaken
    S.contains_infinity
    (infinity_omega_inductive_condition_derives
      (free := free) (Γ := Γ))
  have hInstance := FirstOrder.Derives.forall_elim
    (term := number) (FirstOrder.Derives.conj_elim_right hClosure)
  simpa [infinity_condition] using!
    FirstOrder.Derives.imp_elim hInstance hNumber

theorem pairing_mem_omega
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeft : Γ ⊢ₘ[T] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[T] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] godel_pairₘ(left, right) ∈ₘ ωₘ := by
  exact godel_pairing_mem_omega_of_extends
    (show Theory.Extends T godel_pairing_core_theory from by
      intro sentence hSentence; apply S.contains_natural_addition_bound; theory_inclusion)
    left right hLeft hRight

theorem pairing_coordinates_lt
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeft : Γ ⊢ₘ[T] left ∈ₘ ωₘ)
    (hRight : Γ ⊢ₘ[T] right ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      (left ∈ₘ Sₘ(godel_pairₘ(left, right))) ∧ₘ
        (right ∈ₘ Sₘ(godel_pairₘ(left, right))) := by
  have hInstance := FirstOrder.Derives.theory_weaken
    (Γ := Γ)
    S.contains_natural_addition_bound
    (natural_godel_pairing_coordinate_bound_instance_derives left right)
  exact FirstOrder.Derives.imp_elim hInstance
    (FirstOrder.Derives.conj_intro hLeft hRight)

theorem natural_mem_trans
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (point middle upper : SetOpenTerm free)
    (hMiddleOmega : Γ ⊢ₘ[T] middle ∈ₘ ωₘ)
    (hUpperOmega : Γ ⊢ₘ[T] upper ∈ₘ ωₘ)
    (hLe : Γ ⊢ₘ[T] point ∈ₘ Sₘ(middle))
    (hLt : Γ ⊢ₘ[T] middle ∈ₘ upper) :
    Γ ⊢ₘ[T] point ∈ₘ upper := by
  have hInstance := FirstOrder.Derives.theory_weaken
    (Γ := Γ)
    S.contains_natural_addition_bound
    (natural_le_lt_transitivity_instance_derives point middle upper)
  exact FirstOrder.Derives.imp_elim hInstance <|
    FirstOrder.Derives.conj_intro hMiddleOmega <|
      FirstOrder.Derives.conj_intro hUpperOmega <|
        FirstOrder.Derives.conj_intro hLe hLt

theorem member_successor_self
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[T] source ∈ₘ Sₘ(source) := by
  exact FirstOrder.Derives.theory_weaken
    (Γ := Γ)
    (fun hSentence => S.toArithmeticSupport.contains_successor hSentence)
    (mem_successor_self (Γ := Γ) source)

theorem member_successor_of_member
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source element : SetOpenTerm free)
    (hMember : Γ ⊢ₘ[T] element ∈ₘ source) :
    Γ ⊢ₘ[T] element ∈ₘ Sₘ(source) := by
  have hImp := FirstOrder.Derives.theory_weaken
    (Γ := Γ)
    (fun hSentence => S.toArithmeticSupport.contains_successor hSentence)
    (mem_successor_of_mem (Γ := Γ) source element)
  exact FirstOrder.Derives.imp_elim hImp hMember

theorem natural_mem_successor_trans
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (point middle upper : SetOpenTerm free)
    (hMiddleOmega : Γ ⊢ₘ[T] middle ∈ₘ ωₘ)
    (hUpperOmega : Γ ⊢ₘ[T] upper ∈ₘ ωₘ)
    (hPointLe : Γ ⊢ₘ[T] point ∈ₘ Sₘ(middle))
    (hMiddleLe : Γ ⊢ₘ[T] middle ∈ₘ Sₘ(upper)) :
    Γ ⊢ₘ[T] point ∈ₘ Sₘ(upper) := by
  have hMembershipIff : Γ ⊢ₘ[T]
      (middle ∈ₘ Sₘ(upper)) ↔ₘ
        ((middle ≐ₘ upper) ∨ₘ (middle ∈ₘ upper)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.toArithmeticSupport.contains_successor hSentence)
      (successor_term_membership_iff (Γ := Γ) upper middle)
  have hCases : Γ ⊢ₘ[T]
      (middle ≐ₘ upper) ∨ₘ (middle ∈ₘ upper) :=
    FirstOrder.Derives.iff_elim_left hMembershipIff hMiddleLe
  apply FirstOrder.Derives.disj_elim hCases
  · let Δ : Context signature free :=
      (middle ≐ₘ upper) :: Γ
    have hEquality : Δ ⊢ₘ[T] middle ≐ₘ upper :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSuccessorEquality : Δ ⊢ₘ[T]
        Sₘ(middle) ≐ₘ Sₘ(upper) :=
      successor_term_congr_of_equality middle upper hEquality
    have hPointLe' : Δ ⊢ₘ[T] point ∈ₘ Sₘ(middle) :=
      FirstOrder.Derives.context_weaken_cons hPointLe
    exact FirstOrder.Derives.iff_elim_left
      (membership_right_iff_of_equality
        point (Sₘ(middle)) (Sₘ(upper)) hSuccessorEquality)
      hPointLe'
  · let Δ : Context signature free :=
      (middle ∈ₘ upper) :: Γ
    have hStrict : Δ ⊢ₘ[T] middle ∈ₘ upper :=
      FirstOrder.Derives.assumption (by simp [Δ])
    exact member_successor_of_member S upper point
      (natural_mem_trans S point middle upper
        (FirstOrder.Derives.context_weaken_cons hMiddleOmega)
        (FirstOrder.Derives.context_weaken_cons hUpperOmega)
        (FirstOrder.Derives.context_weaken_cons hPointLe)
        hStrict)

end StructuralSequenceCodeSupport

theorem omega_nonempty_of_numeral_member
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (number : Nat)
    (hNumber : Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ := by
  have hImp : Γ ⊢ₘ[T]
      (numₘ(number) ∈ₘ (ωₘ : SetOpenTerm free)) ⟶ₘ
        (ωₘ ≠ₘ (∅ₘ : SetOpenTerm free)) :=
    FirstOrder.Derives.theory_weaken
      (fun hSentence => S.toArithmeticSupport.contains_empty_set hSentence)
      (member_implies_set_nonempty
        (Γ := Γ)
        (numₘ(number) : SetOpenTerm free)
        (ωₘ : SetOpenTerm free))
  exact FirstOrder.Derives.imp_elim hImp hNumber

private theorem structural_sequence_code_row_condition_instantiateTop
    {free : SetContext}
    (sequence trace code : SetOpenTerm free)
    (index : Nat) :
    Formula.instantiateTop (numₘ(index))
        (object_sequence_code_row_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here)) =
      object_sequence_code_row_condition sequence trace code (numₘ(index)) := by
  simp [object_sequence_code_row_condition,
    object_sequence_code_step_condition,
    Formula.instantiateTop, Substitution.instantiateTop,
    Formula.substitute, Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.instantiateTop]

private theorem structural_sequence_code_trace_body_instantiateTop
    {free : SetContext}
    (sequence code trace : SetOpenTerm free) :
    Formula.instantiateTop trace
        (object_sequence_code_trace_body
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here)) =
      object_sequence_code_trace_body sequence code trace := by
  simp [object_sequence_code_trace_body,
    object_sequence_code_pointwise_condition,
    object_sequence_code_row_condition,
    object_sequence_code_step_condition, sequence_trace_code_bound,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    Formula.instantiateTop, Substitution.instantiateTop,
    Formula.substitute, Formula.substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.instantiateTop, VariableSubstitution.liftBound]

/-! ## 宿主递归 -/

/-- 一次直接结构配数递推。 -/
def object_sequence_code_step {free : SetContext}
    (accumulator element : SetOpenTerm free) : SetOpenTerm free :=
  Sₘ(godel_pairₘ(accumulator, element))

/-- 从任意对象初值开始的直接结构配数折叠。 -/
def object_sequence_code_from {free : SetContext}
    (seed : SetOpenTerm free) : List (SetOpenTerm free) → SetOpenTerm free
  | [] => seed
  | element :: rest =>
      object_sequence_code_from
        (object_sequence_code_step seed element) rest

/-- 零初值的直接结构配数值。 -/
def object_sequence_code_value {free : SetContext}
    (elements : List (SetOpenTerm free)) : SetOpenTerm free :=
  godel_pairₘ(
    object_sequence_code_from (numₘ(0)) elements,
    numₘ(elements.length))

/-- 从任意初值开始的直接结构配数轨迹。 -/
def object_sequence_code_trace_from {free : SetContext}
    (seed : SetOpenTerm free) : List (SetOpenTerm free) →
      List (SetOpenTerm free)
  | [] => [seed]
  | element :: rest =>
      seed :: object_sequence_code_trace_from
        (object_sequence_code_step seed element) rest

/-- 零初值的直接结构配数轨迹。 -/
def object_sequence_code_trace {free : SetContext}
    (elements : List (SetOpenTerm free)) : List (SetOpenTerm free) :=
  object_sequence_code_trace_from (numₘ(0)) elements

/-- 对象项编码的原递归就是列表折叠，不展开对象项的语法。 -/
theorem object_sequence_code_from_eq_foldl
    {free : SetContext} (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free)) :
    object_sequence_code_from seed elements =
      elements.foldl object_sequence_code_step seed := by
  induction elements generalizing seed with
  | nil => rfl
  | cons head tail ih => exact ih _

/-- 自然数与对象项轨迹共用列表扫描的结构定理。 -/
theorem object_sequence_code_trace_from_eq_scanl
    {free : SetContext} (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free)) :
    object_sequence_code_trace_from seed elements =
      elements.scanl object_sequence_code_step seed := by
  induction elements generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      simp only [object_sequence_code_trace_from, List.scanl_cons, ih]

@[simp] theorem object_sequence_code_from_nil
    {free : SetContext} (seed : SetOpenTerm free) :
    object_sequence_code_from seed [] = seed :=
  rfl

@[simp] theorem object_sequence_code_from_cons
    {free : SetContext} (seed : SetOpenTerm free)
    (element : SetOpenTerm free)
    (rest : List (SetOpenTerm free)) :
    object_sequence_code_from seed (element :: rest) =
      object_sequence_code_from
        (object_sequence_code_step seed element) rest :=
  rfl

@[simp] theorem object_sequence_code_value_nil
    {free : SetContext} :
    object_sequence_code_value ([] : List (SetOpenTerm free)) =
      godel_pairₘ(numₘ(0), numₘ(0)) :=
  rfl

@[simp] theorem object_sequence_code_from_append_singleton
    {free : SetContext} (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (element : SetOpenTerm free) :
    object_sequence_code_from seed (elements ++ [element]) =
      object_sequence_code_step
        (object_sequence_code_from seed elements) element := by
  simp only [object_sequence_code_from_eq_foldl, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

@[simp] theorem object_sequence_code_trace_from_length
    {free : SetContext} (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free)) :
    (object_sequence_code_trace_from seed elements).length =
      elements.length + 1 := by
  rw [object_sequence_code_trace_from_eq_scanl, List.length_scanl]

@[simp] theorem object_sequence_code_trace_length
    {free : SetContext} (elements : List (SetOpenTerm free)) :
    (object_sequence_code_trace elements).length =
      elements.length + 1 := by
  simp [object_sequence_code_trace]

theorem object_sequence_code_trace_from_getElem?
    {free : SetContext} (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free)) (index : Nat)
    (hIndex : index ≤ elements.length) :
    (object_sequence_code_trace_from seed elements)[index]? =
      some (object_sequence_code_from seed (elements.take index)) := by
  simp only [object_sequence_code_trace_from_eq_scanl, List.getElem?_scanl,
    hIndex, if_true, object_sequence_code_from_eq_foldl]

theorem object_sequence_code_trace_from_last
    {free : SetContext} (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free)) :
    (object_sequence_code_trace_from seed elements)[elements.length]? =
      some (object_sequence_code_from seed elements) := by
  simpa using object_sequence_code_trace_from_getElem?
    seed elements elements.length (by omega)

theorem object_sequence_code_trace_last
    {free : SetContext} (elements : List (SetOpenTerm free)) :
    (object_sequence_code_trace elements)[elements.length]? =
      some (object_sequence_code_from (numₘ(0)) elements) := by
  simpa [object_sequence_code_trace] using
    object_sequence_code_trace_from_last (numₘ(0)) elements

theorem object_sequence_code_trace_from_step
    {free : SetContext} (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free)) (index : Nat)
    (element : SetOpenTerm free)
    (hElement : elements[index]? = some element) :
    (object_sequence_code_trace_from seed elements)[index + 1]? =
      some (object_sequence_code_step
        (object_sequence_code_from seed (elements.take index)) element) := by
  obtain ⟨hIndex, _⟩ := List.getElem_of_getElem? hElement
  rw [object_sequence_code_trace_from_eq_scanl, List.getElem?_succ_scanl,
    ← object_sequence_code_trace_from_eq_scanl,
    object_sequence_code_trace_from_getElem? seed elements index
      (Nat.le_of_lt hIndex), hElement]
  rfl

/-! ## 对象层递归不变量 -/

theorem object_sequence_code_from_mem_omega
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (hSeed : Γ ⊢ₘ[T] seed ∈ₘ ωₘ)
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] object_sequence_code_from seed elements ∈ₘ ωₘ := by
  rw [object_sequence_code_from_eq_foldl]
  apply List.foldlRecOn (motive := fun value => Γ ⊢ₘ[T] value ∈ₘ ωₘ)
    elements object_sequence_code_step hSeed
  intro value hValue element hElement
  exact S.successor_mem_omega _ (S.pairing_mem_omega _ _ hValue
    (hElements element hElement))

theorem object_sequence_code_trace_from_mem_omega
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (hSeed : Γ ⊢ₘ[T] seed ∈ₘ ωₘ)
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ)
    {value : SetOpenTerm free}
    (hValue : value ∈ object_sequence_code_trace_from seed elements) :
    Γ ⊢ₘ[T] value ∈ₘ ωₘ := by
  rcases List.mem_iff_getElem?.mp hValue with ⟨index, hGet⟩
  have hIndex : index ≤ elements.length := by
    obtain ⟨hLt, _⟩ := List.getElem_of_getElem? hGet
    simpa only [object_sequence_code_trace_from_length, Nat.lt_add_one_iff] using hLt
  have hValueEq := Option.some.inj
    (hGet.symm.trans (object_sequence_code_trace_from_getElem? seed elements index hIndex))
  rw [hValueEq]
  exact object_sequence_code_from_mem_omega S seed (elements.take index) hSeed
    (fun element hElement => hElements element (List.mem_of_mem_take hElement))

/-- 拼接只延续已有折叠状态。 -/
theorem object_sequence_code_from_append
    {free : SetContext} (seed : SetOpenTerm free)
    (left right : List (SetOpenTerm free)) :
    object_sequence_code_from seed (left ++ right) =
      object_sequence_code_from (object_sequence_code_from seed left) right := by
  simp only [object_sequence_code_from_eq_foldl, List.foldl_append]

/-- 同时保持自然数域与初值下界；后续前缀证明只消费这个折叠不变量。 -/
theorem object_sequence_code_seed_mem_successor
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (seed : SetOpenTerm free) (elements : List (SetOpenTerm free))
    (hSeed : Γ ⊢ₘ[T] seed ∈ₘ ωₘ)
    (hElements : ∀ element, element ∈ elements → Γ ⊢ₘ[T] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[T] seed ∈ₘ Sₘ(object_sequence_code_from seed elements) := by
  have hInvariant := List.foldlRecOn
    (motive := fun value => (Γ ⊢ₘ[T] value ∈ₘ ωₘ) ∧ (Γ ⊢ₘ[T] seed ∈ₘ Sₘ(value)))
    elements object_sequence_code_step ⟨hSeed, S.member_successor_self seed⟩
    (by
      intro value hValue element hElement
      have hMember := hElements element hElement
      have hNext := S.successor_mem_omega _ (S.pairing_mem_omega _ _ hValue.1 hMember)
      exact ⟨hNext, S.member_successor_of_member _ _
        (S.natural_mem_trans _ _ _ hValue.1 hNext hValue.2
          (FirstOrder.Derives.conj_elim_left (S.pairing_coordinates_lt _ _ hValue.1 hMember)))⟩)
  simpa only [object_sequence_code_from_eq_foldl] using hInvariant.2

theorem object_sequence_code_point_mem_successor_from
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (point : SetOpenTerm free)
    (hSeed : Γ ⊢ₘ[T] seed ∈ₘ ωₘ)
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ)
    (hPoint : Γ ⊢ₘ[T] point ∈ₘ seed) :
    Γ ⊢ₘ[T]
      point ∈ₘ Sₘ(object_sequence_code_from seed elements) := by
  exact S.natural_mem_successor_trans point seed _ hSeed
    (object_sequence_code_from_mem_omega S seed elements hSeed hElements)
    (S.member_successor_of_member seed point hPoint)
    (object_sequence_code_seed_mem_successor S seed elements hSeed hElements)

theorem object_sequence_code_element_mem_successor
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (index : Nat) (element : SetOpenTerm free)
    (hElement : elements[index]? = some element)
    (hSeed : Γ ⊢ₘ[T] seed ∈ₘ ωₘ)
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      element ∈ₘ Sₘ(object_sequence_code_from seed elements) := by
  induction elements generalizing seed index element with
  | nil =>
      simp at hElement
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hElement
          subst element
          have hHead : Γ ⊢ₘ[T] head ∈ₘ ωₘ :=
            hElements head (by simp)
          have hPair : Γ ⊢ₘ[T]
              godel_pairₘ(seed, head) ∈ₘ ωₘ :=
            S.pairing_mem_omega seed head hSeed hHead
          have hStepOmega : Γ ⊢ₘ[T]
              object_sequence_code_step seed head ∈ₘ ωₘ := by
            simpa [object_sequence_code_step] using
              S.successor_mem_omega (godel_pairₘ(seed, head)) hPair
          have hCoordinates := S.pairing_coordinates_lt
            seed head hSeed hHead
          have hHeadStep : Γ ⊢ₘ[T]
              head ∈ₘ object_sequence_code_step seed head := by
            simpa [object_sequence_code_step] using
              FirstOrder.Derives.conj_elim_right hCoordinates
          simpa [object_sequence_code_from] using
            object_sequence_code_point_mem_successor_from S
              (object_sequence_code_step seed head) tail head
              hStepOmega (by
                intro value hValue
                exact hElements value (by simp [hValue])) hHeadStep
      | succ index =>
          simp only [List.getElem?_cons_succ] at hElement
          simpa [object_sequence_code_from] using
            ih (seed := object_sequence_code_step seed head)
              (index := index) (element := element) hElement
              (by
                have hHead : Γ ⊢ₘ[T] head ∈ₘ ωₘ :=
                  hElements head (by simp)
                have hPair := S.pairing_mem_omega seed head hSeed hHead
                simpa [object_sequence_code_step] using
                  S.successor_mem_omega
                    (godel_pairₘ(seed, head)) hPair)
              (by
                intro value hValue
                exact hElements value (by simp [hValue]))

theorem object_sequence_code_prefix_mem_successor
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (index : Nat) (hIndex : index ≤ elements.length)
    (hSeed : Γ ⊢ₘ[T] seed ∈ₘ ωₘ)
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      object_sequence_code_from seed (elements.take index) ∈ₘ
        Sₘ(object_sequence_code_from seed elements) := by
  have hPrefix := object_sequence_code_from_mem_omega S seed (elements.take index)
    hSeed (fun element hElement => hElements element (List.mem_of_mem_take hElement))
  have hBound := object_sequence_code_seed_mem_successor S
    (object_sequence_code_from seed (elements.take index))
    (elements.drop (elements.take index).length)
    hPrefix (fun element hElement => hElements element (List.mem_of_mem_drop hElement))
  rw [List.length_take, Nat.min_eq_left hIndex,
    ← object_sequence_code_from_append, List.take_append_drop] at hBound
  exact hBound

theorem object_sequence_code_terminal_mem_omega
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      object_sequence_code_value elements ∈ₘ ωₘ := by
  simpa [object_sequence_code_value] using
    S.pairing_mem_omega
      (object_sequence_code_from (numₘ(0)) elements)
      (numₘ(elements.length))
      (object_sequence_code_from_mem_omega S
        (numₘ(0)) elements (S.finite_numeral_mem_omega 0) hElements)
      (S.finite_numeral_mem_omega elements.length)

theorem object_sequence_code_terminal_domain_bound
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      (numₘ(elements.length) : SetOpenTerm free) ∈ₘ
        Sₘ(object_sequence_code_value elements) := by
  have hCoordinates := S.pairing_coordinates_lt
    (object_sequence_code_from (numₘ(0)) elements)
    (numₘ(elements.length))
    (object_sequence_code_from_mem_omega S
      (numₘ(0)) elements (S.finite_numeral_mem_omega 0) hElements)
    (S.finite_numeral_mem_omega elements.length)
  simpa [object_sequence_code_value] using
    FirstOrder.Derives.conj_elim_right hCoordinates

theorem object_sequence_code_point_mem_terminal
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (seed : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (point : SetOpenTerm free)
    (hSeed : Γ ⊢ₘ[T] seed ∈ₘ ωₘ)
    (hElements : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ)
    (hPoint : Γ ⊢ₘ[T]
      point ∈ₘ Sₘ(object_sequence_code_from seed elements)) :
    Γ ⊢ₘ[T]
      point ∈ₘ Sₘ(godel_pairₘ(
        object_sequence_code_from seed elements,
        numₘ(elements.length))) := by
  have hFinalOmega : Γ ⊢ₘ[T]
      object_sequence_code_from seed elements ∈ₘ ωₘ :=
    object_sequence_code_from_mem_omega S seed elements hSeed hElements
  have hLengthOmega : Γ ⊢ₘ[T]
      (numₘ(elements.length) : SetOpenTerm free) ∈ₘ ωₘ :=
    S.finite_numeral_mem_omega elements.length
  have hTerminalOmega : Γ ⊢ₘ[T]
      godel_pairₘ(object_sequence_code_from seed elements,
        numₘ(elements.length)) ∈ₘ ωₘ :=
    S.pairing_mem_omega
      (object_sequence_code_from seed elements)
      (numₘ(elements.length)) hFinalOmega hLengthOmega
  have hFinalMember : Γ ⊢ₘ[T]
      object_sequence_code_from seed elements ∈ₘ
        Sₘ(godel_pairₘ(object_sequence_code_from seed elements,
          numₘ(elements.length))) := by
    exact FirstOrder.Derives.conj_elim_left <|
      S.pairing_coordinates_lt
        (object_sequence_code_from seed elements)
        (numₘ(elements.length)) hFinalOmega hLengthOmega
  exact StructuralSequenceCodeSupport.natural_mem_successor_trans S point
    (object_sequence_code_from seed elements)
    (godel_pairₘ(object_sequence_code_from seed elements,
      numₘ(elements.length)))
    hFinalOmega hTerminalOmega hPoint hFinalMember

theorem standard_object_sequence_value
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (index : Nat) (hIndex : index < elements.length) :
    Γ ⊢ₘ[T]
      (standard_sequence elements ·ₘ numₘ(index)) ≐ₘ (elements[index]'hIndex) := by
  exact standard_sequence_getElem?_value S (List.getElem?_eq_getElem hIndex)

theorem standard_object_sequence_trace_value
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (index : Nat) (hIndex : index ≤ elements.length) :
    Γ ⊢ₘ[T]
      (standard_sequence (object_sequence_code_trace elements) ·ₘ
        numₘ(index)) ≐ₘ
        object_sequence_code_from (numₘ(0)) (elements.take index) := by
  exact standard_sequence_getElem?_value S
    (object_sequence_code_trace_from_getElem? (numₘ(0)) elements index hIndex)

theorem standard_object_sequence_trace_step
    {T : SetTheory} (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (elements : List (SetOpenTerm free))
    (index : Nat) (hIndex : index < elements.length) :
    Γ ⊢ₘ[T]
      (standard_sequence (object_sequence_code_trace elements) ·ₘ
        Sₘ(numₘ(index))) ≐ₘ
        object_sequence_code_step
          (object_sequence_code_from (numₘ(0)) (elements.take index))
          (elements[index]'hIndex) := by
  simpa only [object_sequence_code_trace, finite_numeral_term, successor_term] using
    (standard_sequence_getElem?_value (Γ := Γ) S
      (object_sequence_code_trace_from_step (numₘ(0)) elements index _
        (List.getElem?_eq_getElem hIndex)))

/-- 标准对象项列表直接满足结构码有限序列条件。 -/
theorem object_sequence_code_condition_intro_standard
    {T : SetTheory} (S : StructuralSequenceCodeSupport T)
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (hSourceNonempty : Γ ⊢ₘ[T] source ≠ₘ ∅ₘ)
    (hElementMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ source)
    (hElementOmega : ∀ element, element ∈ elements →
      Γ ⊢ₘ[T] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      object_sequence_code_condition source
        (standard_sequence elements)
        (object_sequence_code_value elements) := by
  let sequence : SetOpenTerm free := standard_sequence elements
  let code : SetOpenTerm free := object_sequence_code_value elements
  let trace : SetOpenTerm free :=
    standard_sequence (object_sequence_code_trace elements)
  have hSequenceSpace : Γ ⊢ₘ[T]
      sequence ∈ₘ seq_spaceₘ(source) := by
    simpa [sequence] using
      standard_sequence_mem_sequence_space
        S.toFiniteSequenceSpaceSupport elements source
        (S.finite_numeral_mem_omega elements.length)
        hSourceNonempty hElementMember
  have hCodeOmega : Γ ⊢ₘ[T] code ∈ₘ ωₘ := by
    simpa [code] using
      object_sequence_code_terminal_mem_omega S elements hElementOmega
  have hSequenceDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(elements.length) := by
    simpa [sequence] using
      standard_sequence_domain_eq
        (Γ := Γ) S.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport
        (elements := elements)
  have hDomainBound : Γ ⊢ₘ[T]
      sequence_domain_code_bound sequence code := by
    have hLengthMember : Γ ⊢ₘ[T]
        (numₘ(elements.length) : SetOpenTerm free) ∈ₘ Sₘ(code) := by
      simpa [code] using
        object_sequence_code_terminal_domain_bound S elements hElementOmega
    exact FirstOrder.Derives.iff_elim_right
      (membership_left_iff_of_equality
        (domₘ(sequence)) (numₘ(elements.length)) (Sₘ(code))
        hSequenceDomain) hLengthMember
  have hTraceSpace : Γ ⊢ₘ[T]
      trace ∈ₘ seq_spaceₘ(ωₘ) := by
    have hTraceLengthOmega : Γ ⊢ₘ[T]
        (numₘ((object_sequence_code_trace elements).length) :
          SetOpenTerm free) ∈ₘ ωₘ :=
      S.finite_numeral_mem_omega (object_sequence_code_trace elements).length
    have hTraceMember : ∀ value,
        value ∈ object_sequence_code_trace elements →
          Γ ⊢ₘ[T] value ∈ₘ ωₘ := by
      intro value hValue
      exact object_sequence_code_trace_from_mem_omega S
        (numₘ(0)) elements (S.finite_numeral_mem_omega 0)
        hElementOmega hValue
    have hSpace := standard_sequence_mem_sequence_space
      S.toFiniteSequenceSpaceSupport
      (object_sequence_code_trace elements) ωₘ hTraceLengthOmega
      (omega_nonempty_of_numeral_member S 0
        (S.finite_numeral_mem_omega 0)) hTraceMember
    simpa [trace] using hSpace
  have hTraceDomain : Γ ⊢ₘ[T]
      domₘ(trace) ≐ₘ Sₘ(domₘ(sequence)) :=
    standard_sequence_trace_domain
      S.toFiniteSequenceSpaceSupport.toFiniteSequenceGraphSupport
      elements (object_sequence_code_trace elements)
      (object_sequence_code_trace_length elements)
  have hTraceBound : Γ ⊢ₘ[T]
      sequence_trace_code_bound trace code := by
    apply standard_sequence_values_mem
      (ArithmeticSupport.finite_core S.toFiniteSequenceSpaceSupport.toArithmeticSupport)
      S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
      (object_sequence_code_trace elements) (Sₘ(code))
    intro value hValue
    rcases List.mem_iff_getElem?.mp hValue with ⟨index, hGet⟩
    have hIndex : index ≤ elements.length := by
      obtain ⟨hLt, _⟩ := List.getElem_of_getElem? hGet
      simpa only [object_sequence_code_trace_length, Nat.lt_add_one_iff] using hLt
    have hValueEq := Option.some.inj (hGet.symm.trans
      (object_sequence_code_trace_from_getElem? (numₘ(0)) elements index hIndex))
    rw [hValueEq]
    exact object_sequence_code_point_mem_terminal S (numₘ(0)) elements _
      (S.finite_numeral_mem_omega 0) hElementOmega
      (object_sequence_code_prefix_mem_successor S (numₘ(0)) elements index hIndex
        (S.finite_numeral_mem_omega 0) hElementOmega)
  have hZero : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(0) ≐ₘ numₘ(0) := by
    apply standard_sequence_getElem?_value
      S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
    cases elements <;> rfl
  let rowBody : SetFormula [SetSort.set] free :=
    object_sequence_code_row_condition
      (sequence.weakenBound SetSort.set)
      (trace.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here)
  have hRowsNumeral : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (numₘ(elements.length)) rowBody :=
    bounded_forall_numeral_intro
      (ArithmeticSupport.finite_core
        S.toFiniteSequenceSpaceSupport.toArithmeticSupport)
      elements.length rowBody (by
        intro index hIndex
        have hElementGet : elements[index]? = some (elements[index]'hIndex) :=
          List.getElem?_eq_getElem hIndex
        have hSequenceValue := standard_object_sequence_value
          (Γ := Γ)
          S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
          elements index hIndex
        have hElementOmegaAt := hElementOmega (elements[index]'hIndex)
          (List.getElem_mem hIndex)
        have hRowBoundRaw := object_sequence_code_element_mem_successor S
          (numₘ(0)) elements index (elements[index]'hIndex) hElementGet
          (S.finite_numeral_mem_omega 0) hElementOmega
        have hRowBound := object_sequence_code_point_mem_terminal S
          (numₘ(0)) elements (elements[index]'hIndex)
          (S.finite_numeral_mem_omega 0) hElementOmega hRowBoundRaw
        have hRowMember : Γ ⊢ₘ[T]
            (sequence ·ₘ numₘ(index)) ∈ₘ Sₘ(code) :=
          FirstOrder.Derives.iff_elim_right
            (membership_left_iff_of_equality
              (sequence ·ₘ numₘ(index)) (elements[index]'hIndex) (Sₘ(code))
              hSequenceValue)
            (by simpa [code] using! hRowBound)
        have hTraceCurrent := standard_object_sequence_trace_value
          (Γ := Γ)
          S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
          elements index (Nat.le_of_lt hIndex)
        have hTraceStep := standard_object_sequence_trace_step
          (Γ := Γ)
          S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
          elements index hIndex
        have hPair := pair_congr_of_equalities
          (trace ·ₘ numₘ(index))
          (object_sequence_code_from (numₘ(0)) (elements.take index))
          (sequence ·ₘ numₘ(index)) (elements[index]'hIndex)
          hTraceCurrent hSequenceValue
        have hSuccessor := successor_term_congr_of_equality
          (godel_pairₘ(trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)))
          (godel_pairₘ(
            object_sequence_code_from (numₘ(0)) (elements.take index),
            (elements[index]'hIndex))) hPair
        have hStep : Γ ⊢ₘ[T]
            object_sequence_code_step_condition
              sequence trace (numₘ(index))
              (sequence ·ₘ numₘ(index)) := by
          apply FirstOrder.Derives.conj_intro
          · exact FirstOrder.Derives.iff_elim_right
              (membership_left_iff_of_equality
                (sequence ·ₘ numₘ(index)) (elements[index]'hIndex) ωₘ
                hSequenceValue) hElementOmegaAt
          · exact Metatheory.Derives.equality_trans hTraceStep
              (Metatheory.Derives.equality_symm hSuccessor)
        have hRow := FirstOrder.Derives.conj_intro hRowMember hStep
        change Γ ⊢ₘ[T] Formula.instantiateTop (numₘ(index)) rowBody
        rw [structural_sequence_code_row_condition_instantiateTop]
        simpa [rowBody, sequence, trace, code] using! hRow)
  have hRows : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (domₘ(sequence)) rowBody :=
    bounded_forall_of_bound_eq hSequenceDomain hRowsNumeral
  have hPointwise : Γ ⊢ₘ[T]
      object_sequence_code_pointwise_condition sequence trace code := by
    change Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall set_levy_bound
        (domₘ(sequence))
        (object_sequence_code_row_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))
    exact hRows
  have hTraceFinal : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(elements.length) ≐ₘ
        object_sequence_code_from (numₘ(0)) elements :=
    by simpa [trace, List.take_length] using
      (standard_object_sequence_trace_value
      (Γ := Γ)
      S.toFiniteSequenceSpaceSupport.toFiniteSequenceEvaluationSupport
      elements elements.length (by omega))
  have hTraceAtDomain : Γ ⊢ₘ[T]
      trace ·ₘ numₘ(elements.length) ≐ₘ trace ·ₘ domₘ(sequence) :=
    function_application_term_congr_argument_of_equality
      trace (numₘ(elements.length)) (domₘ(sequence))
      (Metatheory.Derives.equality_symm hSequenceDomain)
  have hFinalAtDomain : Γ ⊢ₘ[T]
      object_sequence_code_from (numₘ(0)) elements ≐ₘ
        trace ·ₘ domₘ(sequence) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hTraceFinal) hTraceAtDomain
  have hPair := pair_congr_of_equalities
      (object_sequence_code_from (numₘ(0)) elements)
      (trace ·ₘ domₘ(sequence))
      (numₘ(elements.length)) (domₘ(sequence))
      hFinalAtDomain (Metatheory.Derives.equality_symm hSequenceDomain)
  have hFinal : Γ ⊢ₘ[T]
      code ≐ₘ godel_pairₘ(trace ·ₘ domₘ(sequence), domₘ(sequence)) := by
    simpa [code] using! hPair
  have hTraceBody : Γ ⊢ₘ[T]
      (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        object_sequence_code_trace_body sequence code trace := by
    change Γ ⊢ₘ[T]
      (trace ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (((domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
          sequence_trace_code_bound trace code) ∧ₘ
          ((trace ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            (object_sequence_code_pointwise_condition sequence trace code ∧ₘ
              (code ≐ₘ
                godel_pairₘ(trace ·ₘ domₘ(sequence), domₘ(sequence)))))
    exact FirstOrder.Derives.conj_intro hTraceSpace <|
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro hTraceDomain hTraceBound)
        (FirstOrder.Derives.conj_intro hZero <|
          FirstOrder.Derives.conj_intro hPointwise hFinal)
  change Γ ⊢ₘ[T]
    ((((sequence ∈ₘ seq_spaceₘ(source)) ∧ₘ
      (code ∈ₘ ωₘ)) ∧ₘ sequence_domain_code_bound sequence code) ∧ₘ
      object_sequence_code_trace_condition sequence code)
  have hPrefix : Γ ⊢ₘ[T]
      ((sequence ∈ₘ seq_spaceₘ(source)) ∧ₘ (code ∈ₘ ωₘ)) ∧ₘ
        sequence_domain_code_bound sequence code :=
    FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro hSequenceSpace hCodeOmega)
      hDomainBound
  apply FirstOrder.Derives.conj_intro hPrefix
  apply FirstOrder.Derives.exists_intro trace
  change Γ ⊢ₘ[T]
    Formula.instantiateTop trace
      ((Formula.LevyBound.membership ProofT.set_levy_bound
          (.bvar .here)
          ((seq_spaceₘ(ωₘ)).weakenBound ProofT.set_levy_bound.sort)) ∧ₘ
        object_sequence_code_trace_body
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))
  rw [Formula.instantiateTop_conj]
  rw [instantiate_top_membership,
    structural_sequence_code_trace_body_instantiateTop]
  exact hTraceBody

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
