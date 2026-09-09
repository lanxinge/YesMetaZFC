import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-!
# `ProofT` 内在序列条件的直接反演

本模块只抽取编码条件已经携带的数学内容。所有量词均通过内在上下文实例化，
不再引入变量编号、自由支撑或良构桥接。
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

/-- 自然数序列编码条件的五个直接组成部分。 -/
structure NatSequenceConditionParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) where
  sequence_space : Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(ωₘ)
  code_omega : Γ ⊢ₘ[T] code ∈ₘ ωₘ
  domain_code_bound : Γ ⊢ₘ[T] sequence_domain_code_bound sequence code
  value_code_bound : Γ ⊢ₘ[T] nat_sequence_value_code_bound sequence code
  trace_exists : Γ ⊢ₘ[T]
    (nat_sequence_code_trace_condition
      (sequence.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here)).existsE SetSort.set

/-- 从内在自然数序列编码条件中直接抽取五个组成部分。 -/
theorem nat_sequence_code_condition_parts
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (hCondition : Γ ⊢ₘ[T] nat_sequence_code_condition sequence code) :
    NatSequenceConditionParts (T := T) Γ sequence code where
  sequence_space := by
    exact FirstOrder.Derives.conj_elim_left <|
      FirstOrder.Derives.conj_elim_left <|
        FirstOrder.Derives.conj_elim_left <|
          FirstOrder.Derives.conj_elim_left hCondition
  code_omega := by
    exact FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.conj_elim_left <|
        FirstOrder.Derives.conj_elim_left <|
          FirstOrder.Derives.conj_elim_left hCondition
  domain_code_bound := by
    exact FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.conj_elim_left <|
        FirstOrder.Derives.conj_elim_left hCondition
  value_code_bound := by
    exact FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.conj_elim_left hCondition
  trace_exists := by
    exact FirstOrder.Derives.conj_elim_right hCondition

/-- 证明序列编码条件的四个直接组成部分。 -/
structure ProofSequenceConditionParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) where
  sequence_space :
    Γ ⊢ₘ[T] sequence ∈ₘ seq_spaceₘ(syntax_formula_code_set_term)
  code_omega : Γ ⊢ₘ[T] code ∈ₘ ωₘ
  domain_code_bound :
    Γ ⊢ₘ[T] sequence_domain_code_bound sequence code
  trace_condition :
    Γ ⊢ₘ[T] proof_sequence_code_trace_condition sequence code

/-- 从内在证明序列编码条件中直接抽取四个组成部分。 -/
theorem proof_sequence_code_condition_parts
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (hCondition : Γ ⊢ₘ[T]
      proof_sequence_code_condition sequence code) :
    ProofSequenceConditionParts (T := T) Γ sequence code where
  sequence_space := by
    exact FirstOrder.Derives.conj_elim_left <|
      FirstOrder.Derives.conj_elim_left <|
        FirstOrder.Derives.conj_elim_left hCondition
  code_omega := by
    exact FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.conj_elim_left <|
        FirstOrder.Derives.conj_elim_left hCondition
  domain_code_bound := by
    exact FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.conj_elim_left hCondition
  trace_condition := by
    exact FirstOrder.Derives.conj_elim_right hCondition

def nat_sequence_trace_context
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) :
    Context signature (SetSort.set :: free) :=
  Formula.openBoundTop (σ := signature) SetSort.set
      (nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here)) ::
    FreshVariable.extendContext SetSort.set Γ

def nat_sequence_trace_term
    {free : SetContext} : SetOpenTerm (SetSort.set :: free) :=
  FreshVariable.newest (σ := signature) (free := free) SetSort.set

/-- 打开最外层 bound 后，旧开放项直接变为扩展 free 上下文中的项。 -/
theorem term_weakenBound_substitute_newest
    {free : SetContext}
    (term : SetOpenTerm free) :
    (term.weakenBound SetSort.set).substituteMapped
        (VariableSubstitution.instantiateTop
          (FreshVariable.newest (σ := signature) (free := free)
            SetSort.set))
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken SetSort.set)) =
      term.weakenFree SetSort.set := by
  exact Term.openBoundTop_weakenBound SetSort.set term

/-- 有界量词体中的第二层 bound weakening 也可直接打开为 free weakening。 -/
theorem term_two_weakenBound_substitute_newest
    {free : SetContext}
    (term : SetOpenTerm free) :
    ((term.weakenBound SetSort.set).weakenBound SetSort.set).substituteMapped
        (VariableSubstitution.liftBound SetSort.set
          (VariableSubstitution.instantiateTop
            (FreshVariable.newest (σ := signature) (free := free)
              SetSort.set)))
        (VariableSubstitution.of_renaming
          (VariableRenaming.weaken SetSort.set)) =
      (term.weakenFree SetSort.set).weakenBound SetSort.set := by
  calc
    _ = ((term.weakenBound SetSort.set).substituteMapped
          (VariableSubstitution.instantiateTop
            (FreshVariable.newest (σ := signature) (free := free) SetSort.set))
          (VariableSubstitution.of_renaming
            (VariableRenaming.weaken SetSort.set))).weakenBound SetSort.set := by
      simpa only [VariableSubstitution.weakenBound_of_renaming] using
        (Term.substituteMapped_weakenBound SetSort.set
          (VariableSubstitution.instantiateTop
            (FreshVariable.newest (σ := signature) (free := free) SetSort.set))
          (VariableSubstitution.of_renaming (VariableRenaming.weaken SetSort.set))
          (term.weakenBound SetSort.set))
    _ = _ := congrArg (Term.weakenBound SetSort.set)
      (term_weakenBound_substitute_newest term)

/-- 规范轨迹见证上下文中暴露的五个直接分量。 -/
structure NatSequenceTraceParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) where
  trace_space :
    nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
      nat_sequence_trace_term ∈ₘ seq_spaceₘ(ωₘ)
  domain_eq :
    nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
      domₘ(nat_sequence_trace_term) ≐ₘ
        Sₘ(domₘ(sequence.weakenFree SetSort.set))
  code_bound :
    nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
      sequence_trace_code_bound
        nat_sequence_trace_term
        (code.weakenFree SetSort.set)
  zero_value :
    nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
      (nat_sequence_trace_term ·ₘ numₘ(0)) ≐ₘ numₘ(0)
  step :
    nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
      Formula.LevyBound.boundedForall ProofT.set_levy_bound
        (domₘ(sequence.weakenFree SetSort.set))
        (nat_sequence_code_step_condition
          (Term.weakenBound SetSort.set
            (sequence.weakenFree SetSort.set))
          (Term.weakenBound SetSort.set nat_sequence_trace_term)
          (.bvar .here))
  final_code :
    nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
      (code.weakenFree SetSort.set) ≐ₘ
        (nat_sequence_trace_term ·ₘ
          domₘ(sequence.weakenFree SetSort.set))

/-- 从自然数序列条件的存在轨迹中直接取出规范见证的分量。 -/
theorem nat_sequence_code_trace_parts_of_assumption
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (hBody : nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set
        (nat_sequence_code_trace_condition
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))) :
    NatSequenceTraceParts (T := T) Γ sequence code := by
  let body : SetFormula [SetSort.set] free :=
    nat_sequence_code_trace_condition
      (sequence.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here)
  let opened : SetOpenFormula (SetSort.set :: free) :=
    Formula.openBoundTop (σ := signature) SetSort.set body
  have hBody' := hBody
  simp [ nat_sequence_trace_context, Formula.openBoundTop,
    nat_sequence_code_trace_condition, sequence_trace_code_bound,
    nat_sequence_code_step_condition, set_levy_bound,
    Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.instantiateTop,
    VariableSubstitution.weakenBound_of_renaming, VariableSubstitution.liftBound,
    term_weakenBound_substitute_newest,
    term_two_weakenBound_substitute_newest,
    Term.weakenFree_weakenBound] at hBody'
  have hSpace := FirstOrder.Derives.conj_elim_left hBody'
  have hRest := FirstOrder.Derives.conj_elim_right hBody'
  have hDomainAndBound := FirstOrder.Derives.conj_elim_left hRest
  have hZeroAndStepAndFinal := FirstOrder.Derives.conj_elim_right hRest
  have hDomain := FirstOrder.Derives.conj_elim_left hDomainAndBound
  have hCodeBound := FirstOrder.Derives.conj_elim_right hDomainAndBound
  have hZero := FirstOrder.Derives.conj_elim_left hZeroAndStepAndFinal
  have hStepAndFinal := FirstOrder.Derives.conj_elim_right hZeroAndStepAndFinal
  have hStep := FirstOrder.Derives.conj_elim_left hStepAndFinal
  have hFinal := FirstOrder.Derives.conj_elim_right hStepAndFinal
  exact {
    trace_space := by
      simpa [opened, body, nat_sequence_trace_context,
        nat_sequence_trace_term, Formula.openBoundTop,
        nat_sequence_code_trace_condition, sequence_trace_code_bound,
        nat_sequence_code_step_condition, set_levy_bound,
        Formula.LevyBound.boundedForall,
        Formula.LevyBound.membership, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop,
        VariableSubstitution.of_renaming,
        VariableSubstitution.weakenBound_of_renaming,
        VariableSubstitution.freeId,
        VariableSubstitution.boundId, VariableSubstitution.liftBound,
        VariableSubstitution.weakenBound,
        term_weakenBound_substitute_newest,
        term_two_weakenBound_substitute_newest,
        Term.substituteMapped_weakenBound,
        Arguments.substituteMapped_weakenBound,
        Term.weakenFree_weakenBound, Arguments.weakenFree_weakenBound,
        VariableRenaming.id,
        VariableRenaming.weaken] using hSpace
    domain_eq := by
      simpa [opened, body, nat_sequence_trace_context,
        nat_sequence_trace_term, Formula.openBoundTop,
        nat_sequence_code_trace_condition, sequence_trace_code_bound,
        nat_sequence_code_step_condition, set_levy_bound,
        Formula.LevyBound.boundedForall,
        Formula.LevyBound.membership, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop,
        VariableSubstitution.of_renaming,
        VariableSubstitution.weakenBound_of_renaming,
        VariableSubstitution.freeId,
        VariableSubstitution.boundId, VariableSubstitution.liftBound,
        VariableSubstitution.weakenBound,
        term_weakenBound_substitute_newest,
        term_two_weakenBound_substitute_newest,
        Term.substituteMapped_weakenBound,
        Arguments.substituteMapped_weakenBound,
        Term.weakenFree_weakenBound, Arguments.weakenFree_weakenBound,
        VariableRenaming.id,
        VariableRenaming.weaken] using hDomain
    code_bound := by
      simpa [opened, body, nat_sequence_trace_context,
        nat_sequence_trace_term, Formula.openBoundTop,
        nat_sequence_code_trace_condition, sequence_trace_code_bound,
        nat_sequence_code_step_condition, set_levy_bound,
        Formula.LevyBound.boundedForall,
        Formula.LevyBound.membership, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop,
        VariableSubstitution.of_renaming,
        VariableSubstitution.weakenBound_of_renaming,
        VariableSubstitution.freeId,
        VariableSubstitution.boundId, VariableSubstitution.liftBound,
        VariableSubstitution.weakenBound,
        term_weakenBound_substitute_newest,
        term_two_weakenBound_substitute_newest,
        Term.substituteMapped_weakenBound,
        Arguments.substituteMapped_weakenBound,
        Term.weakenFree_weakenBound, Arguments.weakenFree_weakenBound,
        VariableRenaming.id,
        VariableRenaming.weaken] using hCodeBound
    zero_value := by
      simpa [opened, body, nat_sequence_trace_context,
        nat_sequence_trace_term, Formula.openBoundTop,
        nat_sequence_code_trace_condition, sequence_trace_code_bound,
        nat_sequence_code_step_condition, set_levy_bound,
        Formula.LevyBound.boundedForall,
        Formula.LevyBound.membership, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop,
        VariableSubstitution.of_renaming,
        VariableSubstitution.weakenBound_of_renaming,
        VariableSubstitution.freeId,
        VariableSubstitution.boundId, VariableSubstitution.liftBound,
        VariableSubstitution.weakenBound,
        term_weakenBound_substitute_newest,
        term_two_weakenBound_substitute_newest,
        Term.substituteMapped_weakenBound,
        Arguments.substituteMapped_weakenBound,
        Term.weakenFree_weakenBound, Arguments.weakenFree_weakenBound,
        VariableRenaming.id,
        VariableRenaming.weaken] using hZero
    step := by
      simpa [opened, body, nat_sequence_trace_context,
        nat_sequence_trace_term, Formula.openBoundTop,
        nat_sequence_code_trace_condition, sequence_trace_code_bound,
        nat_sequence_code_step_condition, set_levy_bound,
        Formula.LevyBound.boundedForall,
        Formula.LevyBound.membership, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop,
        VariableSubstitution.of_renaming,
        VariableSubstitution.weakenBound_of_renaming,
        VariableSubstitution.freeId,
        VariableSubstitution.boundId, VariableSubstitution.liftBound,
        VariableSubstitution.weakenBound,
        term_weakenBound_substitute_newest,
        term_two_weakenBound_substitute_newest,
        Term.substituteMapped_weakenBound,
        Arguments.substituteMapped_weakenBound,
        Term.weakenFree_weakenBound, Arguments.weakenFree_weakenBound,
        VariableRenaming.id,
        VariableRenaming.weaken] using hStep
    final_code := by
      simpa [opened, body, nat_sequence_trace_context,
        nat_sequence_trace_term, Formula.openBoundTop,
        nat_sequence_code_trace_condition, sequence_trace_code_bound,
        nat_sequence_code_step_condition, set_levy_bound,
        Formula.LevyBound.boundedForall,
        Formula.LevyBound.membership, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        VariableSubstitution.instantiateTop,
        VariableSubstitution.of_renaming,
        VariableSubstitution.weakenBound_of_renaming,
        VariableSubstitution.freeId,
        VariableSubstitution.boundId, VariableSubstitution.liftBound,
        VariableSubstitution.weakenBound,
        term_weakenBound_substitute_newest,
        term_two_weakenBound_substitute_newest,
        Term.substituteMapped_weakenBound,
        Arguments.substituteMapped_weakenBound,
        Term.weakenFree_weakenBound, Arguments.weakenFree_weakenBound,
        VariableRenaming.id,
        VariableRenaming.weaken] using hFinal
  }

/-- 以存在消去把轨迹分量交给后续递归证明，不暴露对象层见证选择。 -/
theorem nat_sequence_code_trace_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (hTrace : Γ ⊢ₘ[T]
      (nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here)).existsE SetSort.set)
    {conclusion : SetOpenFormula free}
    (hCase : NatSequenceTraceParts (T := T) Γ sequence code →
      nat_sequence_trace_context Γ sequence code ⊢ₘ[T]
        conclusion.weakenFree SetSort.set) :
    Γ ⊢ₘ[T] conclusion := by
  let body : SetFormula [SetSort.set] free :=
    nat_sequence_code_trace_condition
      (sequence.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here)
  let opened : SetOpenFormula (SetSort.set :: free) :=
    Formula.openBoundTop (σ := signature) SetSort.set body
  have hExistential : Γ ⊢ₘ[T] opened.existsFreeTop SetSort.set := by
    simpa [opened, body, Formula.existsFreeTop] using hTrace
  apply FirstOrder.Derives.exists_elim hExistential
  have hBody :
      nat_sequence_trace_context Γ sequence code ⊢ₘ[T] opened :=
    FirstOrder.Derives.assumption List.mem_cons_self
  simpa [opened, nat_sequence_trace_context] using
    hCase (nat_sequence_code_trace_parts_of_assumption
      sequence code hBody)

/-- 自然数序列值界在任意定义域点的直接实例化。 -/
theorem nat_sequence_value_code_bound_at
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code index : SetOpenTerm free)
    (hBound : Γ ⊢ₘ[T]
      nat_sequence_value_code_bound sequence code)
    (hIndex : Γ ⊢ₘ[T] index ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T] (sequence ·ₘ index) ∈ₘ code := by
  have hValue := bounded_forall_elim
    (domₘ(sequence))
    ((sequence.weakenBound SetSort.set ·ₘ (.bvar .here)) ∈ₘ
      code.weakenBound SetSort.set)
    index hBound hIndex
  simpa [nat_sequence_value_code_bound,
    Formula.LevyBound.boundedForall] using! hValue

/-- 轨迹值界在任意轨迹定义域点的直接实例化。 -/
theorem sequence_trace_code_bound_at
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (trace code index : SetOpenTerm free)
    (hBound : Γ ⊢ₘ[T]
      sequence_trace_code_bound trace code)
    (hIndex : Γ ⊢ₘ[T] index ∈ₘ domₘ(trace)) :
    Γ ⊢ₘ[T] (trace ·ₘ index) ∈ₘ Sₘ(code) := by
  have hValue := bounded_forall_elim
    (domₘ(trace))
    ((trace.weakenBound SetSort.set ·ₘ (.bvar .here)) ∈ₘ
      Sₘ(code.weakenBound SetSort.set))
    index hBound hIndex
  simpa [sequence_trace_code_bound,
    Formula.LevyBound.boundedForall] using! hValue

/-- 递推界在任意对象定义域点直接给出一步等式。 -/
theorem nat_sequence_code_step_condition_at
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace index : SetOpenTerm free)
    (hStep : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedForall ProofT.set_levy_bound
        (domₘ(sequence))
        (nat_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (.bvar .here)))
    (hIndex : Γ ⊢ₘ[T] index ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T] nat_sequence_code_step_condition sequence trace index := by
  have hValue := bounded_forall_elim
    (domₘ(sequence))
    (nat_sequence_code_step_condition
      (sequence.weakenBound SetSort.set)
      (trace.weakenBound SetSort.set)
      (.bvar .here))
    index hStep hIndex
  simpa [nat_sequence_code_step_condition] using! hValue

/-- 二维编码的逐行条件在任意定义域点直接给出行码存在式。 -/
theorem proof_sequence_code_row_condition_at
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code index : SetOpenTerm free)
    (hPointwise : Γ ⊢ₘ[T]
      proof_sequence_code_pointwise_condition sequence trace code)
    (hIndex : Γ ⊢ₘ[T] index ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      proof_sequence_code_row_condition sequence trace code index := by
  have hValue := bounded_forall_elim
    (domₘ(sequence))
    (proof_sequence_code_row_condition
      (sequence.weakenBound SetSort.set)
      (trace.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here))
    index hPointwise hIndex
  simpa [proof_sequence_code_pointwise_condition] using! hValue

/-- 逐行存在式打开后的规范行码项。 -/
def proof_sequence_row_code_term
    {free : SetContext} : SetOpenTerm (SetSort.set :: free) :=
  FreshVariable.newest (σ := signature) (free := free) SetSort.set

/-- 逐行存在式的规范见证上下文。 -/
def proof_sequence_row_context
    {free : SetContext}
    (Γ : Context signature free)
    (sequence trace code index : SetOpenTerm free) :
    Context signature (SetSort.set :: free) :=
  Formula.openBoundTop (σ := signature) SetSort.set
      (bounded_exists_body code
        (proof_sequence_code_step_condition
          (sequence.weakenBound SetSort.set)
          (trace.weakenBound SetSort.set)
          (index.weakenBound SetSort.set)
          (.bvar .here))) ::
    FreshVariable.extendContext SetSort.set Γ

/-- 规范行码见证携带的全部直接信息。 -/
structure ProofSequenceRowParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (sequence trace code index : SetOpenTerm free) where
  row_code_mem :
    proof_sequence_row_context Γ sequence trace code index ⊢ₘ[T]
      proof_sequence_row_code_term ∈ₘ code.weakenFree SetSort.set
  row_condition :
    proof_sequence_row_context Γ sequence trace code index ⊢ₘ[T]
      proof_sequence_code_step_condition
        (sequence.weakenFree SetSort.set)
        (trace.weakenFree SetSort.set)
        (index.weakenFree SetSort.set)
        proof_sequence_row_code_term

/-- 从逐行存在式的规范假设直接抽取成员 guard 与行条件。 -/
theorem proof_sequence_code_row_parts_of_assumption
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code index : SetOpenTerm free)
    (hBody : proof_sequence_row_context Γ sequence trace code index ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body code
          (proof_sequence_code_step_condition
            (sequence.weakenBound SetSort.set)
            (trace.weakenBound SetSort.set)
            (index.weakenBound SetSort.set)
            (.bvar .here)))) :
    ProofSequenceRowParts (T := T) Γ sequence trace code index := by
  rw [bounded_exists_body_openBoundTop] at hBody
  have hMem := FirstOrder.Derives.conj_elim_left hBody
  have hStep := FirstOrder.Derives.conj_elim_right hBody
  exact {
    row_code_mem := hMem
    row_condition := by
      simpa [proof_sequence_row_code_term] using! hStep
  }

/-- 打开逐行存在码见证，并只暴露规范化后的数学分量。 -/
theorem proof_sequence_code_row_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace code index : SetOpenTerm free)
    {conclusion : SetOpenFormula free}
    (hRow : Γ ⊢ₘ[T]
      proof_sequence_code_row_condition sequence trace code index)
    (hCase : ProofSequenceRowParts (T := T) Γ sequence trace code index →
      proof_sequence_row_context Γ sequence trace code index ⊢ₘ[T]
        conclusion.weakenFree SetSort.set) :
    Γ ⊢ₘ[T] conclusion := by
  let body : SetFormula [SetSort.set] free :=
    proof_sequence_code_step_condition
      (sequence.weakenBound SetSort.set)
      (trace.weakenBound SetSort.set)
      (index.weakenBound SetSort.set)
      (.bvar .here)
  apply bounded_exists_elim code body conclusion
    (by simpa [body, proof_sequence_code_row_condition] using! hRow)
  have hBody : proof_sequence_row_context Γ sequence trace code index ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body code body) :=
    FirstOrder.Derives.assumption List.mem_cons_self
  simpa [body, proof_sequence_row_context] using
    hCase (proof_sequence_code_row_parts_of_assumption
      sequence trace code index hBody)

/-- 二维编码轨迹存在式打开后的规范轨迹项。 -/
def proof_sequence_trace_term
    {free : SetContext} : SetOpenTerm (SetSort.set :: free) :=
  FreshVariable.newest (σ := signature) (free := free) SetSort.set

/-- 二维编码轨迹存在式的规范见证上下文。 -/
def proof_sequence_trace_context
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) :
    Context signature (SetSort.set :: free) :=
  Formula.openBoundTop (σ := signature) SetSort.set
      (bounded_exists_body (seq_spaceₘ(ωₘ))
        (proof_sequence_code_trace_body
          (sequence.weakenBound SetSort.set)
          (code.weakenBound SetSort.set)
          (.bvar .here))) ::
    FreshVariable.extendContext SetSort.set Γ

/-- 规范二维轨迹见证携带的六个直接分量。 -/
structure ProofSequenceTraceParts
    {T : SetTheory}
    {free : SetContext}
    (Γ : Context signature free)
    (sequence code : SetOpenTerm free) where
  trace_space :
    proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      proof_sequence_trace_term ∈ₘ seq_spaceₘ(ωₘ)
  domain_eq :
    proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      domₘ(proof_sequence_trace_term) ≐ₘ
        Sₘ(domₘ(sequence.weakenFree SetSort.set))
  code_bound :
    proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      sequence_trace_code_bound proof_sequence_trace_term
        (code.weakenFree SetSort.set)
  zero_value :
    proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      (proof_sequence_trace_term ·ₘ numₘ(0)) ≐ₘ numₘ(0)
  pointwise :
    proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      proof_sequence_code_pointwise_condition
        (sequence.weakenFree SetSort.set)
        proof_sequence_trace_term
        (code.weakenFree SetSort.set)
  final_code :
    proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      code.weakenFree SetSort.set ≐ₘ
        (proof_sequence_trace_term ·ₘ
          domₘ(sequence.weakenFree SetSort.set))

/-- 从二维轨迹的规范假设直接抽取全部数学分量。 -/
theorem proof_sequence_code_trace_parts_of_assumption
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (hOpened : proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body (seq_spaceₘ(ωₘ))
          (proof_sequence_code_trace_body
            (sequence.weakenBound SetSort.set)
            (code.weakenBound SetSort.set)
            (.bvar .here)))) :
    ProofSequenceTraceParts (T := T) Γ sequence code := by
  rw [bounded_exists_body_openBoundTop] at hOpened
  have hSpace := FirstOrder.Derives.conj_elim_left hOpened
  have hBodyOpened := FirstOrder.Derives.conj_elim_right hOpened
  have hBody : proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      proof_sequence_code_trace_body
        (sequence.weakenFree SetSort.set)
        (code.weakenFree SetSort.set)
        proof_sequence_trace_term := by
    simpa [proof_sequence_trace_term] using! hBodyOpened
  have hDomainAndBound := FirstOrder.Derives.conj_elim_left hBody
  have hZeroAndRest := FirstOrder.Derives.conj_elim_right hBody
  have hDomain := FirstOrder.Derives.conj_elim_left hDomainAndBound
  have hBound := FirstOrder.Derives.conj_elim_right hDomainAndBound
  have hZero := FirstOrder.Derives.conj_elim_left hZeroAndRest
  have hPointwiseAndFinal := FirstOrder.Derives.conj_elim_right hZeroAndRest
  have hPointwise := FirstOrder.Derives.conj_elim_left hPointwiseAndFinal
  have hFinal := FirstOrder.Derives.conj_elim_right hPointwiseAndFinal
  exact {
    trace_space := hSpace
    domain_eq := hDomain
    code_bound := hBound
    zero_value := hZero
    pointwise := hPointwise
    final_code := hFinal
  }

/-- 打开二维编码的轨迹见证，并只暴露规范化后的数学分量。 -/
theorem proof_sequence_code_trace_elim
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    {conclusion : SetOpenFormula free}
    (hTrace : Γ ⊢ₘ[T]
      proof_sequence_code_trace_condition sequence code)
    (hCase : ProofSequenceTraceParts (T := T) Γ sequence code →
      proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
        conclusion.weakenFree SetSort.set) :
    Γ ⊢ₘ[T] conclusion := by
  let body : SetFormula [SetSort.set] free :=
    proof_sequence_code_trace_body
      (sequence.weakenBound SetSort.set)
      (code.weakenBound SetSort.set)
      (.bvar .here)
  apply bounded_exists_elim (seq_spaceₘ(ωₘ)) body conclusion
    (by simpa [body, proof_sequence_code_trace_condition] using hTrace)
  have hOpened : proof_sequence_trace_context Γ sequence code ⊢ₘ[T]
      Formula.openBoundTop (σ := signature) SetSort.set
        (bounded_exists_body (seq_spaceₘ(ωₘ)) body) :=
    FirstOrder.Derives.assumption List.mem_cons_self
  simpa [body, proof_sequence_trace_context] using
    hCase (proof_sequence_code_trace_parts_of_assumption
      sequence code hOpened)

/-- 统一运输递归轨迹的内部界与末值，不依赖具体行编码。 -/
theorem sequence_trace_numeral_data
    {T : SetTheory} (A : ArithmeticSupport T)
    {free : SetContext} {Γ : Context signature free}
    (sequence trace code : SetOpenTerm free) (length bound : Nat)
    (hDomain : Γ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(length))
    (hCode : Γ ⊢ₘ[T] code ≐ₘ numₘ(bound))
    (hTraceDomain : Γ ⊢ₘ[T] domₘ(trace) ≐ₘ Sₘ(domₘ(sequence)))
    (hBound : Γ ⊢ₘ[T] sequence_trace_code_bound trace code)
    (hFinal : Γ ⊢ₘ[T] code ≐ₘ (trace ·ₘ domₘ(sequence))) :
    (∀ index, index ≤ length → Γ ⊢ₘ[T] (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1)) ∧
      (Γ ⊢ₘ[T] numₘ(bound) ≐ₘ (trace ·ₘ numₘ(length))) := by
  have hTrace : Γ ⊢ₘ[T] domₘ(trace) ≐ₘ numₘ(length + 1) :=
    FirstOrder.Derives.eq_trans hTraceDomain
      (successor_term_congr_of_equality _ _ hDomain)
  constructor
  · intro index hIndex
    have hMember := sequence_trace_code_bound_at trace code (numₘ(index)) hBound
      (row_index_mem_of_domain A trace (length + 1) index hTrace (by omega))
    exact FirstOrder.Derives.iff_elim_left
      (membership_right_iff_of_equality _ _ _ (successor_term_congr_of_equality _ _ hCode))
      hMember
  · exact FirstOrder.Derives.eq_trans (FirstOrder.Derives.eq_symm hCode)
      (FirstOrder.Derives.eq_trans hFinal
        (function_application_term_congr_argument_of_equality trace _ _ hDomain))

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
