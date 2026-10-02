import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjectQuotationDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaJoinInstances

/-! # 原始转换与当前类型安全内核 quotation 的交换律 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.KernelQuotation
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

@[simp] theorem bound_index {n : Nat} (i : Fin n) : (project_bound_variable i).index = i.val :=
  congrArg Fin.val (project_bound_index_variable i)

@[simp] theorem project_term_code {n : Nat} (input : Project.Term n) (h : input.freeSupport = []) :
    ProjectEncode.term input = SyntaxEncode.term (project_term input h) := by
  cases input with
  | bound i =>
    rw [ProjectEncode.term, project_term, SyntaxEncode.term_bvar]
    exact congrArg (fun n => Tree.node 0 [leaf n]) (bound_index i).symm
  | free _ => cases h

/-- 对任意自由闭的 Project 公式逐构造子交换；无 Hilbert 化或旧 quote。 -/
theorem project_formula_code {n : Nat} (input : Project.Formula 1 n) (h : input.FreeClosed) :
    ObjectProjectQuotation.run (ProjectEncode.formula input) =
      some (SyntaxEncode.formula (project_formula input h)) := by
  induction input with
  | falsum | truth => rw [ProjectEncode.formula, leaf, ObjectProjectQuotation.run.eq_def, project_formula]; rfl
  | mem left right =>
    simp only [Formula.FreeClosed] at h
    rw [ProjectEncode.formula, ObjectProjectQuotation.run.eq_def]
    simp [ObjectProjectQuotation.atom, project_formula, project_mem, SyntaxEncode.formula,
      SyntaxEncode.argumentsList, project_term_code left h.1, project_term_code right h.2]
  | atom symbol _ args =>
    simp only [Formula.FreeClosed] at h
    cases symbol <;> rw [ProjectEncode.formula, ObjectProjectQuotation.run.eq_def]
    all_goals simp [ObjectProjectQuotation.atom, project_formula, SyntaxEncode.formula,
      SyntaxEncode.argumentsList, project_term_code (args 0) (h 0), project_term_code (args 1) (h 1),
      subset_formula]
  | neg body ih =>
    simp only [Formula.FreeClosed] at h
    rw [ProjectEncode.formula, ObjectProjectQuotation.run.eq_def]
    change (ObjectProjectQuotation.run (ProjectEncode.formula body)).bind _ = _
    rw [ih h]
    simp [project_formula, SyntaxEncode.formula]
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight | iff left right ihLeft ihRight =>
    simp only [Formula.FreeClosed] at h
    rw [ProjectEncode.formula, ObjectProjectQuotation.run.eq_def]
    change (ObjectProjectQuotation.run (ProjectEncode.formula left)).bind _ = _
    rw [ihLeft h.1]
    dsimp only [Option.bind_some]
    rw [ihRight h.2]
    simp [project_formula, SyntaxEncode.formula]
  | forallE body ih | existsE body ih =>
    simp only [Formula.FreeClosed] at h
    rw [ProjectEncode.formula, ObjectProjectQuotation.run.eq_def]
    change (ObjectProjectQuotation.run (ProjectEncode.formula body)).bind _ = _
    rw [ih h]
    simp [project_formula, SyntaxEncode.formula]

theorem positive (input output : Tree) (h : ObjectProjectQuotation.run input = some output) :
    Derives intrinsic_zfc_theory [] (ObjectProjectQuotation.condition
      (numₘ(treeValue input)) (numₘ(treeValue output) : Code)) :=
  ObjectProjectQuotation.positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity input output h

theorem negative (input : Tree) (output : Nat)
    (h : (ObjectProjectQuotation.run input).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ ObjectProjectQuotation.condition
      (numₘ(treeValue input)) (numₘ(output) : Code)) :=
  ObjectProjectQuotation.negative intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport input output h

theorem sentence_positive (sentence : Project.Sentence) :
    Derives intrinsic_zfc_theory [] (ObjectProjectQuotation.condition
      (IntrinsicQuotation.tree (ProjectEncode.formula sentence.formula))
      (IntrinsicQuotation.quote (project_sentence sentence))) :=
  ObjectProjectQuotation.positive_at_tree intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity _ _ (project_formula_code _ sentence.freeClosed)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.KernelQuotation
