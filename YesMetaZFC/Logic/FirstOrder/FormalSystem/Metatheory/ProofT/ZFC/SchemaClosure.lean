import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectUnaryIteration
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTemplateDerives

/-!
# 新 Project 树码上的参数全称闭合

层数是对象输入，不是展开为该长度的元层公式。闭合图只负责添加精确层数的全称节点；
正文作用域由既有正文图负责。旧 Hilbert 全称前缀条件不参与此层证明。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaClosure
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def close (count : Nat) (input : Tree) : Tree := ObjectUnaryIteration.tree 9 count input

theorem encode_forallClosure (n : Nat) (body : Project.Formula 1 n) :
    close n (ProjectEncode.formula body) = ProjectEncode.formula (Project.Formula.forallClosure n body) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Project.Formula.forallClosure, Definitional.Formula.forallClosure, ← ih]
    exact (ObjectUnaryIteration.tree_succ_right 9 n _).symm

def condition {bound free : SetContext} (count input output : SetTerm bound free) : SetFormula bound free :=
  ObjectUnaryIteration.condition (numₘ(9)) count input output

theorem condition_delta0 {bound free : SetContext} (count input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition count input output) := ObjectUnaryIteration.condition_delta0 _ _ _ _

def template : FormulaTemplate.Ternary where
  body := condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

theorem template_apply {bound free : SetContext} (count input output : SetTerm bound free) :
    template count input output = condition count input output := by
  simp [template, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    condition, ObjectUnaryIteration.condition, ObjectHorn.condition,
    IntrinsicQuotation.node, structural_list_code_term, structural_raw_node_code_term,
    structural_code_tag, Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons]

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _ _

theorem positive (count input output : Nat) (h : ObjectUnaryIteration.value 9 count input = output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(count)) (numₘ(input)) (numₘ(output) : Code)) :=
  ObjectUnaryIteration.positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity 9 count input output h

theorem negative (count input output : Nat) (h : ObjectUnaryIteration.value 9 count input ≠ output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(count)) (numₘ(input)) (numₘ(output) : Code)) :=
  ObjectUnaryIteration.negative intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport 9 count input output h

theorem positive_at_tree (count : Nat) (input output : Tree) (h : close count input = output) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(count)) (tree input) (tree output)) :=
  ObjectUnaryIteration.positive_at_tree intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    intrinsic_zfc_arithmetic_support.contains_infinity 9 count input output h

theorem negative_at_tree (count : Nat) (input output : Tree) (h : close count input ≠ output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(count)) (tree input) (tree output)) :=
  ObjectUnaryIteration.negative_at_tree intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.toArithmeticSupport 9 count input output h

def run (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) : Option Tree :=
  (SchemaTemplate.run kind n input).map (close n)

theorem run_isSome (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) :
    (run kind n input).isSome = SchemaBody.check (kind.sourceDepth n) input := by
  simp only [run, Option.isSome_map, SchemaTemplate.run_isSome]

theorem run_separation {n : Nat} (schema : Project.UnarySchema n) :
    run .separation n (ProjectEncode.formula schema.body) =
      some (ProjectEncode.formula (Axioms.Schema.separation schema).formula) := by
  rw [run, SchemaTemplate.run_separation, Option.map_some, encode_forallClosure]
  rfl

theorem run_collection {n : Nat} (schema : Project.BinarySchema n) :
    run .collection n (ProjectEncode.formula schema.body) =
      some (ProjectEncode.formula (Axioms.Schema.collection schema).formula) := by
  rw [run, SchemaTemplate.run_collection, Option.map_some, encode_forallClosure]
  rfl

theorem run_replacement {n : Nat} (schema : Project.BinarySchema n) :
    run .replacement n (ProjectEncode.formula schema.body) =
      some (ProjectEncode.formula (Axioms.Schema.replacement schema).formula) := by
  rw [run, SchemaTemplate.run_replacement, Option.map_some, encode_forallClosure]
  rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaClosure
