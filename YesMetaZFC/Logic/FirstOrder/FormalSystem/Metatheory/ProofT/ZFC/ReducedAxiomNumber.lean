import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedAxiomPacket
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectBinaryTest

/-! # 完整等价公理基的任意数值输出表示

输出无需预先给出闭句类型。实际证书解码器决定唯一结论，固定表与模式图
共同证明同一数值关系的正负实例，供证明节点读取数码头部。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedAxiomNumber
open Nonlogical.BasicSetTheory NatPacket IntrinsicQuotation QuineEncoding ReducedAxioms
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedAxioms.basis

def value (certificate : ReducedAxiomPacket.Certificate) : Nat :=
  treeValue (SyntaxEncode.formula (axiomPresentation.sentence certificate))
def run (packet : Nat) : Option Nat := (ReducedAxiomPacket.decode packet).map value

def checked (packet output : Nat) : Bool := decide (run packet = some output)

theorem checked_iff (packet output : Nat) : checked packet output = true ↔
    ∃ certificate, ReducedAxiomPacket.encode certificate = packet ∧ value certificate = output := by
  constructor
  · intro h
    obtain ⟨certificate, hDecode, hValue⟩ := Option.map_eq_some_iff.mp (of_decide_eq_true h)
    exact ⟨certificate, (ReducedAxiomPacket.decode_eq_some_iff packet certificate).mp hDecode, hValue⟩
  · rintro ⟨certificate, hPacket, hValue⟩
    exact decide_eq_true (Option.map_eq_some_iff.mpr
      ⟨certificate, (ReducedAxiomPacket.decode_eq_some_iff packet certificate).mpr hPacket, hValue⟩)

def entries : List ObjectFiniteTable.Entry := ObjectFiniteAxioms.entries basis.axioms key

def condition {bound free : SetContext} (packet output : SetTerm bound free) : SetFormula bound free :=
  BaseAxiomPacket.condition packet output ∨ₘ ObjectFiniteTable.condition entries packet output

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (packet output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition packet output).substituteMapped bs fs =
      condition (packet.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition, Formula.substituteMapped]

def template : FormulaTemplate.Binary where
  body := condition (.fvar .here) (.fvar (.there .here))

@[simp] theorem template_apply {bound free : SetContext} (packet output : SetTerm bound free) :
    template packet output = condition packet output := by
  simp [template, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem positive (packet output : Nat) (h : checked packet output = true) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (numₘ(output) : Code)) := by
  obtain ⟨certificate, rfl, rfl⟩ := (checked_iff packet output).mp h
  cases certificate with
  | inl certificate =>
    apply FirstOrder.Derives.disj_intro_left
    exact BaseAxiomPacket.positive_number _ _ (by unfold ReducedAxiomPacket.encode ReducedAxiomPacket.encodeTree; rw [BaseAxiomPacket.run_encode]; rfl)
  | inr index =>
    apply FirstOrder.Derives.disj_intro_right
    exact ObjectFiniteTable.positive intrinsic_zfc_certificate_core entries
      (key index.val, SyntaxEncode.formula basis.axioms[index])
      (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)

theorem negative (packet output : Nat) (h : checked packet output = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (numₘ(output) : Code)) := by
  have hNo : run packet ≠ some output := of_decide_eq_false h
  apply IntrinsicSchema.disj_neg
  · apply BaseAxiomPacket.negative
    intro hBase
    obtain ⟨tree, hTree, hValue⟩ := Option.map_eq_some_iff.mp hBase
    obtain ⟨certificate, hPacket, rfl⟩ := (BaseAxiomPacket.run_eq_some_iff packet tree).mp hTree
    apply hNo
    apply Option.map_eq_some_iff.mpr
    refine ⟨.inl certificate, ?_, hValue⟩
    apply (ReducedAxiomPacket.decode_eq_some_iff packet _).mpr
    exact hPacket
  · apply ObjectFiniteTable.negative intrinsic_zfc_certificate_core
    intro entry hEntry hPacket hValue
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp hEntry
    apply hNo
    apply Option.map_eq_some_iff.mpr
    refine ⟨.inr index, ?_, hValue⟩
    apply (ReducedAxiomPacket.decode_eq_some_iff packet _).mpr
    exact hPacket.symm

def binaryTest : ObjectBinaryTest.Test intrinsic_zfc_theory where
  condition := template
  delta0 := .disj (BaseAxiomPacket.condition_delta0 _ _) (ObjectFiniteTable.condition_delta0 _ _ _)
  checked := checked
  positive packet output h := by rw [template_apply]; exact positive packet output h
  negative packet output h := by rw [template_apply]; exact negative packet output h

def localTest : ObjectCheckedTrace.LocalTest intrinsic_zfc_theory :=
  ObjectBinaryTest.localTest intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.contains_successor binaryTest

@[simp] theorem localTest_checked_pair (packet output : Nat) :
    localTest.checked (nodeValue 0 [packet, output]) = checked packet output :=
  ObjectBinaryTest.checked_pair binaryTest packet output

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedAxiomNumber
