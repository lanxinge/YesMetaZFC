import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectRangeTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameInstances
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel

/-! # 六个实际重命名位置的参数表生成 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTable
open Nonlogical.BasicSetTheory QuineEncoding IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectRangeTable
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def entry : SchemaRename.Site → Entry
  | .separation => ⟨0, 3, [0]⟩
  | .collectionPremise => ⟨1, 3, [0, 1]⟩
  | .collectionImage => ⟨2, 4, [0, 1]⟩
  | .replacementFirst => ⟨3, 3, [1, 2]⟩
  | .replacementSecond => ⟨4, 3, [0, 2]⟩
  | .replacementImage => ⟨5, 4, [1, 0]⟩

def sites : List SchemaRename.Site :=
  [.separation, .collectionPremise, .collectionImage, .replacementFirst, .replacementSecond, .replacementImage]

def program : List Entry := sites.map entry

theorem entry_mem (site : SchemaRename.Site) : entry site ∈ program := by
  cases site <;> simp [program, sites]

theorem entry_of_tag (site : SchemaRename.Site) (candidate : Entry)
    (h : candidate ∈ program) (hTag : candidate.tag = (entry site).tag) : candidate = entry site := by
  simp only [program, sites, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> cases site <;> simp_all [entry]

theorem table_eq (site : SchemaRename.Site) (n : Nat) :
    (entry site).heads ++ range (entry site).start n = site.table n := by
  cases site <;> simp [entry, range_ofFn, SchemaRename.Site.table]

def condition {bound free : SetContext} (tag n output : SetTerm bound free) : SetFormula bound free :=
  ObjectRangeTable.condition program tag n output

theorem condition_delta0 {bound free : SetContext} (tag n output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition tag n output) := ObjectRangeTable.condition_delta0 _ _ _ _

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext}
    (tag n output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (condition tag n output).substituteMapped bs fs =
      condition (tag.substituteMapped bs fs) (n.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition, ObjectRangeTable.condition, ObjectHorn.condition, IntrinsicQuotation.node,
    structural_list_code_term, structural_raw_node_code_term, structural_code_tag,
    Term.substituteMapped, Arguments.substituteMapped]

def template : FormulaTemplate.Ternary where
  body := condition (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _ _

theorem positive (site : SchemaRename.Site) (n : Nat) :
    Derives intrinsic_zfc_theory [] (condition (numₘ((entry site).tag)) (numₘ(n))
      (numₘ(listValue (site.table n)) : Code)) := by
  have h := ObjectRangeTable.table_accept program (entry site) (entry_mem site) n
  rw [table_eq] at h
  obtain ⟨rows, hRoot, hRows⟩ := h
  exact ObjectHorn.transport (rules program) (FirstOrder.Derives.eq_symm
    (node_evaluate intrinsic_zfc_certificate_core 1 [(entry site).tag, n, listValue (site.table n)]))
    (ObjectHorn.positive intrinsic_zfc_certificate_core
      intrinsic_zfc_arithmetic_support.toFiniteSequenceGraphSupport
      (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
        (relation_plane_theory_subset_function_predicate_theory
          (power_set_operator_theory_subset_relation_plane_theory h)))
      intrinsic_zfc_arithmetic_support.contains_infinity (rules program) _ rows hRoot hRows)

theorem negative (site : SchemaRename.Site) (n output : Nat) (hBad : listValue (site.table n) ≠ output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ((entry site).tag)) (numₘ(n)) (numₘ(output) : Code)) := by
  have h := ObjectRangeTable.table_reject program (entry site).tag n output (by
    intro candidate hCandidate hTag
    rw [entry_of_tag site candidate hCandidate hTag, table_eq]
    exact hBad)
  exact ObjectHorn.transport_negative (rules program) (FirstOrder.Derives.eq_symm
    (node_evaluate intrinsic_zfc_certificate_core 1 [(entry site).tag, n, output]))
    (ObjectHorn.negative intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.toArithmeticSupport h)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTable
