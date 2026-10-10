import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteJoin
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FixedAxiomTable

/-! # 自然数到当前树码的有限表表示

输出常量保留为紧凑树项。正负推导只依赖有限算术核；表可以有重复键，
否定接口明确要求排除所有匹配行，不偷偷把关系表解释为首项查找。
-/
namespace YesMetaZFC.Automation.ObjectFiniteTable
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

abbrev Entry := Nat × Tree

def branch {bound free : SetContext} (entry : Entry)
    (input output : SetTerm bound free) : SetFormula bound free :=
  (input ≐ₘ numₘ(entry.1)) ∧ₘ (FixedAxiomTable.row_term (IntrinsicQuotation.tree entry.2) ≐ₘ output)

def condition {bound free : SetContext} (entries : List Entry)
    (input output : SetTerm bound free) : SetFormula bound free :=
  anyOf (entries.map (fun entry => branch entry input output))

@[simp] theorem condition_substituteMapped (entries : List Entry)
    {sb sf tb tf : SetContext} (input output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition entries input output).substituteMapped bs fs =
      condition entries (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition, branch, FixedAxiomTable.row_term, Function.comp_def, Formula.substituteMapped]

def template (entries : List Entry) : FormulaTemplate.Binary where
  body := condition entries (.fvar .here) (.fvar (.there .here))

@[simp] theorem template_apply (entries : List Entry) {bound free : SetContext}
    (input output : SetTerm bound free) : template entries input output = condition entries input output := by
  simp [template, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem condition_delta0 (entries : List Entry) {bound free : SetContext}
    (input output : SetTerm bound free) : Formula.IsDelta0 set_levy_bound (condition entries input output) := by
  apply anyOf_delta0
  intro φ hφ
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hφ
  exact .conj (.equal _ _) (.equal _ _)

theorem template_delta0 (entries : List Entry) :
    Formula.IsDelta0 set_levy_bound (template entries).body := condition_delta0 entries _ _

theorem positive_at_tree {T : SetTheory} (entries : List Entry) (entry : Entry)
    (hEntry : entry ∈ entries) :
    Derives T [] (condition entries (numₘ(entry.1)) (IntrinsicQuotation.tree entry.2)) := by
  apply anyOf_intro (List.mem_map.mpr ⟨entry, hEntry, rfl⟩)
  unfold branch
  rw [FixedAxiomTable.row_term_empty]
  exact FirstOrder.Derives.conj_intro (Metatheory.Derives.equality_refl _)
    (Metatheory.Derives.equality_refl _)

theorem positive {T : SetTheory} (C : CertificateCore T) (entries : List Entry) (entry : Entry)
    (hEntry : entry ∈ entries) :
    Derives T [] (condition entries (numₘ(entry.1)) (numₘ(treeValue entry.2) : Code)) := by
  apply anyOf_intro (List.mem_map.mpr ⟨entry, hEntry, rfl⟩)
  unfold branch
  rw [FixedAxiomTable.row_term_empty]
  exact FirstOrder.Derives.conj_intro (Metatheory.Derives.equality_refl _) (tree_evaluate C entry.2)

/-- 候选输出是任意自然数，无须预先证明它表示树。 -/
theorem negative {T : SetTheory} (C : CertificateCore T) (entries : List Entry) (input output : Nat)
    (h : ∀ entry, entry ∈ entries → input = entry.1 → treeValue entry.2 ≠ output) :
    Derives T [] (¬ₘ condition entries (numₘ(input)) (numₘ(output) : Code)) := by
  apply anyOf_negative
  intro φ hφ
  obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hφ
  unfold branch
  rw [FixedAxiomTable.row_term_empty]
  apply FirstOrder.Derives.neg_intro
  have hBoth := FirstOrder.Derives.assumption (T := T)
    (Γ := [(numₘ(input) ≐ₘ numₘ(entry.1)) ∧ₘ (IntrinsicQuotation.tree entry.2 ≐ₘ numₘ(output))])
    List.mem_cons_self
  by_cases hKey : input = entry.1
  · have hNumeric := Metatheory.Derives.equality_trans
      (FirstOrder.Derives.eq_symm (FirstOrder.Derives.context_weaken_cons (tree_evaluate C entry.2)))
      (FirstOrder.Derives.conj_elim_right hBoth)
    exact FirstOrder.Derives.neg_elim hNumeric
      (FirstOrder.Derives.context_weaken_cons (C.numeral_ne (h entry hEntry hKey)))
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hBoth)
      (FirstOrder.Derives.context_weaken_cons (C.numeral_ne hKey))

end YesMetaZFC.Automation.ObjectFiniteTable
