import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues

/-! # 固定个数的中间码存在连接所需的公共推导接口 -/
namespace YesMetaZFC.Automation.ObjectHorn
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT QuineEncoding
open Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem allOf_negative_of_member {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    {formulas : List (SetOpenFormula free)} {φ : SetOpenFormula free}
    (hMem : φ ∈ formulas) (hNeg : Derives T Γ (¬ₘ φ)) : Derives T Γ (¬ₘ allOf formulas) := by
  apply FirstOrder.Derives.neg_intro
  exact FirstOrder.Derives.neg_elim
    (allOf_elim (FirstOrder.Derives.assumption List.mem_cons_self) hMem)
    (FirstOrder.Derives.context_weaken_cons hNeg)

@[simp] theorem node_substituteMapped {sb sf tb tf : SetContext} (tag : Nat) (fields : List (SetTerm sb sf))
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (IntrinsicQuotation.node tag fields).substituteMapped bs fs =
      IntrinsicQuotation.node tag (fields.map (fun t => t.substituteMapped bs fs)) := by
  simp [IntrinsicQuotation.node, structural_list_code_term_substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped]

@[simp] theorem condition_substituteMapped (rules : List Rule) {sb sf tb tf : SetContext} (row : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition rules row).substituteMapped bs fs = condition rules (row.substituteMapped bs fs) := by
  simp [condition, Term.substituteMapped, Arguments.substituteMapped]

end YesMetaZFC.Automation.ObjectHorn
