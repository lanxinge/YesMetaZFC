import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.KernelQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjectQuotationBounds

/-! # 模式闭句的 Project 中间码与内核 quotation 的对象连接

中间 Project 码在最终输出后继中量化；接口只保留模式种类、参数数目、正文和内核码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaKernelJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def run (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) : Option Tree :=
  (SchemaClosure.run kind n input).bind ObjectProjectQuotation.run

def matrix {bound free : SetContext} (kind : SchemaTemplate.Kind) (middle n input output : SetTerm bound free) :
    SetFormula bound free :=
  SchemaJoin.condition (numₘ(kind.tag)) n input middle ∧ₘ ObjectProjectQuotation.condition middle output

@[simp] theorem matrix_substituteMapped {sb sf tb tf : SetContext} (kind : SchemaTemplate.Kind)
    (middle n input output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (matrix kind middle n input output).substituteMapped bs fs = matrix kind
      (middle.substituteMapped bs fs) (n.substituteMapped bs fs)
      (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [matrix, Formula.substituteMapped]

def template (kind : SchemaTemplate.Kind) : FormulaTemplate.Ternary where
  body := quantify 1 (Sₘ(.fvar (.there (.there .here))))
    (matrix kind (.bvar (project_bound_variable (0 : Fin 1))) (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))

def condition {bound free : SetContext} (kind : SchemaTemplate.Kind) (n input output : SetTerm bound free) :
    SetFormula bound free := template kind n input output

theorem template_delta0 (kind : SchemaTemplate.Kind) : Formula.IsDelta0 set_levy_bound (template kind).body :=
  quantify_delta0 _ _ _ (.conj (SchemaJoin.condition_delta0 _ _ _ _) (ObjectProjectQuotation.condition_delta0 _ _))

theorem condition_delta0 {bound free : SetContext} (kind : SchemaTemplate.Kind) (n input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition kind n input output) :=
  FormulaTemplate.instantiate_delta0 _ (template_delta0 kind) _

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (kind : SchemaTemplate.Kind)
    (n input output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (condition kind n input output).substituteMapped bs fs = condition kind
      (n.substituteMapped bs fs) (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp only [condition, FormulaTemplate.apply_three, FormulaTemplate.instantiate_substituteMapped]
  congr 1
  funext sort v
  cases v with
  | here => rfl
  | there v => cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v

theorem matrix_positive (kind : SchemaTemplate.Kind) (n : Nat) (input middle output : Tree)
    (hMiddle : SchemaClosure.run kind n input = some middle)
    (hOutput : ObjectProjectQuotation.run middle = some output) :
    Derives intrinsic_zfc_theory [] (matrix kind (numₘ(treeValue middle)) (numₘ(n))
      (numₘ(treeValue input)) (numₘ(treeValue output) : Code)) :=
  FirstOrder.Derives.conj_intro (SchemaJoin.positive kind n input _ (by rw [hMiddle]; rfl))
    (KernelQuotation.positive middle output hOutput)

theorem matrix_negative (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (output middle : Nat)
    (hBad : (run kind n input).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ matrix kind (numₘ(middle)) (numₘ(n))
      (numₘ(treeValue input)) (numₘ(output) : Code)) := by
  classical
  apply FirstOrder.Derives.neg_intro
  have hBoth := FirstOrder.Derives.assumption (T := intrinsic_zfc_theory)
    (Γ := [matrix kind (numₘ(middle)) (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)]) List.mem_cons_self
  by_cases hMiddle : (SchemaClosure.run kind n input).map treeValue = some middle
  · obtain ⟨closed, hClosed, rfl⟩ := Option.map_eq_some_iff.mp hMiddle
    apply FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_right hBoth)
    apply FirstOrder.Derives.context_weaken_cons
    apply KernelQuotation.negative
    simpa [run, hClosed] using hBad
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hBoth)
      (FirstOrder.Derives.context_weaken_cons (SchemaJoin.negative kind n input middle hMiddle))

theorem positive (kind : SchemaTemplate.Kind) (n : Nat) (input output : Tree)
    (h : run kind n input = some output) :
    Derives intrinsic_zfc_theory [] (condition kind (numₘ(n)) (numₘ(treeValue input)) (numₘ(treeValue output) : Code)) := by
  obtain ⟨middle, hMiddle, hOutput⟩ := Option.bind_eq_some_iff.mp h
  unfold condition template FormulaTemplate.apply_three FormulaTemplate.instantiate
  apply quantify_positive (values := fun _ => treeValue middle)
  · intro i
    simpa [Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.cons, finite_numeral_term] using
      numeral_mem_of_lt intrinsic_zfc_arithmetic_support.contains_successor
        (Nat.lt_succ_of_le (ObjectProjectQuotation.run_le middle output hOutput))
  · simpa [Term.substituteMapped, VariableSubstitution.cons, numeralSubstitution, project_bound_index, Variable.index] using
      matrix_positive kind n input middle output hMiddle hOutput

theorem negative (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (output : Nat)
    (h : (run kind n input).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition kind (numₘ(n)) (numₘ(treeValue input)) (numₘ(output) : Code)) := by
  unfold condition template FormulaTemplate.apply_three FormulaTemplate.instantiate
  apply quantify_negative intrinsic_zfc_certificate_core.toFiniteCore (limit := output + 1)
  · rfl
  · intro values _
    simpa [Term.substituteMapped, VariableSubstitution.cons, numeralSubstitution, project_bound_index, Variable.index] using
      matrix_negative kind n input output (values 0) h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaKernelJoin
