import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaEnvelope
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeBounds

/-! # 暴露参数与正文槽位的模式外壳等式 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaEnvelope
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation ProofCode
open _root_.YesMetaZFC.Automation ObjectHorn ObjectCodeBounds
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def link {bound free : SetContext} (tag : Nat) (input count body : SetTerm bound free) : SetFormula bound free :=
  input ≐ₘ (pattern tag).term count body

@[simp] theorem link_substituteMapped {sb sf tb tf : SetContext} (tag : Nat)
    (input count body : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (link tag input count body).substituteMapped bs fs = link tag
      (input.substituteMapped bs fs) (count.substituteMapped bs fs) (body.substituteMapped bs fs) := by
  simp [link, Formula.substituteMapped]

theorem link_positive (tag input count body : Nat) (h : input = (pattern tag).eval count body) :
    Derives intrinsic_zfc_theory [] (link tag (numₘ(input)) (numₘ(count)) (numₘ(body) : Code)) := by
  rw [h]
  exact Metatheory.Derives.equality_symm ((pattern tag).evaluate intrinsic_zfc_certificate_core count body)

theorem link_negative (tag input count body : Nat) (h : input ≠ (pattern tag).eval count body) :
    Derives intrinsic_zfc_theory [] (¬ₘ link tag (numₘ(input)) (numₘ(count)) (numₘ(body) : Code)) := by
  apply FirstOrder.Derives.neg_intro
  exact FirstOrder.Derives.neg_elim
    (Metatheory.Derives.equality_trans (FirstOrder.Derives.assumption List.mem_cons_self)
      (FirstOrder.Derives.context_weaken_cons ((pattern tag).evaluate intrinsic_zfc_certificate_core count body)))
    (FirstOrder.Derives.context_weaken_cons (intrinsic_zfc_certificate_core.numeral_ne h))

theorem count_le (tag count : Nat) (body : Tree) : count ≤ treeValue (.node tag [leaf count, body]) := by
  have hCount : count ≤ treeValue (leaf count) :=
    Nat.le_trans (left_le_godel_pair_value count 1) (Nat.le_succ _)
  rw [treeValue_node]
  exact Nat.le_trans hCount (node_field_le tag [treeValue (leaf count), treeValue body] _ (by simp))

theorem body_le (tag count : Nat) (body : Tree) : treeValue body ≤ treeValue (.node tag [leaf count, body]) := by
  rw [treeValue_node]
  exact node_field_le tag [treeValue (leaf count), treeValue body] _ (by simp)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaEnvelope
