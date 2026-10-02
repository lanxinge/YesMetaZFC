import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjectQuotationReject

/-! # 固定 quotation 转换图的普通正负推导 -/
namespace YesMetaZFC.Automation.ObjectProjectQuotation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (input output : Tree) (h : run input = some output) :
    Derives T [] (condition (numₘ(treeValue input)) (numₘ(treeValue output) : Code)) := by
  obtain ⟨rows, hRoot, hRows⟩ := run_accept input output h
  exact ObjectHorn.transport rules (FirstOrder.Derives.eq_symm (node_evaluate C 0 [treeValue input, treeValue output]))
    (ObjectHorn.positive C S hPower hInfinity rules _ rows hRoot hRows)

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (input : Tree) (output : Nat) (h : (run input).map treeValue ≠ some output) :
    Derives T [] (¬ₘ condition (numₘ(treeValue input)) (numₘ(output) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm (node_evaluate C 0 [treeValue input, output]))
    (ObjectHorn.negative C A (run_reject input output h))

theorem positive_at_tree {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (input output : Tree) (h : run input = some output) :
    Derives T [] (condition (IntrinsicQuotation.tree input) (IntrinsicQuotation.tree output)) :=
  ObjectHorn.transport rules (node_congr 0
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input))
      (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C output)) .nil)))
    (positive C S hPower hInfinity input output h)

end YesMetaZFC.Automation.ObjectProjectQuotation
