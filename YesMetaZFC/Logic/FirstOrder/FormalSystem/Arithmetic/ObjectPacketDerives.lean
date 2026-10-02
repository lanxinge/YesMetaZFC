import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketReject

/-! # 版本一传输包与对象树码之间的统一正负推导 -/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def template : FormulaTemplate.Binary where
  body := condition (.fvar .here) (.fvar (.there .here))

theorem template_apply {bound free : SetContext} (packet treeCode : SetTerm bound free) :
    template packet treeCode = condition packet treeCode := by
  simp [template, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    condition, ObjectHorn.condition, IntrinsicQuotation.node, structural_list_code_term, structural_raw_node_code_term,
    structural_code_tag, Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons]

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _

theorem packet_accept (input : Tree) : Acceptance rules (nodeValue 5 [NatPacket.encode input, treeValue input]) := by
  let root := nodeValue 5 [NatPacket.encode input, treeValue input]
  have hPacket : NatPacket.encode input ≤ root := field_le 5 (by simp)
  have hInput : treeValue input ≤ root := field_le 5 (by simp)
  have hBody : tree input 1 ≤ root := by rw [encode_eq] at hPacket; omega
  have h := Acceptance.of_rule (rules := rules) packetRule (by simp [rules])
    (fun i : Fin 3 => [treeValue input, NatPacket.encode input, tree input 1][i])
    (by
      change ∀ i : Fin 3, [treeValue input, NatPacket.encode input, tree input 1][i] ≤ root
      apply list_bounds [treeValue input, NatPacket.encode input, tree input 1] root
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption)
    (by intro guard h; exact False.elim (List.not_mem_nil h))
    (by
      intro premise hPremise
      dsimp only [packetRule] at hPremise
      rcases List.mem_cons.mp hPremise with rfl | hPremise
      · change Acceptance rules (nodeValue 1 [1, tree input 1, NatPacket.encode input])
        rw [encode_eq]
        exact affine_accept true 1 _ (by decide)
      · have hPremise := List.mem_singleton.mp hPremise
        subst premise
        exact tree_accept input 1)
  exact h

theorem packet_reject (packet : Nat) (input : Tree) (hBad : NatPacket.encode input ≠ packet) :
    Rejection rules (nodeValue 5 [packet, treeValue input]) := by
  apply Rejection.of_tagged heads_tagged 5 [packet, treeValue input]
  intro rule hRule values _ hHead _
  rw [rulesFor_five] at hRule
  have hRule := List.mem_singleton.mp hRule
  subst rule
  dsimp only [packetRule] at values hHead ⊢
  have h := ((nodeValue_eq_iff 5 5 [packet, treeValue input] [values 1, values 0]).mp hHead).2
  simp only [List.cons.injEq, and_true] at h
  by_cases hBody : tree input 1 = values 2
  · refine ⟨node (n := 3) 1 [.literal 1, .var 2, .var 1] , List.mem_cons_self, ?_⟩
    apply affine_reject true
    intro hGood
    apply hBad
    rw [encode_eq, hBody, h.1]
    exact hGood.2
  · refine ⟨node (n := 3) 3 [.var 0, .literal 1, .var 2] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 3 [values 0, 1, values 2])
    rw [← h.2]
    exact tree_reject input 1 _ hBody

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (packet : Nat) (input : Tree) (h : NatPacket.decode packet = some input) :
    Derives T [] (condition (numₘ(packet)) (numₘ(treeValue input) : Code)) := by
  have hCode := NatPacket.encode_of_decode h
  obtain ⟨rows, hRoot, hRows⟩ := hCode ▸ packet_accept input
  exact ObjectHorn.transport rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 5 [packet, treeValue input]))
    (ObjectHorn.positive C S hPower hInfinity rules _ rows hRoot hRows)

/-- 失败包和成功包的错误候选树使用同一个否定出口，无规范性前提。 -/
theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (packet : Nat) (input : Tree) (h : NatPacket.decode packet ≠ some input) :
    Derives T [] (¬ₘ condition (numₘ(packet)) (numₘ(treeValue input) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm (node_evaluate C 5 [packet, treeValue input]))
    (ObjectHorn.negative C A (packet_reject packet input
      (fun hCode => h ((NatPacket.decode_eq_some_iff packet input).mpr hCode))))

theorem positive_at_tree {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (packet : Nat) (input : Tree) (h : NatPacket.decode packet = some input) :
    Derives T [] (condition (numₘ(packet)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport rules (node_congr 5 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input)) .nil)))
    (positive C S hPower hInfinity packet input h)

theorem negative_at_tree {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (packet : Nat) (input : Tree) (h : NatPacket.decode packet ≠ some input) :
    Derives T [] (¬ₘ condition (numₘ(packet)) (IntrinsicQuotation.tree input)) :=
  ObjectHorn.transport_negative rules (node_congr 5 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input)) .nil))) (negative C A packet input h)

end YesMetaZFC.Automation.ObjectPacket
