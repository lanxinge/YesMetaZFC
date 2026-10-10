import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1AxiomPresentation

/-! # 任意有限闭公理表的具体对象表示

公理表及其证书编号固定，待检查闭句和自然数证书任意。比较保留当前内核 quotation，
接受与拒绝均编译为普通 Hilbert 推导；编号允许重复，检查遍历所有匹配行。
-/
namespace YesMetaZFC.Automation.ObjectFiniteAxioms
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding IntrinsicQuotation ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def axioms (sentences : List SetSentence) : SetTheory := fun φ => φ ∈ sentences

def certificates (sentences : List SetSentence) : AxiomPresentation (axioms sentences) where
  Certificate := Fin sentences.length
  sentence i := sentences[i]
  sound i := List.getElem_mem i.isLt
  complete := by
    intro φ h
    obtain ⟨i, hi, hφ⟩ := List.mem_iff_getElem.mp h
    exact ⟨⟨i, hi⟩, hφ⟩

def entries (sentences : List SetSentence) (key : Nat → Nat) : List ObjectFiniteTable.Entry :=
  (List.finRange sentences.length).map (fun i => (key i.val, SyntaxEncode.formula sentences[i]))

def checked (sentences : List SetSentence) (key : Nat → Nat) (packet : Nat) (φ : SetSentence) : Bool :=
  (List.finRange sentences.length).any (fun i =>
    decide (packet = key i.val) && (AxiomPresentation.singleton sentences[i]).check () φ)

theorem checked_eq_true_iff (sentences : List SetSentence) (key : Nat → Nat) (packet : Nat) (φ : SetSentence) :
    checked sentences key packet φ = true ↔
      ∃ i : Fin sentences.length, packet = key i.val ∧ sentences[i] = φ := by
  simp [checked, List.any_eq_true, AxiomPresentation.check_eq_true_iff, AxiomPresentation.singleton]

theorem checked_sound {sentences : List SetSentence} {key : Nat → Nat} {packet : Nat} {φ : SetSentence}
    (h : checked sentences key packet φ = true) : axioms sentences φ := by
  obtain ⟨i, _, rfl⟩ := (checked_eq_true_iff sentences key packet φ).mp h
  exact List.getElem_mem i.isLt

theorem checked_complete (sentences : List SetSentence) (key : Nat → Nat) {φ : SetSentence}
    (h : axioms sentences φ) : ∃ packet, checked sentences key packet φ = true := by
  obtain ⟨i, hi, hφ⟩ := List.mem_iff_getElem.mp h
  exact ⟨key i, (checked_eq_true_iff sentences key (key i) φ).mpr ⟨⟨i, hi⟩, rfl, hφ⟩⟩

theorem positive {T : SetTheory} (sentences : List SetSentence) (key : Nat → Nat)
    {packet : Nat} {φ : SetSentence} (h : checked sentences key packet φ = true) :
    Derives T [] (ObjectFiniteTable.condition (entries sentences key) (numₘ(packet)) (IntrinsicQuotation.quote φ)) := by
  obtain ⟨i, rfl, rfl⟩ := (checked_eq_true_iff sentences key packet φ).mp h
  exact ObjectFiniteTable.positive_at_tree _ _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

theorem negative {T : SetTheory} (C : CertificateCore T) (sentences : List SetSentence) (key : Nat → Nat)
    {packet : Nat} {φ : SetSentence} (h : checked sentences key packet φ = false) :
    Derives T [] (¬ₘ ObjectFiniteTable.condition (entries sentences key) (numₘ(packet)) (IntrinsicQuotation.quote φ)) := by
  apply anyOf_negative
  intro branch hBranch
  obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hBranch
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hEntry
  unfold ObjectFiniteTable.branch
  rw [FixedAxiomTable.row_term_empty]
  apply FirstOrder.Derives.neg_intro
  have hBoth := FirstOrder.Derives.assumption (T := T)
    (Γ := [(numₘ(packet) ≐ₘ numₘ(key i.val)) ∧ₘ (IntrinsicQuotation.quote sentences[i] ≐ₘ IntrinsicQuotation.quote φ)]) List.mem_cons_self
  by_cases hKey : packet = key i.val
  · have hNe : sentences[i] ≠ φ := by
      intro hEq
      have hTrue := (checked_eq_true_iff sentences key packet φ).mpr ⟨i, hKey, hEq⟩
      rw [h] at hTrue
      cases hTrue
    exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_right hBoth)
      (FirstOrder.Derives.context_weaken_cons (IntrinsicQuotation.quote_ne C hNe))
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hBoth)
      (FirstOrder.Derives.context_weaken_cons (C.numeral_ne hKey))

/-- 有限公理成员关系的全部表示字段，不要求额外表示假设。 -/
def presentation {T : SetTheory} (C : CertificateCore T) (sentences : List SetSentence) (key : Nat → Nat) :
    Delta1AxiomPresentation T (axioms sentences) where
  condition := ObjectFiniteTable.template (entries sentences key)
  delta0 packet output := by
    rw [ObjectFiniteTable.template_apply]
    exact ObjectFiniteTable.condition_delta0 _ _ _
  checked := checked sentences key
  checked_sound := checked_sound
  checked_complete := checked_complete sentences key
  condition_positive h := by
    rw [ObjectFiniteTable.template_apply]
    exact positive sentences key h
  condition_negative h := by
    rw [ObjectFiniteTable.template_apply]
    exact negative C sentences key h

end YesMetaZFC.Automation.ObjectFiniteAxioms
