import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchema
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredCertificateCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.FiniteSequence

/-!
# `ProofT` 的固定公理表

固定表只保存自然数证书与闭内在公式码项。闭项类型已经保证排序、bound 和 free
上下文正确，因此表结构不再携带 `Admissible` 或变量支撑字段。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open StructuredCertificateCondition
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

abbrev closed_term := SetTerm [] []

/-- 可被对象 verifier 消费的有限固定公理表。 -/
structure FixedAxiomTable where
  rows : List (Nat × closed_term)

namespace FixedAxiomTable

/-! ## 直接序列生产 -/

/-- 固定表中的公式码列；表项类型已经保证每项是闭内在项。 -/
def formula_elements (A : FixedAxiomTable) : List closed_term :=
  A.rows.map Prod.snd

/-- 固定表中的理论证书码列；内层 payload 是行证书 numeral。 -/
def certificate_elements (A : FixedAxiomTable) : List closed_term :=
  A.rows.map (fun row => theory_certificate_code (numₘ(row.1)))

/-- 固定表公式码列的标准有限图。 -/
def formula_sequence (A : FixedAxiomTable) : closed_term :=
  standard_sequence A.formula_elements

/-- 固定表完整理论证书码列的标准有限图。 -/
def certificate_sequence (A : FixedAxiomTable) : closed_term :=
  standard_sequence A.certificate_elements

@[simp] theorem formula_elements_length (A : FixedAxiomTable) :
    A.formula_elements.length = A.rows.length := by
  simp [formula_elements]

@[simp] theorem certificate_elements_length (A : FixedAxiomTable) :
    A.certificate_elements.length = A.rows.length := by
  simp [certificate_elements]

/-- 将闭表项提升到任意内在上下文。 -/
def row_term {bound free : SetContext} (term : closed_term) :
    SetTerm bound free :=
  Term.embedClosed bound free term

@[simp] theorem row_term_empty (term : closed_term) :
    row_term (bound := []) (free := []) term = term := by
  exact Term.rec
    (motive_1 := fun sort term =>
      row_term (bound := []) (free := []) term = term)
    (motive_2 := fun sorts arguments =>
      Arguments.embedClosed [] [] arguments = arguments)
    (fun entry => nomatch entry)
    (fun entry => nomatch entry)
    (fun function _ ih => congrArg (Term.app function) ih)
    rfl
    (fun _ _ ihHead ihTail => congr (congrArg Arguments.cons ihHead) ihTail)
    term

/-- 固定表行编译为内在二元分支，公式和证书槽位由上下文索引固定。 -/
def row_branch (row : Nat × closed_term) : IntrinsicSchema.BinaryBranch where
  tag := row.1
  condition := fun formula certificate =>
    ((certificate ≐ₘ numₘ(row.1)) ∧ₘ
      (formula ≐ₘ row_term row.2))
  delta0 := by
    intro bound free formula certificate
    exact Formula.IsDelta0.conj
      (Formula.IsDelta0.equal certificate (numₘ(row.1)))
      (Formula.IsDelta0.equal formula (row_term row.2))

/-- 固定表的逐项有限析取。 -/
def condition_rows {bound free : SetContext}
    (rows : List (Nat × closed_term))
    (formula certificate : SetTerm bound free) : SetFormula bound free :=
  IntrinsicSchema.binary_condition_list
    (rows.map row_branch) formula certificate

/-- 一张固定公理表的对象 verifier 条件。 -/
def condition {bound free : SetContext}
    (A : FixedAxiomTable)
    (formula certificate : SetTerm bound free) : SetFormula bound free :=
  condition_rows A.rows formula certificate

/-- 空固定表。 -/
def empty : FixedAxiomTable where
  rows := []

/-- 单条固定公理。 -/
def singleton (certificate : Nat) (formula : closed_term) : FixedAxiomTable where
  rows := [(certificate, formula)]

/-- 有限扩张通过追加表实现。 -/
def append (A B : FixedAxiomTable) : FixedAxiomTable where
  rows := A.rows ++ B.rows

@[simp] theorem condition_rows_nil
    {bound free : SetContext}
    (formula certificate : SetTerm bound free) :
    condition_rows [] formula certificate = Formula.falsum :=
  by
    simp [condition_rows, IntrinsicSchema.binary_condition_list]

@[simp] theorem condition_rows_cons
    {bound free : SetContext}
    (row : Nat × closed_term)
    (rows : List (Nat × closed_term))
    (formula certificate : SetTerm bound free) :
    condition_rows (row :: rows) formula certificate =
      (((certificate ≐ₘ numₘ(row.1)) ∧ₘ
          (formula ≐ₘ row_term row.2)) ∨ₘ
        condition_rows rows formula certificate) :=
  by
    simp [condition_rows, IntrinsicSchema.binary_condition_list, row_branch]

theorem condition_rows_delta0
    {bound free : SetContext}
    (rows : List (Nat × closed_term))
    (formula certificate : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (condition_rows rows formula certificate) := by
  simpa [condition_rows] using
    IntrinsicSchema.binary_condition_list_delta0
      (rows.map row_branch) formula certificate

theorem condition_delta0
    (A : FixedAxiomTable)
    {bound free : SetContext}
    (formula certificate : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (A.condition formula certificate) :=
  condition_rows_delta0 A.rows formula certificate

theorem condition_rows_neg
    {T : SetTheory}
    {free : SetContext}
    {rows : List (Nat × closed_term)}
    {Γ : Context signature free}
    {formula certificate : SetOpenTerm free}
    (hReject :
      ∀ row, row ∈ rows →
        Γ ⊢ₘ[T] ¬ₘ
          (((certificate ≐ₘ numₘ(row.1)) ∧ₘ
            (formula ≐ₘ row_term row.2)))) :
    Γ ⊢ₘ[T] ¬ₘ condition_rows rows formula certificate := by
  simpa [condition_rows] using
    IntrinsicSchema.binary_condition_list_neg
      (branches := rows.map row_branch)
      (formula := formula) (certificate := certificate)
      (by
        intro branch hBranch
        rcases List.mem_map.mp hBranch with ⟨row, hRow, rfl⟩
        simpa [row_branch] using hReject row hRow)

theorem condition_neg
    {T : SetTheory}
    (A : FixedAxiomTable)
    {free : SetContext}
    {Γ : Context signature free}
    {formula certificate : SetOpenTerm free}
    (hReject :
      ∀ row, row ∈ A.rows →
        Γ ⊢ₘ[T] ¬ₘ
          (((certificate ≐ₘ numₘ(row.1)) ∧ₘ
            (formula ≐ₘ row_term row.2)))) :
    Γ ⊢ₘ[T] ¬ₘ A.condition formula certificate := by
  exact condition_rows_neg hReject

/-! ## 模板化证明图 -/

abbrev condition_template_free : SetContext :=
  [SetSort.set, SetSort.set]

/-- 固定表条件的内在二元模板。 -/
def condition_template (A : FixedAxiomTable) : FormulaTemplate.Binary where
  body := A.condition
    (.fvar .here : SetOpenTerm condition_template_free)
    (.fvar (.there .here) : SetOpenTerm condition_template_free)

/-- 固定公理表直接给出一个 `Delta0` proof graph。 -/
def proof_graph (A : FixedAxiomTable) : Delta0ProofGraph where
  condition := A.condition_template
  delta0 := by
    intro bound free formula certificate
    exact Formula.IsDelta0.substituteMapped
      (boundSubstitution := VariableSubstitution.empty)
      (freeSubstitution :=
        VariableSubstitution.cons formula
          (VariableSubstitution.cons certificate
            VariableSubstitution.empty))
      (A.condition_delta0
        (.fvar .here : SetOpenTerm condition_template_free)
        (.fvar (.there .here) : SetOpenTerm condition_template_free))

theorem condition_sigma1
    (A : FixedAxiomTable)
    {bound free : SetContext}
    (formula certificate : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (A.condition formula certificate) :=
  (A.condition_delta0 formula certificate).to_sigma1

theorem condition_pi1
    (A : FixedAxiomTable)
    {bound free : SetContext}
    (formula certificate : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (A.condition formula certificate) :=
  (A.condition_delta0 formula certificate).to_pi1

end FixedAxiomTable
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
