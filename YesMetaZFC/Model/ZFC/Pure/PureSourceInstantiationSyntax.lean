import YesMetaZFC.Model.ZFC.Pure.PureSourceInstantiation
import YesMetaZFC.Model.ZFC.Pure.PureSourceFormulaConstruction

/-! # 固定 AST 代入内部闭项后的良构性

束缚变量由类型化上下文保证范围，自由变量像必须在每个所需深度通过实际项检查。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding
open PureSourceTermConstruction PureSourceFormulaConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

mutual
theorem term_wellFormed (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} {freeCount : 𝒩.Carrier .set} (hFree : mem 𝒩 freeCount (w 𝒩))
    (hTerms : ∀ index, index < free.length →
      TermGraph ObjectFormulaSyntax.rules (numeral 𝒩 bound.length) freeCount (values index))
    {sort : SetSort} : (input : Term signature bound free sort) →
      TermGraph ObjectFormulaSyntax.rules (numeral 𝒩 bound.length) freeCount (term 𝒩 values input)
  | .bvar entry => variable_code h𝒩 syntax_support false entry.index
      (numeral_natural h𝒩 bound.length) hFree (numeral_lt h𝒩 (SyntaxDecode.variable_lt entry))
  | .fvar entry => hTerms entry.index (SyntaxDecode.variable_lt entry)
  | .app symbol args => application h𝒩 syntax_support (numeral_natural h𝒩 bound.length) hFree
      symbol (arguments 𝒩 values args) (arguments_natural h𝒩 hValues args)
      (arguments_wellFormed h𝒩 hValues hFree hTerms args)

theorem arguments_wellFormed (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} {freeCount : 𝒩.Carrier .set} (hFree : mem 𝒩 freeCount (w 𝒩))
    (hTerms : ∀ index, index < free.length →
      TermGraph ObjectFormulaSyntax.rules (numeral 𝒩 bound.length) freeCount (values index))
    {sorts : SetContext} : (input : Arguments signature bound free sorts) →
      ArgumentsGraph ObjectFormulaSyntax.rules (numeral 𝒩 bound.length) freeCount
        (numeral 𝒩 sorts.length) (fieldsCode 𝒩 (arguments 𝒩 values input))
  | .nil => arguments_nil h𝒩 syntax_support (numeral_natural h𝒩 bound.length) hFree
  | @Arguments.cons _ _ _ sort sorts head tail => arguments_cons h𝒩 syntax_support
      (numeral_natural h𝒩 bound.length) hFree (numeral_natural h𝒩 sorts.length)
      (term_natural h𝒩 hValues head) (fields_natural h𝒩 (arguments_natural h𝒩 hValues tail))
      (term_wellFormed h𝒩 hValues hFree hTerms head) (arguments_wellFormed h𝒩 hValues hFree hTerms tail)
end

theorem formula_wellFormed (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} {freeCount : 𝒩.Carrier .set} (hFree : mem 𝒩 freeCount (w 𝒩))
    (hTerms : ∀ depth index, index < free.length →
      TermGraph ObjectFormulaSyntax.rules (numeral 𝒩 depth) freeCount (values index))
    (input : SetFormula bound free) :
    FormulaGraph (numeral 𝒩 bound.length) freeCount (formula 𝒩 values input) := by
  induction input with
  | falsum =>
    exact constant h𝒩 0 (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules])
      (numeral_natural h𝒩 _) hFree
  | truth =>
    exact constant h𝒩 1 (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules])
      (numeral_natural h𝒩 _) hFree
  | rel symbol args =>
    exact relation h𝒩 (numeral_natural h𝒩 _) hFree symbol
      (arguments 𝒩 values args) (arguments_natural h𝒩 hValues args)
      (arguments_wellFormed h𝒩 hValues hFree (hTerms _) args)
  | equal left right =>
    exact equality h𝒩 (numeral_natural h𝒩 _) hFree
      (term_natural h𝒩 hValues left) (term_natural h𝒩 hValues right)
      (term_wellFormed h𝒩 hValues hFree (hTerms _) left) (term_wellFormed h𝒩 hValues hFree (hTerms _) right)
  | neg body ih =>
    exact unary h𝒩 4 false
      (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]) (numeral_natural h𝒩 _) hFree
      (formula_natural h𝒩 hValues body) (ih hTerms)
  | conj left right ihLeft ihRight =>
    exact binary h𝒩 5
      (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]) (numeral_natural h𝒩 _) hFree
      (formula_natural h𝒩 hValues left) (formula_natural h𝒩 hValues right) (ihLeft hTerms) (ihRight hTerms)
  | disj left right ihLeft ihRight =>
    exact binary h𝒩 6
      (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]) (numeral_natural h𝒩 _) hFree
      (formula_natural h𝒩 hValues left) (formula_natural h𝒩 hValues right) (ihLeft hTerms) (ihRight hTerms)
  | imp left right ihLeft ihRight =>
    exact binary h𝒩 7
      (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]) (numeral_natural h𝒩 _) hFree
      (formula_natural h𝒩 hValues left) (formula_natural h𝒩 hValues right) (ihLeft hTerms) (ihRight hTerms)
  | iff left right ihLeft ihRight =>
    exact binary h𝒩 8
      (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]) (numeral_natural h𝒩 _) hFree
      (formula_natural h𝒩 hValues left) (formula_natural h𝒩 hValues right) (ihLeft hTerms) (ihRight hTerms)
  | forallE sort body ih =>
    exact unary h𝒩 9 true
      (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]) (numeral_natural h𝒩 _) hFree
      (formula_natural h𝒩 hValues body) (ih hTerms)
  | existsE sort body ih =>
    exact unary h𝒩 10 true
      (by simp [ObjectFormulaSyntax.rules, ObjectFormulaSyntax.formulaRules]) (numeral_natural h𝒩 _) hFree
      (formula_natural h𝒩 hValues body) (ih hTerms)

/-- 当前 quotation 在其原始 bound/free 长度下通过完整公式检查。 -/
theorem original_wellFormed (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free : SetContext} (input : SetFormula bound free) :
    FormulaGraph (numeral 𝒩 bound.length) (numeral 𝒩 free.length)
      ((IntrinsicQuotation.quote input).eval (Env.empty : Env 𝒩 [] [])) := by
  rw [← original_quote]
  exact formula_wellFormed h𝒩 (original_natural h𝒩) (numeral_natural h𝒩 free.length)
    (fun depth index hIndex => variable_code h𝒩 syntax_support true index
      (numeral_natural h𝒩 depth) (numeral_natural h𝒩 free.length) (numeral_lt h𝒩 hIndex)) input

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
