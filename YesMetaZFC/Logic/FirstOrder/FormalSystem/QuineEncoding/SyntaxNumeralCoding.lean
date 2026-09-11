import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormalSystem

/-!
# 标准有限 numeral 的结构码命名

本模块直接递归生成内在有限 numeral 的 Quine 结构码，并在对象语言中加入相应
的递归函数合同。它只依赖结构语法编码和自然数基础，不引入 token、字符串、
具名 binder 或自由变量编号保留区间。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace QuineEncoding

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols

set_option autoImplicit false

/-! ## 宿主结构码 -/

/-- 有限 numeral 的直接 Quine 结构码。 -/
def syntax_numeral_code : Nat → Code
  | 0 => const_codeₘ(numₘ(FunctionSymbol.emptySet.ctorIdx))
  | number + 1 =>
      app_codeₘ(
        numₘ(signature.funcArity FunctionSymbol.successor),
        numₘ(FunctionSymbol.successor.ctorIdx),
        code_consₘ(syntax_numeral_code number, code_nilₘ))

@[simp]
theorem syntax_numeral_code_eq_quote_term (number : Nat) :
    syntax_numeral_code number =
      (quote_term
        (finite_numeral_term (bound := []) (free := []) number) :
        Code) := by
  induction number with
  | zero =>
      simp [syntax_numeral_code, finite_numeral_term,
        quote_term, signature]
  | succ number ih =>
      simp [syntax_numeral_code, finite_numeral_term,
        quote_term, quote_arguments, signature, ih]

/-! ## 对象侧递归定义 -/

def syntax_numeral_code_condition {bound free : SetContext}
    (number candidate : SetTerm bound free) : SetFormula bound free :=
  let numberOne := number.weakenFree SetSort.set
  let candidateOne := candidate.weakenFree SetSort.set
  let predecessor : SetTerm bound (SetSort.set :: free) := .fvar .here
  (number ∈ₘ ωₘ) ⟶ₘ
    (((number ≐ₘ numₘ(0)) ∧ₘ
        (candidate ≐ₘ const_codeₘ(numₘ(FunctionSymbol.emptySet.ctorIdx)))) ∨ₘ
      (((predecessor ∈ₘ ωₘ) ∧ₘ
          (numberOne ≐ₘ Sₘ(predecessor))) ∧ₘ
        (candidateOne ≐ₘ
          app_codeₘ(
            numₘ(signature.funcArity FunctionSymbol.successor),
            numₘ(FunctionSymbol.successor.ctorIdx),
            code_consₘ(
              syntax_numeral_code_term predecessor,
              code_nilₘ)))).existsFreeTop SetSort.set)

def syntax_numeral_code_definition_instance {bound free : SetContext}
    (number candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ syntax_num_codeₘ(number)) ↔ₘ
    syntax_numeral_code_condition number candidate

def syntax_numeral_code_definition_axiom : SetSentence :=
  Metatheory.Formula.forall_close
    (syntax_numeral_code_definition_instance
      (.fvar (.there .here) : SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here : SetOpenTerm [SetSort.set, SetSort.set]))

def syntax_numeral_coding_theory : SetTheory :=
  Theory.insert syntax_numeral_code_definition_axiom
    formal_language_encoding_theory

derive_theory_subset formal_language_encoding_theory ⊆ syntax_numeral_coding_theory

private theorem syntax_numeral_code_axiom_derives :
    ([] : Context signature []) ⊢ₘ[syntax_numeral_coding_theory]
      Formula.fromSentence syntax_numeral_code_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

theorem syntax_numeral_code_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (number candidate : SetOpenTerm free) :
    Γ ⊢ₘ[syntax_numeral_coding_theory]
      syntax_numeral_code_definition_instance number candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    syntax_numeral_code_definition_instance
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons number VariableSubstitution.empty)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ (by
      simpa [syntax_numeral_code_definition_axiom, body] using
        syntax_numeral_code_axiom_derives)
  simpa [body, τ, syntax_numeral_code_definition_instance,
    syntax_numeral_code_condition, Formula.substituteFree,
    Substitution.free_map, Formula.substitute, Formula.substituteMapped,
    Term.substituteFree, Term.substitute, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftFree,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

end QuineEncoding
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
