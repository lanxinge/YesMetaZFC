import YesMetaZFC.Logic.FirstOrder.FormalSystem.LanguageEncoding
import YesMetaZFC.Logic.FirstOrder.Hilbert.Translation

/-!
# 可编号单排序签名的 Quine 结构编码

本层只接收内在良构的一阶语法，并总函数地产生带标签的 Quine 结构码：

* bound/free 变量由类型化上下文中的 de Bruijn 位置直接给出；
* 异质参数列按其类型索引递归编码；
* 全称节点不携带名字，因此没有新鲜性或停机证明义务；
* 对象侧代码始终落在闭式 `SetTerm [] []` 中。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped FormalSystem.Symbols

universe u v w

/-- 关系符号在结构码中采用隶属节点或普通谓词节点。 -/
inductive QuotationRelationKind where
  | membership
  | predicate
  deriving DecidableEq, Repr

/-- 可编号单排序签名的 Quine 编码数据。 -/
class QuotationNumbering (σ : Signature.{u, v, w}) where
  objectSort : σ.SortSymbol
  sort_eq_object : ∀ sort, sort = objectSort
  function_number : σ.FuncSymbol → Nat
  relation_number : σ.RelSymbol → Nat
  function_number_injective : Function.Injective function_number
  relation_number_injective : Function.Injective relation_number
  relation_kind : σ.RelSymbol → QuotationRelationKind :=
    fun _ => .predicate
  membership_domain : ∀ relation,
    relation_kind relation = .membership →
      σ.relDomain relation = [objectSort, objectSort]
  membership_unique : ∀ {left right},
    relation_kind left = .membership →
      relation_kind right = .membership → left = right

namespace QuotationNumbering

theorem sort_eq {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (sort : σ.SortSymbol) :
    sort = numbering.objectSort :=
  numbering.sort_eq_object sort

theorem object_eq_sort {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (sort : σ.SortSymbol) :
    numbering.objectSort = sort :=
  (numbering.sort_eq_object sort).symm

end QuotationNumbering

abbrev Code := SetTerm [] []

mutual

/-- 内在项的直接结构码。 -/
def quote_term {σ : Signature.{u, v, w}} [QuotationNumbering σ]
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    Term σ bound free sort → Code
  | .bvar entry => bound_var_codeₘ(numₘ(entry.index))
  | .fvar entry => free_var_codeₘ(numₘ(entry.index))
  | .app function arguments =>
      match σ.funcDomain function with
      | [] =>
          const_codeₘ(numₘ(QuotationNumbering.function_number function))
      | _ :: _ =>
          app_codeₘ(
            numₘ(σ.funcArity function),
            numₘ(QuotationNumbering.function_number function),
            quote_arguments arguments)

/-- 内在异质参数列的 Quine 列表码。 -/
def quote_arguments {σ : Signature.{u, v, w}} [QuotationNumbering σ]
    {bound free : SortContext σ} {sorts : List σ.SortSymbol} :
    Arguments σ bound free sorts → Code
  | .nil => code_nilₘ
  | .cons term rest =>
      code_consₘ(quote_term term, quote_arguments rest)

end

mutual

/-- bound-closed 项嵌入任意局部 binder 后，Quine 结构码不变。 -/
@[simp] theorem quote_term_embedBoundClosed
    {σ : Signature.{u, v, w}} [QuotationNumbering σ]
    {free : SortContext σ} {sort : σ.SortSymbol}
    (targetBound : SortContext σ) (term : Term σ [] free sort) :
    quote_term (term.embedBoundClosed targetBound) = quote_term term := by
  cases term with
  | bvar entry => exact nomatch entry
  | fvar entry => simp [quote_term]
  | app function arguments =>
      simp [quote_term, quote_arguments_embedBoundClosed]

/-- bound-closed 参数列嵌入任意局部 binder 后，Quine 结构码不变。 -/
@[simp] theorem quote_arguments_embedBoundClosed
    {σ : Signature.{u, v, w}} [QuotationNumbering σ]
    {free : SortContext σ} {sorts : List σ.SortSymbol}
    (targetBound : SortContext σ)
    (arguments : Arguments σ [] free sorts) :
    quote_arguments (arguments.embedBoundClosed targetBound) =
      quote_arguments arguments := by
  cases arguments with
  | nil => simp [quote_arguments]
  | cons head tail =>
      simp [quote_arguments, quote_term_embedBoundClosed,
        quote_arguments_embedBoundClosed]

end

def quote_membership_arguments
    {σ : Signature.{u, v, w}} [numbering : QuotationNumbering σ]
    {bound free : SortContext σ} (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (hKind : numbering.relation_kind relation = .membership) : Code :=
  let typedArguments : Arguments σ bound free
      [numbering.objectSort, numbering.objectSort] :=
    numbering.membership_domain relation hKind ▸ arguments
  match typedArguments with
  | .cons left (.cons right .nil) =>
      mem_codeₘ(quote_term left, quote_term right)

/-- 内在关系原子的直接结构码。 -/
def quote_relation {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    {bound free : SortContext σ} (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation)) : Code :=
  match hKind : numbering.relation_kind relation with
  | .membership =>
      quote_membership_arguments relation arguments hKind
  | .predicate =>
      pred_codeₘ(
        numₘ(σ.relArity relation),
        numₘ(numbering.relation_number relation),
        quote_arguments arguments)

theorem quote_relation_membership_eq
    {σ : Signature.{u, v, w}} [numbering : QuotationNumbering σ]
    {bound free : SortContext σ} (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (hKind : numbering.relation_kind relation = .membership) :
    quote_relation relation arguments =
      quote_membership_arguments relation arguments hKind := by
  unfold quote_relation
  split
  · rename_i h
    have hEq : h = hKind := Subsingleton.elim _ _
    cases hEq
    rfl
  · rename_i h
    have hFalse :
        (QuotationRelationKind.membership : QuotationRelationKind) =
          QuotationRelationKind.predicate :=
      hKind.symm.trans h
    cases hFalse

theorem quote_membership_arguments_cons_eq
    {σ : Signature.{u, v, w}} [numbering : QuotationNumbering σ]
    {bound free : SortContext σ} (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (hKind : numbering.relation_kind relation = .membership)
    (left right : Term σ bound free numbering.objectSort)
    (hArguments :
      numbering.membership_domain relation hKind ▸ arguments =
        Arguments.cons left (Arguments.cons right Arguments.nil)) :
    quote_membership_arguments relation arguments hKind =
      mem_codeₘ(quote_term left, quote_term right) := by
  unfold quote_membership_arguments
  rw [hArguments]
  rfl

theorem quote_relation_predicate_eq
    {σ : Signature.{u, v, w}} [numbering : QuotationNumbering σ]
    {bound free : SortContext σ} (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation))
    (hKind : numbering.relation_kind relation = .predicate) :
    quote_relation relation arguments =
      pred_codeₘ(
        numₘ(σ.relArity relation),
        numₘ(numbering.relation_number relation),
        quote_arguments arguments) := by
  unfold quote_relation
  split
  · rename_i h
    have hFalse :
        (QuotationRelationKind.predicate : QuotationRelationKind) =
          QuotationRelationKind.membership :=
      hKind.symm.trans h
    cases hFalse
  · rename_i h
    have hEq : h = hKind := Subsingleton.elim _ _
    cases hEq
    rfl

/-- Hilbert 核公式的直接结构码。 -/
def quote_hilbert {σ : Signature.{u, v, w}} [QuotationNumbering σ]
    {bound free : SortContext σ} : Formula σ bound free → Code
  | .falsum =>
      neg_codeₘ(all_codeₘ(eq_codeₘ(
        bound_var_codeₘ(numₘ(0)), bound_var_codeₘ(numₘ(0)))))
  | .truth =>
      all_codeₘ(eq_codeₘ(
        bound_var_codeₘ(numₘ(0)), bound_var_codeₘ(numₘ(0))))
  | .rel relation arguments => quote_relation relation arguments
  | .equal left right => eq_codeₘ(quote_term left, quote_term right)
  | .neg body => neg_codeₘ(quote_hilbert body)
  | .conj left right =>
      neg_codeₘ(imp_codeₘ(quote_hilbert left, neg_codeₘ(quote_hilbert right)))
  | .disj left right =>
      imp_codeₘ(neg_codeₘ(quote_hilbert left), quote_hilbert right)
  | .imp left right =>
      imp_codeₘ(quote_hilbert left, quote_hilbert right)
  | .iff left right =>
      neg_codeₘ(imp_codeₘ(
        imp_codeₘ(quote_hilbert left, quote_hilbert right),
        neg_codeₘ(imp_codeₘ(quote_hilbert right, quote_hilbert left))))
  | .forallE _ body => all_codeₘ(quote_hilbert body)
  | .existsE _ body =>
      neg_codeₘ(all_codeₘ(neg_codeₘ(quote_hilbert body)))

/-- 已按 Hilbert 联结词编码的 quotation 对再次编译保持不变。 -/
@[simp] theorem quote_hilbert_hilbertize {σ : Signature} [QuotationNumbering σ]
    {bound free : SortContext σ} (formula : Formula σ bound free) :
    quote_hilbert (Formula.hilbertize QuotationNumbering.objectSort formula) =
      quote_hilbert formula := by
  induction formula <;>
    simp_all [Formula.hilbertize, Formula.hilbert_truth, Formula.hilbert_falsum,
      Formula.hilbert_conj, Formula.hilbert_iff, quote_hilbert, quote_term, Variable.index]

/-- 公共公式先 Hilbert 化，再直接生成结构码。 -/
def quote {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    {bound free : SortContext σ} (formula : Formula σ bound free) : Code :=
  quote_hilbert (Formula.hilbertize numbering.objectSort formula)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding
