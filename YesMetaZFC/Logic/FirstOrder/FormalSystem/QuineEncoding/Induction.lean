import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding

/-! # quotation 的构造封闭性归纳

对实际 quotation 只做一次宿主语法归纳。具体识别谓词提供原子、否定、蕴含和
全称构造的封闭性；需要同步保持码域等不变量时，将它们放入同一个谓词。
这不假定对象模型内部自然数的外部良基性。
-/
namespace YesMetaZFC.Automation.QuotationInduction

open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.FormalSystem.QuineEncoding
open Logic.FirstOrder.Nonlogical.BasicSetTheory
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
open scoped Logic.FirstOrder.FormalSystem.Symbols

universe u v w

/-- quotation 的五种基础构造合同；合取、析取、存在等沿实际 Hilbert 编码得到。 -/
structure FormulaClosure (σ : Signature.{u, v, w}) [QuotationNumbering σ]
    (P : Nat → Code → Prop) : Prop where
  relation : ∀ {bound free : SortContext σ} (r : σ.RelSymbol)
    (args : Arguments σ bound free (σ.relDomain r)) (depth : Nat),
    bound.length ≤ depth → P depth (quote_relation r args)
  equality : ∀ {bound free : SortContext σ} {sort : σ.SortSymbol}
    (left right : Term σ bound free sort) (depth : Nat),
    bound.length ≤ depth → P depth (eq_codeₘ(quote_term left, quote_term right))
  negation : ∀ depth body, P depth body → P depth (neg_codeₘ(body))
  implication : ∀ depth left right, P depth left → P depth right →
    P depth (imp_codeₘ(left, right))
  universal : ∀ depth body, P (depth + 1) body → P depth (all_codeₘ(body))

/-- 真公式的码使用一个新 bound 变量，其合法深度由后继给出。 -/
theorem FormulaClosure.truth
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] {P : Nat → Code → Prop}
    (C : FormulaClosure σ P) (depth : Nat) :
    P depth (quote_hilbert (.truth : Formula σ [] [])) := by
  exact C.universal depth _
    (C.equality (free := [])
      (.bvar (.here : Variable [QuotationNumbering.objectSort] QuotationNumbering.objectSort))
      (.bvar .here) (depth + 1) (Nat.succ_le_succ (Nat.zero_le depth)))

/-- 识别与伴随不变量共用这一归纳，无须为每个目标复制整棵公式递归。 -/
theorem FormulaClosure.quote_hilbert
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] {P : Nat → Code → Prop}
    (C : FormulaClosure σ P) {bound free : SortContext σ}
    (formula : Formula σ bound free) (depth : Nat) (hBound : bound.length ≤ depth) :
    P depth (QuineEncoding.quote_hilbert formula) := by
  induction formula generalizing depth with
  | falsum => exact C.negation depth _ (C.truth depth)
  | truth => exact C.truth depth
  | rel r args => exact C.relation r args depth hBound
  | equal left right => exact C.equality left right depth hBound
  | neg body ih => exact C.negation depth _ (ih depth hBound)
  | conj left right ihLeft ihRight =>
    exact C.negation depth _
      (C.implication depth _ _ (ihLeft depth hBound) (C.negation depth _ (ihRight depth hBound)))
  | disj left right ihLeft ihRight =>
    exact C.implication depth _ _ (C.negation depth _ (ihLeft depth hBound)) (ihRight depth hBound)
  | imp left right ihLeft ihRight =>
    exact C.implication depth _ _ (ihLeft depth hBound) (ihRight depth hBound)
  | iff left right ihLeft ihRight =>
    exact C.negation depth _ (C.implication depth _ _
      (C.implication depth _ _ (ihLeft depth hBound) (ihRight depth hBound))
      (C.negation depth _ (C.implication depth _ _ (ihRight depth hBound) (ihLeft depth hBound))))
  | forallE sort body ih =>
    exact C.universal depth _ (ih (depth + 1) (Nat.succ_le_succ hBound))
  | existsE sort body ih =>
    exact C.negation depth _ (C.universal depth _
      (C.negation (depth + 1) _ (ih (depth + 1) (Nat.succ_le_succ hBound))))

end YesMetaZFC.Automation.QuotationInduction
