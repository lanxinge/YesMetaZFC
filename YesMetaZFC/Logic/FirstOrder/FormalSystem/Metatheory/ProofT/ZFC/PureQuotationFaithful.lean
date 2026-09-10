import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureQuotation

/-! # 纯公式完整 AST 编码的忠实性

逐构造子的编码具有单射性，并与当前源 AST 编码的结构嵌入相容。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureQuotation
open Nonlogical.BasicSetTheory PureOpenTransfer NatPacket
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature

private theorem variable_injective_m {S : Type} {context : List S} {s : S}
    (a b : Variable context s) (h : a.index = b.index) : a = b := by
  induction a with
  | here => cases b <;> simp_all [Variable.index]
  | there a ih =>
    cases b with
    | here => simp [Variable.index] at h
    | there b => exact congrArg Variable.there (ih b (Nat.add_right_cancel h))

theorem termTree_injective_m {bound free : SortContext ℒ} :
    {s : _root_.YesMetaZFC.SetTheory.SetSort} → (a b : Term ℒ bound free s) →
      termTree_m a = termTree_m b → a = b
  | _, .app f _, _, _ => nomatch f
  | _, _, .app f _, _ => nomatch f
  | _, .bvar a, .bvar b, h => congrArg Term.bvar
      (variable_injective_m a b (by simpa [termTree_m, leaf] using h))
  | _, .fvar a, .fvar b, h => congrArg Term.fvar
      (variable_injective_m a b (by simpa [termTree_m, leaf] using h))
  | _, .bvar _, .fvar _, h => by simp [termTree_m] at h
  | _, .fvar _, .bvar _, h => by simp [termTree_m] at h

theorem argumentsTree_injective_m {bound free sorts : SortContext ℒ}
    (a b : Arguments ℒ bound free sorts) (h : argumentsTree_m a = argumentsTree_m b) : a = b := by
  induction a using Arguments.listRec with
  | nil => cases b; rfl
  | cons a rest ih =>
    cases b with
    | cons b tail =>
      have h := List.cons.inj h
      rw [termTree_injective_m a b h.1, ih tail h.2]


theorem tree_injective_m {bound free : SortContext ℒ} (p other : Formula ℒ bound free)
    (h : tree_m p = tree_m other) : p = other := by
  induction p with
  | falsum => cases other <;> simp_all [tree_m, leaf]
  | truth => cases other <;> simp_all [tree_m, leaf]
  | rel r args =>
    cases r
    cases other <;> simp_all [tree_m, leaf]
    case rel r args' =>
      cases r
      exact ⟨rfl, argumentsTree_injective_m args args' h⟩
  | @equal bound free s a b =>
    cases s
    cases other <;> simp_all [tree_m, leaf]
    case equal s c d =>
      cases s
      exact ⟨rfl, termTree_injective_m a c h.1, termTree_injective_m b d h.2⟩
  | neg p ih =>
    cases other <;> simp_all [tree_m, leaf]
    exact ih _ rfl
  | conj p q ip iq =>
    cases other <;> simp_all [tree_m, leaf]
    exact ⟨ip _ rfl, iq _ rfl⟩
  | disj p q ip iq =>
    cases other <;> simp_all [tree_m, leaf]
    exact ⟨ip _ rfl, iq _ rfl⟩
  | imp p q ip iq =>
    cases other <;> simp_all [tree_m, leaf]
    exact ⟨ip _ rfl, iq _ rfl⟩
  | iff p q ip iq =>
    cases other <;> simp_all [tree_m, leaf]
    exact ⟨ip _ rfl, iq _ rfl⟩
  | forallE s p ih =>
    cases s
    cases other <;> simp_all [tree_m, leaf]
    case forallE s q => cases s; exact ⟨rfl, ih q rfl⟩
  | existsE s p ih =>
    cases s
    cases other <;> simp_all [tree_m, leaf]
    case existsE s q => cases s; exact ⟨rfl, ih q rfl⟩

theorem code_injective_m {bound free : SetContext}
    (p q : Formula ℒ (pureContext_m bound) (pureContext_m free)) (h : code_m p = code_m q) : p = q :=
  tree_injective_m p q (IntrinsicQuotation.treeValue_injective h)

/-- 纯项编码保持原完整 AST 的变量标签和槽位。 -/
theorem term_source_m {bound free : SetContext} :
    {s : _root_.YesMetaZFC.SetTheory.SetSort} →
    (t : Term ℒ (pureContext_m bound) (pureContext_m free) s) →
      SyntaxEncode.term (term_m t) = termTree_m t
  | _, .bvar v => by
    simp only [term_m, SyntaxEncode.term_bvar, termTree_m]
    rw [variable_index_m]
  | _, .fvar v => by
    simp only [term_m, SyntaxEncode.term_fvar, termTree_m]
    rw [variable_index_m]
  | _, .app f _ => nomatch f

/-- 结构嵌入没有翻译见证；纯公式编码逐节点等于原完整 AST 编码的相应子语言。 -/
theorem tree_source_m {bound free : SetContext} :
    (φ : Formula ℒ (pureContext_m bound) (pureContext_m free)) →
      SyntaxEncode.formula (formula_m φ) = tree_m φ
  | .falsum => by simp only [formula_m, tree_m, SyntaxEncode.formula]
  | .truth => by simp only [formula_m, tree_m, SyntaxEncode.formula]
  | .rel .membership (.cons a (.cons b .nil)) => by
    simp only [formula_m, tree_m, SyntaxEncode.formula, SyntaxEncode.argumentsList,
      argumentsTree_m, term_source_m]
    rfl
  | .equal a b => by simp only [formula_m, tree_m, SyntaxEncode.formula, term_source_m]
  | .neg p => by simp only [formula_m, tree_m, SyntaxEncode.formula, tree_source_m p]
  | .conj p q | .disj p q | .imp p q | .iff p q => by
    simp only [formula_m, tree_m, SyntaxEncode.formula, tree_source_m p, tree_source_m q]
  | .forallE .set p | .existsE .set p => by
    simp only [formula_m, tree_m, SyntaxEncode.formula, tree_source_m (bound := SetSort.set :: bound) (free := free) p]

/-- 按类型化上下文解码后，得到原纯 AST 的逐节点结构嵌入。 -/
theorem decode_tree_m {bound free : SetContext}
    (φ : Formula ℒ (pureContext_m bound) (pureContext_m free)) :
    SyntaxDecode.formula bound free (tree_m φ) = some (formula_m φ) := by
  rw [← tree_source_m]
  exact SyntaxEncode.formula_roundtrip (formula_m φ)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureQuotation
