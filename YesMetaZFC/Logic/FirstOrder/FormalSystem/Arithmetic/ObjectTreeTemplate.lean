import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues

/-!
# 带正文槽位的固定树模板

模板只负责按固定结构填槽，不识别槽内语法，也不执行重命名。编译结果只使用已有
数码项与相等；同一个带标签公式同时表示所有分支，任意错误输出均可在有限算术核中否定。
-/
namespace YesMetaZFC.Automation.ObjectTreeTemplate
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

inductive Template (arity : Nat) where
  | hole (index : Fin arity)
  | leaf (tag : Nat)
  | unary (tag : Nat) (body : Template arity)
  | binary (tag : Nat) (left right : Template arity)
  deriving Repr

namespace Template
def plug {n : Nat} (inputs : Fin n → Tree) : Template n → Tree
  | .hole i => inputs i
  | .leaf tag => .node tag []
  | .unary tag body => .node tag [body.plug inputs]
  | .binary tag left right => .node tag [left.plug inputs, right.plug inputs]

def expr {n : Nat} : Template n → Expr n
  | .hole i => .var i
  | .leaf tag => .node (.literal tag) []
  | .unary tag body => .node (.literal tag) [body.expr]
  | .binary tag left right => .node (.literal tag) [left.expr, right.expr]

/-- 固定模板的结构求值与实际填槽逐节点交换。 -/
theorem value_plug {n : Nat} (shape : Template n) (inputs : Fin n → Tree) :
    IntrinsicQuotation.treeValue (shape.plug inputs) =
      shape.expr.eval (fun i => IntrinsicQuotation.treeValue (inputs i)) := by
  induction shape <;> simp_all [plug, expr, Expr.eval]

theorem term_plug {n : Nat} (shape : Template n) (inputs : Fin n → Tree) :
    shape.expr.term (fun i => IntrinsicQuotation.tree (inputs i)) =
      IntrinsicQuotation.tree (shape.plug inputs) := by
  induction shape <;> simp_all [plug, expr, Expr.term,
    IntrinsicQuotation.tree, IntrinsicQuotation.forest]

def condition {n : Nat} (shape : Template n) {bound free : SetContext}
    (inputs : Fin n → SetTerm bound free) (output : SetTerm bound free) : SetFormula bound free :=
  shape.expr.term inputs ≐ₘ output

theorem positive {T : SetTheory} (C : CertificateCore T) {n : Nat}
    (shape : Template n) (inputs : Fin n → Nat) (output : Nat)
    (h : shape.expr.eval inputs = output) :
    Derives T [] (shape.condition (fun i => numₘ(inputs i)) (numₘ(output) : Code)) := by
  rw [← h]
  exact shape.expr.evaluate C inputs

theorem negative {T : SetTheory} (C : CertificateCore T) {n : Nat}
    (shape : Template n) (inputs : Fin n → Nat) (output : Nat)
    (h : shape.expr.eval inputs ≠ output) :
    Derives T [] (¬ₘ shape.condition (fun i => numₘ(inputs i)) (numₘ(output) : Code)) := by
  apply FirstOrder.Derives.neg_intro
  have hEq := FirstOrder.Derives.assumption (T := T)
    (Γ := [shape.condition (fun i => numₘ(inputs i)) (numₘ(output) : Code)]) List.mem_cons_self
  have hNumeric := Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm
      (FirstOrder.Derives.context_weaken_cons (shape.expr.evaluate C inputs))) hEq
  exact FirstOrder.Derives.neg_elim hNumeric
    (FirstOrder.Derives.context_weaken_cons (C.numeral_ne h))

theorem positive_at_tree {T : SetTheory} {n : Nat}
    (shape : Template n) (inputs : Fin n → Tree) (output : Tree)
    (h : shape.plug inputs = output) :
    Derives T [] (shape.condition (fun i => IntrinsicQuotation.tree (inputs i))
      (IntrinsicQuotation.tree output)) := by
  unfold condition
  rw [term_plug, h]
  exact Metatheory.Derives.equality_refl _

theorem negative_at_tree {T : SetTheory} (C : CertificateCore T) {n : Nat}
    (shape : Template n) (inputs : Fin n → Tree) (output : Tree)
    (h : shape.plug inputs ≠ output) :
    Derives T [] (¬ₘ shape.condition (fun i => IntrinsicQuotation.tree (inputs i))
      (IntrinsicQuotation.tree output)) := by
  unfold condition
  rw [term_plug]
  apply FirstOrder.Derives.neg_intro
  have hEq := FirstOrder.Derives.assumption (T := T)
    (Γ := [IntrinsicQuotation.tree (shape.plug inputs) ≐ₘ IntrinsicQuotation.tree output])
    List.mem_cons_self
  have hNumeric := Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm (FirstOrder.Derives.context_weaken_cons
      (IntrinsicQuotation.tree_evaluate C (shape.plug inputs))))
    (Metatheory.Derives.equality_trans hEq (FirstOrder.Derives.context_weaken_cons
      (IntrinsicQuotation.tree_evaluate C output)))
  exact FirstOrder.Derives.neg_elim hNumeric (FirstOrder.Derives.context_weaken_cons
    (C.numeral_ne (fun hEq => h (IntrinsicQuotation.treeValue_injective hEq))))
end Template

/-- 标签也是对象输入；有限分支表与正文大小、参数数目和候选输出无关。 -/
def graph {n : Nat} (program : List (Nat × Template n)) {bound free : SetContext}
    (tag : SetTerm bound free) (inputs : Fin n → SetTerm bound free)
    (output : SetTerm bound free) : SetFormula bound free :=
  anyOf (program.map (fun entry => (tag ≐ₘ numₘ(entry.1)) ∧ₘ entry.2.condition inputs output))

theorem graph_delta0 {n : Nat} (program : List (Nat × Template n)) {bound free : SetContext}
    (tag : SetTerm bound free) (inputs : Fin n → SetTerm bound free) (output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (graph program tag inputs output) := by
  apply anyOf_delta0
  intro φ hφ
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hφ
  exact .conj (.equal _ _) (.equal _ _)

@[simp] theorem graph_substituteMapped {n : Nat} (program : List (Nat × Template n))
    {sb sf tb tf : SetContext} (tag : SetTerm sb sf) (inputs : Fin n → SetTerm sb sf)
    (output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (graph program tag inputs output).substituteMapped bs fs =
      graph program (tag.substituteMapped bs fs)
        (fun i => (inputs i).substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [graph, Template.condition, Formula.substituteMapped, Function.comp_def]

theorem graph_positive {T : SetTheory} {n : Nat} (program : List (Nat × Template n))
    (tag : Nat) (inputs : Fin n → Code) (output : Code) (shape : Template n)
    (hEntry : (tag, shape) ∈ program) (h : Derives T [] (shape.condition inputs output)) :
    Derives T [] (graph program (numₘ(tag)) inputs output) := by
  apply anyOf_intro (List.mem_map.mpr ⟨(tag, shape), hEntry, rfl⟩)
  exact FirstOrder.Derives.conj_intro (Metatheory.Derives.equality_refl _) h

/-- 负向覆盖所有匹配分支；未知标签不需要关于正文的任何假设。 -/
theorem graph_negative {T : SetTheory} (C : CertificateCore T) {n : Nat}
    (program : List (Nat × Template n)) (tag : Nat) (inputs : Fin n → Code) (output : Code)
    (h : ∀ entry, entry ∈ program → tag = entry.1 →
      Derives T [] (¬ₘ entry.2.condition inputs output)) :
    Derives T [] (¬ₘ graph program (numₘ(tag)) inputs output) := by
  apply anyOf_negative
  intro φ hφ
  obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hφ
  apply FirstOrder.Derives.neg_intro
  have hBoth := FirstOrder.Derives.assumption (T := T)
    (Γ := [(numₘ(tag) ≐ₘ numₘ(entry.1)) ∧ₘ entry.2.condition inputs output]) List.mem_cons_self
  by_cases hTag : tag = entry.1
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_right hBoth)
      (FirstOrder.Derives.context_weaken_cons (h entry hEntry hTag))
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.conj_elim_left hBoth)
      (FirstOrder.Derives.context_weaken_cons (C.numeral_ne hTag))

end YesMetaZFC.Automation.ObjectTreeTemplate
