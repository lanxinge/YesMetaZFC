import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxEncode

/-! # 固定 AST 的参数化码构造

只遍历外部固定的公式骨架，自由变量槽位直接使用给定的码值。
节点代数保持抽象，供内部模型求值和当前结构 quotation 共用。
-/
namespace YesMetaZFC.Automation.ObjectCodeInstantiation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket
set_option autoImplicit false
universe u v
variable {α : Type u}

def prepend (first : α) (rest : Nat → α) : Nat → α
  | 0 => first
  | index + 1 => rest index

theorem prepend_eta (values : Nat → α) : prepend (values 0) (fun i => values (i + 1)) = values := by
  funext i; cases i <;> rfl

mutual
def tree (node : Nat → List α → α) : Tree → α
  | .node tag fields => node tag (forest node fields)
def forest (node : Nat → List α → α) : List Tree → List α
  | [] => []
  | head :: tail => tree node head :: forest node tail
end

mutual
def term (node : Nat → List α → α) (values : Nat → α)
    {bound free : SetContext} {sort : SetSort} : Term signature bound free sort → α
  | .bvar entry => node 0 [node entry.index []]
  | .fvar entry => values entry.index
  | .app symbol args => node 2 (node symbol.ctorIdx [] :: arguments node values args)
def arguments (node : Nat → List α → α) (values : Nat → α)
    {bound free sorts : SetContext} : Arguments signature bound free sorts → List α
  | .nil => []
  | .cons head tail => term node values head :: arguments node values tail
end

/-- 两个字段列表逐项满足给定关系。 -/
inductive FieldsRel {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | nil : FieldsRel R [] []
  | cons {left right lefts rights} : R left right → FieldsRel R lefts rights →
      FieldsRel R (left :: lefts) (right :: rights)

/-- 变量的 AST 形状决定任意自由槽位赋值下的码值。 -/
theorem variable_of_encode (node : Nat → List α → α) (values : Nat → α)
    {bound free : SetContext} {sort : SetSort} (isFree : Bool) (index : Nat) :
    (input : Term signature bound free sort) →
    SyntaxEncode.term input = .node (if isFree then 1 else 0) [leaf index] →
    term node values input = if isFree then values index else node 0 [node index []]
  | .bvar entry, h => by
    cases isFree with
    | false =>
      have hi : entry.index = index := by simpa [SyntaxEncode.term_bvar, leaf] using h
      change node 0 [node entry.index []] = node 0 [node index []]
      rw [hi]
    | true => simp [SyntaxEncode.term_bvar] at h
  | .fvar entry, h => by
    cases isFree with
    | false => simp [SyntaxEncode.term_fvar] at h
    | true =>
      have hi : entry.index = index := by simpa [SyntaxEncode.term_fvar, leaf] using h
      change values entry.index = values index
      rw [hi]
  | .app symbol args, h => by
    cases isFree <;> simp [SyntaxEncode.term_app] at h

mutual
/-- 节点代数间的关系逐层传递到项和参数列。 -/
theorem term_rel {β : Type v} (leftNode : Nat → List α → α) (rightNode : Nat → List β → β)
    (leftValues : Nat → α) (rightValues : Nat → β) (R : α → β → Prop)
    (hNode : ∀ tag left right, FieldsRel R left right → R (leftNode tag left) (rightNode tag right))
    {bound free : SetContext} (hValues : ∀ i, i < free.length → R (leftValues i) (rightValues i)) {sort : SetSort} :
    (input : Term signature bound free sort) → R (term leftNode leftValues input) (term rightNode rightValues input)
  | .bvar entry => hNode 0 _ _ (.cons (hNode entry.index [] [] .nil) .nil)
  | .fvar entry => hValues entry.index entry.index_lt_length
  | .app symbol args => hNode 2 _ _ (.cons (hNode symbol.ctorIdx [] [] .nil)
      (arguments_rel leftNode rightNode leftValues rightValues R hNode hValues args))

theorem arguments_rel {β : Type v} (leftNode : Nat → List α → α) (rightNode : Nat → List β → β)
    (leftValues : Nat → α) (rightValues : Nat → β) (R : α → β → Prop)
    (hNode : ∀ tag left right, FieldsRel R left right → R (leftNode tag left) (rightNode tag right))
    {bound free sorts : SetContext} (hValues : ∀ i, i < free.length → R (leftValues i) (rightValues i)) :
    (input : Arguments signature bound free sorts) →
      FieldsRel R (arguments leftNode leftValues input) (arguments rightNode rightValues input)
  | .nil => .nil
  | .cons head tail => .cons (term_rel leftNode rightNode leftValues rightValues R hNode hValues head)
      (arguments_rel leftNode rightNode leftValues rightValues R hNode hValues tail)
end

def formula (node : Nat → List α → α) (values : Nat → α)
    {bound free : SetContext} : SetFormula bound free → α
  | .falsum => node 0 []
  | .truth => node 1 []
  | .rel symbol args => node 2 (node symbol.ctorIdx [] :: arguments node values args)
  | .equal left right => node 3 [term node values left, term node values right]
  | .neg body => node 4 [formula node values body]
  | .conj left right => node 5 [formula node values left, formula node values right]
  | .disj left right => node 6 [formula node values left, formula node values right]
  | .imp left right => node 7 [formula node values left, formula node values right]
  | .iff left right => node 8 [formula node values left, formula node values right]
  | .forallE _ body => node 9 [formula node values body]
  | .existsE _ body => node 10 [formula node values body]

/-- 完整公式也保持节点代数关系；可用于求值和受自然数界约束的模型传输。 -/
theorem formula_rel {β : Type v} (leftNode : Nat → List α → α) (rightNode : Nat → List β → β)
    (leftValues : Nat → α) (rightValues : Nat → β) (R : α → β → Prop)
    (hNode : ∀ tag left right, FieldsRel R left right → R (leftNode tag left) (rightNode tag right))
    {bound free : SetContext} (hValues : ∀ i, i < free.length → R (leftValues i) (rightValues i)) (input : SetFormula bound free) :
    R (formula leftNode leftValues input) (formula rightNode rightValues input) := by
  induction input with
  | falsum =>
    exact hNode 0 [] [] .nil
  | truth =>
    exact hNode 1 [] [] .nil
  | rel symbol args =>
    exact hNode 2 _ _ (.cons (hNode symbol.ctorIdx [] [] .nil)
      (arguments_rel leftNode rightNode leftValues rightValues R hNode hValues args))
  | equal left right =>
    exact hNode 3 _ _
      (.cons (term_rel leftNode rightNode leftValues rightValues R hNode hValues left)
        (.cons (term_rel leftNode rightNode leftValues rightValues R hNode hValues right) .nil))
  | neg body ih =>
    exact hNode 4 _ _ (.cons (ih hValues) .nil)
  | conj left right ihLeft ihRight =>
    exact hNode 5 _ _ (.cons (ihLeft hValues) (.cons (ihRight hValues) .nil))
  | disj left right ihLeft ihRight =>
    exact hNode 6 _ _ (.cons (ihLeft hValues) (.cons (ihRight hValues) .nil))
  | imp left right ihLeft ihRight =>
    exact hNode 7 _ _ (.cons (ihLeft hValues) (.cons (ihRight hValues) .nil))
  | iff left right ihLeft ihRight =>
    exact hNode 8 _ _ (.cons (ihLeft hValues) (.cons (ihRight hValues) .nil))
  | forallE sort body ih =>
    exact hNode 9 _ _ (.cons (ih hValues) .nil)
  | existsE sort body ih =>
    exact hNode 10 _ _ (.cons (ih hValues) .nil)

theorem FieldsRel.left_property {β : Type v} {P : α → Prop} {left : List α} {right : List β}
    (h : FieldsRel (fun value _ => P value) left right) : ∀ value ∈ left, P value := by
  induction h with
  | nil => intro value hv; cases hv
  | cons h _ ih =>
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h
    · exact ih value hv

theorem FieldsRel.eq {left right : List α} (h : FieldsRel Eq left right) : left = right := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [h, ih]

/-- 未使用的自由变量槽位不影响固定公式的码值。 -/
theorem formula_values_congr (node : Nat → List α → α) (values other : Nat → α)
    {bound free : SetContext} (input : SetFormula bound free)
    (h : ∀ i, i < free.length → values i = other i) :
    formula node values input = formula node other input :=
  formula_rel node node values other Eq (fun tag _ _ h => congrArg (node tag) h.eq) h input

/-- 单模型性质是关系保持的特例，复用同一 AST 遍历。 -/
theorem term_property (node : Nat → List α → α) (values : Nat → α) (P : α → Prop)
    (hNode : ∀ tag fields, (∀ value ∈ fields, P value) → P (node tag fields))
    (hValues : ∀ index, P (values index)) {bound free : SetContext} {sort : SetSort}
    (input : Term signature bound free sort) : P (term node values input) :=
  term_rel node node values values (fun value _ => P value)
    (fun tag _ _ h => hNode tag _ h.left_property) (fun i _ => hValues i) input

theorem arguments_property (node : Nat → List α → α) (values : Nat → α) (P : α → Prop)
    (hNode : ∀ tag fields, (∀ value ∈ fields, P value) → P (node tag fields))
    (hValues : ∀ index, P (values index)) {bound free sorts : SetContext}
    (input : Arguments signature bound free sorts) : ∀ value ∈ arguments node values input, P value :=
  (arguments_rel node node values values (fun value _ => P value)
    (fun tag _ _ h => hNode tag _ h.left_property) (fun i _ => hValues i) input).left_property

theorem formula_property (node : Nat → List α → α) (values : Nat → α) (P : α → Prop)
    (hNode : ∀ tag fields, (∀ value ∈ fields, P value) → P (node tag fields))
    (hValues : ∀ index, P (values index)) {bound free : SetContext} (input : SetFormula bound free) :
    P (formula node values input) :=
  formula_rel node node values values (fun value _ => P value)
    (fun tag _ _ h => hNode tag _ h.left_property) (fun i _ => hValues i) input

mutual
theorem term_original (node : Nat → List α → α) {bound free : SetContext} {sort : SetSort}
    : (input : Term signature bound free sort) →
    term node (fun index => node 1 [node index []]) input = tree node (SyntaxEncode.term input)
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app symbol args => congrArg (fun fields => node 2 (node symbol.ctorIdx [] :: fields)) (arguments_original node args)
theorem arguments_original (node : Nat → List α → α) {bound free sorts : SetContext}
    (input : Arguments signature bound free sorts) :
    arguments node (fun index => node 1 [node index []]) input = forest node (SyntaxEncode.argumentsList input) := by
  cases input with
  | nil => rfl
  | cons head tail => simp only [arguments, SyntaxEncode.argumentsList, forest, term_original node head, arguments_original node tail]
end

theorem formula_original (node : Nat → List α → α) {bound free : SetContext} (input : SetFormula bound free) :
    formula node (fun index => node 1 [node index []]) input = tree node (SyntaxEncode.formula input) := by
  induction input with
  | falsum => rfl
  | truth => rfl
  | rel symbol args => exact congrArg (fun fields => node 2 (node symbol.ctorIdx [] :: fields)) (arguments_original node args)
  | equal left right => simp only [formula, SyntaxEncode.formula, tree, forest, term_original]
  | neg body ih => exact congrArg (fun code => node 4 [code]) ih
  | conj left right ihLeft ihRight => simp only [formula, SyntaxEncode.formula, tree, forest, ihLeft, ihRight]
  | disj left right ihLeft ihRight => simp only [formula, SyntaxEncode.formula, tree, forest, ihLeft, ihRight]
  | imp left right ihLeft ihRight => simp only [formula, SyntaxEncode.formula, tree, forest, ihLeft, ihRight]
  | iff left right ihLeft ihRight => simp only [formula, SyntaxEncode.formula, tree, forest, ihLeft, ihRight]
  | forallE _ body ih => exact congrArg (fun code => node 9 [code]) ih
  | existsE _ body ih => exact congrArg (fun code => node 10 [code]) ih

end YesMetaZFC.Automation.ObjectCodeInstantiation
