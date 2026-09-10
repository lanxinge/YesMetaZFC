import YesMetaZFC.Automation.ObjectHornReflection
import YesMetaZFC.Automation.ObjectFormulaSyntax

/-! # 一般语法反射的行形状与实际归纳公式

三类行只以输入语法码为秩；上下文长度及参数个数不参与秩。
这些描述只用于证明原规则的下降性，不修改检查图。
-/
namespace YesMetaZFC.Automation.ObjectSyntaxReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectHorn ObjectTermSyntax ObjectFormulaSyntax ObjectNumeralReflection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe u v

inductive Row (α : Type u) where
  | term (bound free input : α)
  | arguments (bound free count input : α)
  | formula (bound free input : α)

def Row.tag {α : Type u} : Row α → Nat
  | .term .. => 0
  | .arguments .. => 1
  | .formula .. => 4
def Row.fields {α : Type u} : Row α → List α
  | .term b f input | .formula b f input => [b, f, input]
  | .arguments b f count input => [b, f, count, input]
def Row.input {α : Type u} : Row α → α
  | .term _ _ input | .arguments _ _ _ input | .formula _ _ input => input
def Row.map {α : Type u} {β : Type v} (f : α → β) : Row α → Row β
  | .term b c input => .term (f b) (f c) (f input)
  | .arguments b c count input => .arguments (f b) (f c) (f count) (f input)
  | .formula b c input => .formula (f b) (f c) (f input)

@[simp] theorem Row.map_tag {α : Type u} {β : Type v} (f : α → β) (row : Row α) :
    (row.map f).tag = row.tag := by cases row <;> rfl
@[simp] theorem Row.map_fields {α : Type u} {β : Type v} (f : α → β) (row : Row α) :
    (row.map f).fields = row.fields.map f := by cases row <;> rfl
@[simp] theorem Row.map_input {α : Type u} {β : Type v} (f : α → β) (row : Row α) :
    (row.map f).input = f row.input := by cases row <;> rfl
theorem Row.input_mem {α : Type u} (row : Row α) : row.input ∈ row.fields := by
  cases row <;> simp [input, fields]

def Row.expr {n : Nat} (row : Row (Expr n)) : Expr n := .node (.literal row.tag) row.fields

/-- 每个递归输入都出现在头输入最外层后继的内部，因此严格小于头输入。 -/
def Below {n : Nat} (child parent : Expr n) : Prop :=
  ∃ index body, child = .var index ∧ parent = .succ body ∧ index ∈ body.variables

def Ranked (rule : Rule) : Prop :=
  ∃ head : Row (Expr rule.arity), head.expr = rule.head ∧
    ∀ premise ∈ rule.premises, ∃ child : Row (Expr rule.arity),
      child.expr = premise ∧ Below child.input head.input

theorem ranked (rule : Rule) (hRule : rule ∈ ObjectFormulaSyntax.rules) : Ranked rule := by
  simp only [ObjectFormulaSyntax.rules, termRules, argumentRules, formulaRules,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with (((rfl | rfl) | hRule) | rfl | rfl) |
    ((rfl | rfl) | hRule) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp hRule
  · exact ⟨.term _ _ _, rfl, fun _ hp => False.elim (List.not_mem_nil hp)⟩
  · exact ⟨.term _ _ _, rfl, fun _ hp => False.elim (List.not_mem_nil hp)⟩
  · refine ⟨.term _ _ _, rfl, ?_⟩
    intro premise hp; obtain rfl := List.mem_singleton.mp hp
    exact ⟨.arguments _ _ _ _, rfl, _, _, rfl, rfl, by
        first | exact List.mem_cons_self
              | exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  · exact ⟨.arguments _ _ _ _, rfl, fun _ hp => False.elim (List.not_mem_nil hp)⟩
  · refine ⟨.arguments _ _ _ _, rfl, ?_⟩
    intro premise hp; rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨.term _ _ _, rfl, _, _, rfl, rfl, by
        first | exact List.mem_cons_self
              | exact List.mem_cons_of_mem _ List.mem_cons_self⟩
    · obtain rfl := List.mem_singleton.mp hp
      exact ⟨.arguments _ _ _ _, rfl, _, _, rfl, rfl, by
        first | exact List.mem_cons_self
              | exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  · exact ⟨.formula _ _ _, rfl, fun _ hp => False.elim (List.not_mem_nil hp)⟩
  · exact ⟨.formula _ _ _, rfl, fun _ hp => False.elim (List.not_mem_nil hp)⟩
  · refine ⟨.formula _ _ _, rfl, ?_⟩
    intro premise hp; obtain rfl := List.mem_singleton.mp hp
    exact ⟨.arguments _ _ _ _, rfl, _, _, rfl, rfl, by
        first | exact List.mem_cons_self
              | exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  · refine ⟨.formula _ _ _, rfl, ?_⟩
    intro premise hp; rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨.term _ _ _, rfl, _, _, rfl, rfl, by
        first | exact List.mem_cons_self
              | exact List.mem_cons_of_mem _ List.mem_cons_self⟩
    · obtain rfl := List.mem_singleton.mp hp
      exact ⟨.term _ _ _, rfl, _, _, rfl, rfl, by
        first | exact List.mem_cons_self
              | exact List.mem_cons_of_mem _ List.mem_cons_self⟩
  all_goals refine ⟨.formula _ _ _, rfl, ?_⟩
  all_goals intro premise hp
  all_goals rcases List.mem_cons.mp hp with rfl | hp
  all_goals first
    | exact False.elim (List.not_mem_nil hp)
    | obtain rfl := List.mem_singleton.mp hp
    | skip
  all_goals exact ⟨.formula _ _ _, rfl, _, _, rfl, rfl, by
        first | exact List.mem_cons_self
              | exact List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem head_variables (rule : Rule) (hRule : rule ∈ ObjectFormulaSyntax.rules) :
    ∀ i, i ∈ rule.head.variables := by
  rcases List.mem_append.mp hRule with hRule | hRule
  · exact ObjectTermSyntax.head_variables rule (List.mem_append_left _ hRule)
  simp only [formulaRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with ((rfl | rfl) | hRule) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try decide
  obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp hRule
  intro i
  change Fin 3 at i
  change i ∈ ([0, 1, 2] : List (Fin 3))
  have hi := i.isLt
  have hCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> decide

def atInput {bound free : SetContext} (graph : ProofT.Delta0ProofGraph)
    (input : SetTerm bound free) : SetFormula bound free :=
  let lifted := ((input.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set
  let b : SetTerm bound (.set :: .set :: .set :: free) := .fvar (.there (.there .here))
  let f : SetTerm bound (.set :: .set :: .set :: free) := .fvar (.there .here)
  let c : SetTerm bound (.set :: .set :: .set :: free) := .fvar .here
  forallNatural (forallNatural (forallNatural (ObjectHorn.allOf
    ([Row.term b f lifted, Row.arguments b f c lifted, Row.formula b f lifted].map fun row =>
      let root := ProofT.IntrinsicQuotation.node row.tag row.fields
      ObjectHorn.condition ObjectFormulaSyntax.rules root ⟶ₘ
        ObjectHornReflection.atRow graph ObjectFormulaSyntax.rules root))))

end YesMetaZFC.Automation.ObjectSyntaxReflection
