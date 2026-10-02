import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCheckedTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteJoin
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreeCode

/-! # 六类证明节点与结论连接的统一递归对象外壳

行 0 检查带标注的节点，行 1 检查根节点并连接所声明的结论。
所有节点共享一个有限规则表，递归检查沿实际子证明下降。
本模块完成外壳的计算和正负推导；LocalTest 必须另由局部公理及语法变换
的对象表示构造，因此此模块本身不宣称已经给出 ZFC 的 Delta1ProofPresentation。
-/
namespace YesMetaZFC.Automation.ObjectProofTree
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding IntrinsicQuotation
open ObjectHorn ObjectCodeProjection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

structure Shape where
  tag : Nat
  extra : Nat
  children : List (Fin (extra + 2))

abbrev logicalShape : Shape := ⟨0, 1, []⟩
abbrev theoryShape : Shape := ⟨1, 1, []⟩
abbrev mpShape : Shape := ⟨2, 2, [2, 3]⟩
abbrev forallShape : Shape := ⟨3, 1, [2]⟩
abbrev strengtheningShape : Shape := ⟨4, 1, [2]⟩
abbrev substitutionShape : Shape := ⟨5, 3, [4]⟩
def shapes : List Shape :=
  [logicalShape, theoryShape, mpShape, forallShape, strengtheningShape, substitutionShape]

def payload (shape : Shape) : Expr (shape.extra + 2) :=
  .node (.literal shape.tag) (List.ofFn Expr.var)

def payloadValue (shape : Shape) (values : Fin (shape.extra + 2) → Nat) : Nat :=
  nodeValue shape.tag (List.ofFn values)

@[simp] theorem payload_eval (shape : Shape) (values : Fin (shape.extra + 2) → Nat) :
    (payload shape).eval values = payloadValue shape values := by
  simp [payload, payloadValue, List.map_ofFn, Function.comp_def, Expr.eval]

abbrev branch (shape : Shape) (root : Bool) : Rule where
  arity := shape.extra + 2
  head := if root then .node (.literal 1) [payload shape, .var 1]
    else .node (.literal 0) [payload shape]
  guards := if root then [(.var 0, .literal 1)] else []
  premises := if root then [.node (.literal 0) [payload shape]]
    else shape.children.map (fun index => .node (.literal 0) [.var index])

def rules : List Rule := shapes.flatMap (fun shape => [branch shape false, branch shape true])

@[simp] theorem branch_head (shape : Shape) (root : Bool) (values : Fin (shape.extra + 2) → Nat) :
    (branch shape root).head.eval values =
      if root then nodeValue 1 [payloadValue shape values, values 1] else nodeValue 0 [payloadValue shape values] := by
  cases root <;> simp [Expr.eval]

def rank (row : Nat) : Nat := 2 * field row 0 + if tag row = 1 then 1 else 0

@[simp] theorem rank_node (input : Nat) : rank (nodeValue 0 [input]) = 2 * input := by simp [rank]
@[simp] theorem rank_root (input output : Nat) : rank (nodeValue 1 [input, output]) = 2 * input + 1 := by simp [rank]

theorem payload_bound (shape : Shape) (values : Fin (shape.extra + 2) → Nat) (i : Fin (shape.extra + 2)) :
    values i < payloadValue shape values :=
  node_field_lt shape.tag (List.ofFn values) (values i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem branch_bound (shape : Shape) (root : Bool) (values : Fin (shape.extra + 2) → Nat)
    (i : Fin (shape.extra + 2)) : values i ≤ (branch shape root).head.eval values := by
  have h : values i ≤ payloadValue shape values := Nat.le_of_lt (payload_bound shape values i)
  cases root <;> simp only [Bool.false_eq_true, if_false, if_true, Expr.node_eval,
    List.map_cons, List.map_nil, Expr.eval, payload_eval]
  · exact Nat.le_trans h (ObjectCodeBounds.node_field_le 0 _ _ List.mem_cons_self)
  · exact Nat.le_trans h (ObjectCodeBounds.node_field_le 1 _ _ List.mem_cons_self)

theorem branch_mem (shape : Shape) (h : shape ∈ shapes) (root : Bool) : branch shape root ∈ rules := by
  apply List.mem_flatMap.mpr
  refine ⟨shape, h, ?_⟩
  cases root <;> simp

theorem descending : Descending rules rank := by
  intro rule hRule values _ _ premise hPremise
  obtain ⟨shape, _, hRule⟩ := List.mem_flatMap.mp hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · change Fin (shape.extra + 2) → Nat at values
    change premise ∈ shape.children.map (fun i => Expr.node (.literal 0) [.var i]) at hPremise
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp hPremise
    simp only [Bool.false_eq_true, if_false, Expr.node_eval, List.map_cons,
      List.map_nil, Expr.eval, payload_eval, rank_node]
    have h := payload_bound shape values index
    omega
  · have hRule := List.mem_singleton.mp hRule
    subst rule
    change Fin (shape.extra + 2) → Nat at values
    have hPremise := List.mem_singleton.mp hPremise
    subst premise
    simp [Expr.eval]

/-- 局部检查只在节点行调用；根行负责结论连接。 -/
def rowCheck (localCheck : Nat → Bool) (row : Nat) : Bool :=
  if tag row = 0 then localCheck (field row 0) else true

def nodeChecked (localCheck : Nat → Bool) (code : Nat) : Bool :=
  ObjectCheckedTrace.check (rowCheck localCheck) rules rank (nodeValue 0 [code])

def checked (localCheck : Nat → Bool) (code conclusion : Nat) : Bool :=
  ObjectCheckedTrace.check (rowCheck localCheck) rules rank (nodeValue 1 [code, conclusion])

/-- 该公式把局部对象测试与整棵树的递归轨迹连接；测试不能只留作未证明的合同。 -/
def condition (localCondition : FormulaTemplate.Unary)
    {bound free : SetContext} (code conclusion : SetTerm bound free) : SetFormula bound free :=
  ObjectCheckedTrace.condition rules localCondition (IntrinsicQuotation.node 1 [code, conclusion])

@[simp] theorem condition_substituteMapped (localCondition : FormulaTemplate.Unary)
    {sb sf tb tf : SetContext} (code conclusion : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition localCondition code conclusion).substituteMapped bs fs =
      condition localCondition (code.substituteMapped bs fs) (conclusion.substituteMapped bs fs) := by
  simp [condition, ObjectCheckedTrace.condition, Term.substituteMapped, Arguments.substituteMapped]

def template (localCondition : FormulaTemplate.Unary) : FormulaTemplate.Binary where
  body := condition localCondition (.fvar .here) (.fvar (.there .here))

@[simp] theorem template_apply (localCondition : FormulaTemplate.Unary)
    {bound free : SetContext} (code conclusion : SetTerm bound free) :
    template localCondition code conclusion = condition localCondition code conclusion := by
  simp [template, FormulaTemplate.apply_two, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

def graph (localCondition : FormulaTemplate.Unary)
    (hLocal : Formula.IsDelta0 set_levy_bound localCondition.body) : Delta0ProofGraph where
  condition := template localCondition
  delta0 code conclusion := by
    rw [template_apply]
    exact ObjectCheckedTrace.delta0 rules localCondition hLocal _

/-- 一个节点成功恰好要求局部检查和全部指定子证明成功。 -/
theorem node_intro (localCheck : Nat → Bool) (shape : Shape) (hShape : shape ∈ shapes)
    (values : Fin (shape.extra + 2) → Nat)
    (hLocal : localCheck (payloadValue shape values) = true)
    (hChildren : ∀ i, i ∈ shape.children → nodeChecked localCheck (values i) = true) :
    nodeChecked localCheck (payloadValue shape values) = true := by
  apply (ObjectCheckedTrace.check_eq_true_iff (rowCheck localCheck) rules rank descending _).mpr
  refine ⟨by simpa [rowCheck] using hLocal, branch shape false, branch_mem shape hShape false,
    values, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [Expr.eval] using branch_bound shape false values i
  · simp [Expr.eval]
  · intro guard h; cases h
  · intro premise h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    simpa only [nodeChecked, Expr.node_eval, List.map_cons, List.map_nil, Expr.eval] using hChildren i hi

theorem root_intro (localCheck : Nat → Bool) (shape : Shape) (hShape : shape ∈ shapes)
    (values : Fin (shape.extra + 2) → Nat)
    (hClosed : values 0 = 0)
    (hNode : nodeChecked localCheck (payloadValue shape values) = true) :
    checked localCheck (payloadValue shape values) (values 1) = true := by
  apply (ObjectCheckedTrace.check_eq_true_iff (rowCheck localCheck) rules rank descending _).mpr
  refine ⟨by simp [rowCheck] , branch shape true, branch_mem shape hShape true, values, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [Expr.eval] using branch_bound shape true values i
  · simp [Expr.eval]
  · intro guard h
    have h := List.mem_singleton.mp h
    subst guard
    change values 0 < 1
    omega
  · intro premise h
    have h := List.mem_singleton.mp h
    subst premise
    simpa only [nodeChecked, Expr.node_eval, List.map_cons, List.map_nil, Expr.eval, payload_eval] using hNode

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (localTest : ObjectCheckedTrace.LocalTest T) (localCheck : Nat → Bool)
    (hTest : localTest.checked = rowCheck localCheck)
    (code conclusion : Nat) (h : checked localCheck code conclusion = true) :
    Derives T [] (condition localTest.condition (numₘ(code)) (numₘ(conclusion) : Code)) := by
  apply ObjectCheckedTrace.transport rules localTest.condition
    (FirstOrder.Derives.eq_symm (node_evaluate C 1 [code, conclusion]))
  apply ObjectCheckedTrace.positive C S hPower hInfinity localTest rules rank descending
  simpa only [hTest, checked] using h

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (localTest : ObjectCheckedTrace.LocalTest T) (localCheck : Nat → Bool)
    (hTest : localTest.checked = rowCheck localCheck)
    (code conclusion : Nat) (h : checked localCheck code conclusion = false) :
    Derives T [] (¬ₘ condition localTest.condition (numₘ(code)) (numₘ(conclusion) : Code)) := by
  apply ObjectCheckedTrace.transport_negative rules localTest.condition
    (FirstOrder.Derives.eq_symm (node_evaluate C 1 [code, conclusion]))
  apply ObjectCheckedTrace.negative C A localTest rules rank descending
  simpa only [hTest, checked] using h

end YesMetaZFC.Automation.ObjectProofTree
