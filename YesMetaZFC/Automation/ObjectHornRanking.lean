import YesMetaZFC.Automation.ObjectHornReflection
import YesMetaZFC.Automation.ObjectSyntaxReflection

/-! # 有限 Horn 图的分层秩证书

同层按一个内部字段下降，跨层按固定的外部阶段下降。
证书核验原表达式的完整节点形状，不修改规则或轨迹正文。
-/
namespace YesMetaZFC.Automation.ObjectHornRanking
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectHorn ProofT QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

deriving instance DecidableEq for ObjectHorn.Expr

structure Plan where
  tags : List Nat
  width : Nat → Nat
  slot : (tag : Nat) → Fin (width tag)
  phase : Nat → Nat

def fields {n : Nat} : Expr n → List (Expr n)
  | .succ (.pair (.literal 1) (.pair head tail)) => head :: fields tail
  | _ => []

def frame {n : Nat} : Expr n → Nat × List (Expr n)
  | .succ (.pair (.literal tag) payload) => (tag, fields payload)
  | _ => (0, [])

def WellFormed (plan : Plan) {n : Nat} (expr : Expr n) : Prop :=
  (frame expr).1 ∈ plan.tags ∧ (frame expr).2.length = plan.width (frame expr).1 ∧
    expr = .node (.literal (frame expr).1) (frame expr).2

instance (plan : Plan) {n : Nat} (expr : Expr n) : Decidable (WellFormed plan expr) := by
  unfold WellFormed; infer_instance

def rankExpr (plan : Plan) {n : Nat} (expr : Expr n) : Expr n :=
  (frame expr).2[(plan.slot (frame expr).1).val]?.getD (.literal 0)

def below {n : Nat} : Expr n → Expr n → Bool
  | .var index, .succ body => decide (index ∈ body.variables)
  | _, _ => false

theorem below_sound {n : Nat} {child parent : Expr n} (h : below child parent = true) :
    ObjectSyntaxReflection.Below child parent := by
  cases child <;> cases parent <;> simp only [below, Bool.false_eq_true] at h
  rename_i index body
  exact ⟨index, body, rfl, rfl, of_decide_eq_true h⟩

def Earlier (plan : Plan) {n : Nat} (child parent : Expr n) : Prop :=
  plan.phase (frame child).1 < plan.phase (frame parent).1 ∨
    plan.phase (frame child).1 = plan.phase (frame parent).1 ∧
      below (rankExpr plan child) (rankExpr plan parent) = true

instance (plan : Plan) {n : Nat} (child parent : Expr n) : Decidable (Earlier plan child parent) := by
  unfold Earlier; infer_instance

def Valid (plan : Plan) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, WellFormed plan rule.head ∧
    ∀ premise ∈ rule.premises, WellFormed plan premise ∧ Earlier plan premise rule.head

def Shapes (plan : Plan) (rules : List Rule) : Prop :=
  ∀ rule ∈ rules, WellFormed plan rule.head ∧ ∀ premise ∈ rule.premises, WellFormed plan premise

def checkShapes (plan : Plan) (rules : List Rule) : Bool :=
  rules.all fun rule => decide (WellFormed plan rule.head) &&
    rule.premises.all fun premise => decide (WellFormed plan premise)

theorem checkShapes_sound (plan : Plan) (rules : List Rule) (h : checkShapes plan rules = true) : Shapes plan rules := by
  simpa only [checkShapes, Shapes, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using h

def check (plan : Plan) (rules : List Rule) : Bool :=
  rules.all fun rule => decide (WellFormed plan rule.head) &&
    rule.premises.all fun premise => decide (WellFormed plan premise ∧ Earlier plan premise rule.head)

theorem check_sound (plan : Plan) (rules : List Rule) (h : check plan rules = true) : Valid plan rules := by
  simpa only [check, Valid, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using h

/-- 固定数量的自然数参数全称量化，由原有存在见证块对偶得到。 -/
def allNatural {free : SetContext} (count : Nat) (body : SetFormula (project_bound_context count) free) : SetOpenFormula free :=
  .neg (quantify count ωₘ (.neg body))

def atTag (graph : Delta0ProofGraph) (rules : List Rule) (plan : Plan) (tag : Nat) : SetOpenFormula [.set] :=
  let inputs : Fin (plan.width tag) → SetTerm (project_bound_context (plan.width tag)) [.set] :=
    fun i => .bvar (project_bound_variable i)
  let root := IntrinsicQuotation.node tag (List.ofFn inputs)
  allNatural (plan.width tag) ((inputs (plan.slot tag) ≐ₘ .fvar .here) ⟶ₘ
    (ObjectHorn.condition rules root ⟶ₘ ObjectHornReflection.atRow graph rules root))

def atPhase (graph : Delta0ProofGraph) (rules : List Rule) (plan : Plan) (phase : Nat) : SetOpenFormula [.set] :=
  allOf ((plan.tags.filter fun tag => plan.phase tag == phase).map (atTag graph rules plan))

end YesMetaZFC.Automation.ObjectHornRanking
