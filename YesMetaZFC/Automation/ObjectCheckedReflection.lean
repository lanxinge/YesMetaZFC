import YesMetaZFC.Automation.ObjectHornRanking
import YesMetaZFC.Automation.ObjectProofTree

/-! # 已检查轨迹的反射公式与原证明树秩证书 -/
namespace YesMetaZFC.Automation.ObjectCheckedReflection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectHorn ObjectHornRanking ObjectNumeralReflection ProofT QuineEncoding
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 保留原已检查轨迹；第二槽仅供公共模板传输接口使用。 -/
def template (rules : List Rule) (localCondition : FormulaTemplate.Unary) : FormulaTemplate.Binary :=
  ⟨ObjectCheckedTrace.condition rules localCondition (.fvar .here)⟩

theorem template_apply (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    {bound free : SetContext} (row other : SetTerm bound free) :
    template rules localCondition row other = ObjectCheckedTrace.condition rules localCondition row := by
  unfold template FormulaTemplate.apply_two FormulaTemplate.instantiate
  dsimp only
  simp only [ObjectCheckedTrace.condition, ObjectTrace.condition_substituteMapped, Term.substituteMapped]
  rfl

def atRow {bound free : SetContext} (graph : Delta0ProofGraph)
    (rules : List Rule) (localCondition : FormulaTemplate.Unary) (row : SetTerm bound free) : SetFormula bound free :=
  forallNumeral row ((NaturalProofPresentation.graph graph).provability
    (ObjectCodeInstantiation.formula IntrinsicQuotation.node (fun _ => .fvar .here) (template rules localCondition).body))

def premises {free : SetContext} (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    (rule : Rule) (inputs : Fin rule.arity → SetOpenTerm free) : SetOpenFormula free :=
  allOf (rule.premises.map (fun premise => ObjectCheckedTrace.condition rules localCondition (premise.term inputs)))

def atTag (graph : Delta0ProofGraph) (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    (plan : Plan) (tag : Nat) : SetOpenFormula [.set] :=
  let inputs : Fin (plan.width tag) → SetTerm (project_bound_context (plan.width tag)) [.set] :=
    fun i => .bvar (project_bound_variable i)
  let root := IntrinsicQuotation.node tag (List.ofFn inputs)
  allNatural (plan.width tag) ((inputs (plan.slot tag) ≐ₘ .fvar .here) ⟶ₘ
    (ObjectCheckedTrace.condition rules localCondition root ⟶ₘ atRow graph rules localCondition root))

def atPhase (graph : Delta0ProofGraph) (rules : List Rule) (localCondition : FormulaTemplate.Unary)
    (plan : Plan) (phase : Nat) : SetOpenFormula [.set] :=
  allOf ((plan.tags.filter fun tag => plan.phase tag == phase).map (atTag graph rules localCondition plan))

/-- 根行进入节点阶段；节点阶段沿实际子证明编码严格下降。 -/
def proofPlan : Plan where
  tags := [0, 1]
  width := fun tag => if tag = 0 then 1 else 2
  slot := fun tag => ⟨0, by split <;> decide⟩
  phase := fun tag => tag

theorem proof_valid : Valid proofPlan ObjectProofTree.rules :=
  check_sound _ _ (by decide +kernel)

end YesMetaZFC.Automation.ObjectCheckedReflection
